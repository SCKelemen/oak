//! A bounded protocol abstraction, NOT ARM execution, a weak-memory model,
//! a verified Oak implementation, or an optimizer-admission certificate.
use serde::Serialize;
use stateright::{Model, Property};

pub mod validation;

pub const OBSERVERS: usize = 2;
// Six phases, two observers with 3*3*3*2*2 states, and three history bits.
// This is a mathematical bound, never a traversal cutoff.
pub const STATE_UPPER_BOUND: usize = 6 * 108 * 108 * 8;
pub const SAFETY: [&str; 3] = [
    "acknowledged_before_reclaim",
    "no_old_reference_after_reclaim",
    "no_access_to_reclaimed_page",
];
pub const REACHABILITY: [&str; 3] = [
    "old_page_accessible",
    "old_access_can_be_inflight",
    "remap_finishes_and_new_page_accessible",
];

#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Serialize)]
pub enum Policy {
    Safe,
    SkipPublicationWait,
    SkipInflightDrain,
    SkipInvalidation,
    SkipCompletionWait,
}

impl Policy {
    pub const ALL: [Self; 5] = [
        Self::Safe,
        Self::SkipPublicationWait,
        Self::SkipInflightDrain,
        Self::SkipInvalidation,
        Self::SkipCompletionWait,
    ];
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Serialize)]
pub enum Page {
    Old,
    New,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Serialize)]
pub enum Descriptor {
    Old,
    Invalid,
    New,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd, Hash, Serialize)]
pub enum Phase {
    Mapped,
    Broken,
    Issued,
    Completed,
    Made,
    Reclaimed,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Serialize)]
pub struct Observer {
    pub visible: Descriptor,
    pub cached: Option<Page>,
    // A sampled translation and its pending access; completion can refill
    // the cache. This is an abstract lifetime, NOT a hardware walk model.
    pub inflight: Option<Page>,
    pub invalidated: bool,
    pub acknowledged: bool,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Serialize)]
pub struct State {
    pub phase: Phase,
    pub observers: [Observer; OBSERVERS],
    pub old_access: bool,
    pub new_access: bool,
    pub stale_access: bool,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Serialize)]
pub enum Action {
    Break,
    PublishBreak(usize),
    IssueInvalidation,
    ServiceInvalidation(usize),
    Acknowledge(usize),
    CompleteInvalidation,
    Make,
    PublishMake(usize),
    Reclaim,
    StartAccess(usize),
    FinishAccess(usize),
    AccessCached(usize),
}

#[derive(Clone, Copy, Debug)]
pub struct Remap {
    pub policy: Policy,
}

impl State {
    fn observe_access(&mut self, page: Page) {
        match page {
            Page::Old => {
                self.old_access = true;
                self.stale_access |= self.phase == Phase::Reclaimed;
            }
            Page::New => self.new_access = true,
        }
    }

    pub fn safety(&self) -> [bool; 3] {
        [
            self.phase != Phase::Reclaimed || self.observers.iter().all(|o| o.acknowledged),
            self.phase != Phase::Reclaimed
                || self.observers.iter().all(|o| {
                    o.visible != Descriptor::Old
                        && o.cached != Some(Page::Old)
                        && o.inflight != Some(Page::Old)
                }),
            !self.stale_access,
        ]
    }

    pub fn reachability(&self) -> [bool; 3] {
        [
            self.old_access,
            self.observers.iter().any(|o| o.inflight == Some(Page::Old)),
            self.phase == Phase::Reclaimed && self.new_access,
        ]
    }
}

impl Model for Remap {
    type State = State;
    type Action = Action;

    fn init_states(&self) -> Vec<State> {
        // All four initial cache occupancies; visible descriptors start Old.
        (0..1 << OBSERVERS)
            .map(|mask| State {
                phase: Phase::Mapped,
                observers: std::array::from_fn(|i| Observer {
                    visible: Descriptor::Old,
                    cached: (mask & (1 << i) != 0).then_some(Page::Old),
                    inflight: None,
                    invalidated: false,
                    acknowledged: false,
                }),
                old_access: false,
                new_access: false,
                stale_access: false,
            })
            .collect()
    }

    fn actions(&self, _: &State, actions: &mut Vec<Action>) {
        // Stable ordering is part of reproducible counterexample replay.
        actions.extend([
            Action::Break,
            Action::IssueInvalidation,
            Action::CompleteInvalidation,
            Action::Make,
            Action::Reclaim,
        ]);
        for i in 0..OBSERVERS {
            actions.extend([
                Action::PublishBreak(i),
                Action::ServiceInvalidation(i),
                Action::Acknowledge(i),
                Action::PublishMake(i),
                Action::StartAccess(i),
                Action::FinishAccess(i),
                Action::AccessCached(i),
            ]);
        }
    }

    fn next_state(&self, state: &State, action: Action) -> Option<State> {
        let mut next = *state;
        match action {
            Action::Break if state.phase == Phase::Mapped => next.phase = Phase::Broken,
            Action::PublishBreak(i) if state.phase >= Phase::Broken => {
                let observer = next.observers.get_mut(i)?;
                if observer.visible != Descriptor::Old {
                    return None;
                }
                observer.visible = Descriptor::Invalid;
            }
            Action::IssueInvalidation
                if state.phase == Phase::Broken
                    && (self.policy == Policy::SkipPublicationWait
                        || state.observers.iter().all(|o| o.visible != Descriptor::Old)) =>
            {
                next.phase = Phase::Issued;
            }
            Action::ServiceInvalidation(i) if state.phase >= Phase::Issued => {
                let observer = next.observers.get_mut(i)?;
                if observer.invalidated
                    || (observer.inflight.is_some() && self.policy != Policy::SkipInflightDrain)
                {
                    return None;
                }
                // Explicit per-observer service, never a magic global flush.
                observer.cached = None;
                observer.invalidated = true;
            }
            Action::Acknowledge(i) if state.phase >= Phase::Issued => {
                let observer = next.observers.get_mut(i)?;
                if observer.acknowledged
                    || (!observer.invalidated && self.policy != Policy::SkipInvalidation)
                {
                    return None;
                }
                observer.acknowledged = true;
            }
            Action::CompleteInvalidation
                if state.phase == Phase::Issued
                    && (self.policy == Policy::SkipCompletionWait
                        || state.observers.iter().all(|o| o.acknowledged)) =>
            {
                next.phase = Phase::Completed;
            }
            Action::Make if state.phase == Phase::Completed => next.phase = Phase::Made,
            Action::PublishMake(i) if state.phase >= Phase::Made => {
                let observer = next.observers.get_mut(i)?;
                if observer.visible != Descriptor::Invalid {
                    return None;
                }
                observer.visible = Descriptor::New;
            }
            Action::Reclaim if state.phase == Phase::Made => next.phase = Phase::Reclaimed,
            Action::StartAccess(i) => {
                let observer = next.observers.get_mut(i)?;
                if observer.cached.is_some() || observer.inflight.is_some() {
                    return None;
                }
                observer.inflight = Some(match observer.visible {
                    Descriptor::Old => Page::Old,
                    Descriptor::New => Page::New,
                    Descriptor::Invalid => return None,
                });
            }
            Action::FinishAccess(i) => {
                let observer = next.observers.get_mut(i)?;
                let page = observer.inflight.take()?;
                observer.cached = Some(page);
                next.observe_access(page);
            }
            Action::AccessCached(i) => {
                let page = next.observers.get(i)?.cached?;
                next.observe_access(page);
            }
            _ => return None,
        }
        // Stuttering adds no reachable state or safety information here.
        (next != *state).then_some(next)
    }

    fn properties(&self) -> Vec<Property<Self>> {
        vec![
            // Stateright 0.31.0 also stops expanding states internally once
            // every property has a discovery. Keep traversal alive even for
            // mutants. This is bookkeeping, NOT a substantive safety claim.
            Property::<Self>::always("enumeration_sentinel", |_, _| true),
            Property::<Self>::always(SAFETY[0], |_, s| s.safety()[0]),
            Property::<Self>::always(SAFETY[1], |_, s| s.safety()[1]),
            Property::<Self>::always(SAFETY[2], |_, s| s.safety()[2]),
            Property::<Self>::sometimes(REACHABILITY[0], |_, s| s.reachability()[0]),
            Property::<Self>::sometimes(REACHABILITY[1], |_, s| s.reachability()[1]),
            Property::<Self>::sometimes(REACHABILITY[2], |_, s| s.reachability()[2]),
        ]
    }
}
