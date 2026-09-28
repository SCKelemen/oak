//! Coverage cross-checks use the SAME transition relation, not an independent
//! architectural model. Full Eq state storage avoids fingerprint-only merging.
use crate::{Action, Policy, Remap, State, OBSERVERS, REACHABILITY, SAFETY, STATE_UPPER_BOUND};
use serde::Serialize;
use stateright::{Checker, HasDiscoveries, Model, StateRecorder};
use std::collections::{BTreeSet, HashSet, VecDeque};

#[derive(Debug)]
struct Exact {
    states: HashSet<State>,
    transitions: usize,
    max_action_distance: usize,
    violations: [usize; 3],
    reached: [bool; 3],
}

fn enumerate(model: Remap) -> Exact {
    let initial = model.init_states();
    let mut result = Exact {
        states: initial.iter().copied().collect(),
        transitions: 0,
        max_action_distance: 0,
        violations: [0; 3],
        reached: [false; 3],
    };
    let mut pending: VecDeque<_> = initial.into_iter().map(|s| (s, 0)).collect();
    while let Some((state, distance)) = pending.pop_front() {
        result.max_action_distance = result.max_action_distance.max(distance);
        for (i, holds) in state.safety().into_iter().enumerate() {
            result.violations[i] += usize::from(!holds);
        }
        for (i, holds) in state.reachability().into_iter().enumerate() {
            result.reached[i] |= holds;
        }
        let mut actions = Vec::new();
        model.actions(&state, &mut actions);
        for action in actions {
            if let Some(next) = model.next_state(&state, action) {
                result.transitions += 1;
                if result.states.insert(next) {
                    pending.push_back((next, distance + 1));
                }
            }
        }
    }
    result
}

fn verify_coverage(
    expected: &HashSet<State>,
    observed: &[State],
    unique: usize,
) -> Result<(), String> {
    let actual: HashSet<_> = observed.iter().copied().collect();
    if actual != *expected || observed.len() != actual.len() || unique != actual.len() {
        return Err(format!(
            "coverage mismatch: expected {}, visited {}, distinct {}, reported {unique}",
            expected.len(),
            observed.len(),
            actual.len()
        ));
    }
    Ok(())
}

#[derive(Debug, Serialize)]
pub struct Witness {
    pub property: &'static str,
    pub kind: &'static str,
    pub initial: State,
    pub actions: Vec<Action>,
    pub final_state: State,
}

fn replay(model: Remap, path: &[(State, Option<Action>)]) -> Result<Witness, String> {
    let initial = path.first().ok_or("empty trace")?.0;
    if !model.init_states().contains(&initial) {
        return Err("trace starts outside initial states".into());
    }
    let mut actions = Vec::new();
    for step in path.windows(2) {
        let action = step[0].1.ok_or("missing trace action")?;
        let mut enabled = Vec::new();
        model.actions(&step[0].0, &mut enabled);
        if !enabled.contains(&action) || model.next_state(&step[0].0, action) != Some(step[1].0) {
            return Err("illegal action or incorrect resulting state".into());
        }
        actions.push(action);
    }
    let (final_state, last_action) = path.last().ok_or("empty trace")?;
    if last_action.is_some() {
        return Err("trace ends with an unexecuted action".into());
    }
    Ok(Witness {
        property: "",
        kind: "",
        initial,
        actions,
        final_state: *final_state,
    })
}

#[derive(Debug, Serialize)]
pub struct PolicyReport {
    pub policy: Policy,
    pub completed: bool,
    pub full_state_set_matches: bool,
    pub initial_states: usize,
    pub unique_states: usize,
    pub transitions: usize,
    pub exact_max_action_distance: usize,
    pub stateright_max_depth: usize,
    pub violating_states: [usize; 3],
    pub reachability: [bool; 3],
    pub witnesses: Vec<Witness>,
}

pub fn verify_policy(policy: Policy) -> Result<PolicyReport, String> {
    let model = Remap { policy };
    let exact = enumerate(model);
    if exact.states.len() > STATE_UPPER_BOUND {
        return Err("finite-state bound exceeded".into());
    }
    let (recorder, recorded) = StateRecorder::<Remap>::new_with_accessor();
    let checker = model
        .checker()
        .threads(1)
        // In pinned 0.31.0 AnyOf(empty) never matches. The sentinel also
        // prevents the BFS's separate internal discovery-based early exit.
        .finish_when(HasDiscoveries::AnyOf(BTreeSet::new()))
        .visitor(recorder)
        .spawn_bfs()
        .join();
    if !checker.is_done() {
        return Err("Stateright did not finish".into());
    }
    verify_coverage(&exact.states, &recorded(), checker.unique_state_count())?;
    if checker.state_count() != exact.transitions + model.init_states().len() {
        return Err("generated transition count mismatch".into());
    }
    if checker.discovery("enumeration_sentinel").is_some() {
        return Err("enumeration sentinel failed".into());
    }
    let mut witnesses = Vec::new();
    for (i, name) in SAFETY.into_iter().enumerate() {
        let found = checker.discovery(name);
        if found.is_some() != (exact.violations[i] > 0) {
            return Err(format!("checker disagreement on {name}"));
        }
        if let Some(path) = found {
            let mut witness = replay(model, &path.into_vec())?;
            if witness.final_state.safety()[i] {
                return Err(format!("counterexample does not refute {name}"));
            }
            witness.property = name;
            witness.kind = "counterexample";
            witnesses.push(witness);
        }
    }
    for (i, name) in REACHABILITY.into_iter().enumerate() {
        if !exact.reached[i] {
            return Err(format!("nonvacuity obligation unreachable: {name}"));
        }
        let path = checker
            .discovery(name)
            .ok_or(format!("missing witness: {name}"))?;
        let mut witness = replay(model, &path.into_vec())?;
        if !witness.final_state.reachability()[i] {
            return Err(format!("invalid reachability witness: {name}"));
        }
        witness.property = name;
        witness.kind = "example";
        witnesses.push(witness);
    }
    let failures = exact.violations.map(|n| n > 0);
    let expected = match policy {
        Policy::Safe => [false, false, false],
        Policy::SkipCompletionWait => [true, true, true],
        _ => [false, true, true],
    };
    if failures != expected {
        return Err(format!(
            "{policy:?}: safety failures {failures:?}, expected {expected:?}"
        ));
    }
    Ok(PolicyReport {
        policy,
        completed: true,
        full_state_set_matches: true,
        initial_states: model.init_states().len(),
        unique_states: exact.states.len(),
        transitions: exact.transitions,
        exact_max_action_distance: exact.max_action_distance,
        stateright_max_depth: checker.max_depth(),
        violating_states: exact.violations,
        reachability: exact.reached,
        witnesses,
    })
}

#[derive(Debug, Serialize)]
pub struct Report {
    pub schema: &'static str,
    pub evidence: &'static str,
    pub stateright: &'static str,
    pub observers: usize,
    pub address_spaces: usize,
    pub mappings: usize,
    pub remaps: usize,
    pub distinct_pages: usize,
    pub state_upper_bound_per_policy: usize,
    pub search: &'static str,
    pub safety_properties: [&'static str; 3],
    pub reachability_properties: [&'static str; 3],
    pub optimizer_permission: bool,
    pub policies: Vec<PolicyReport>,
}

pub fn verify_all() -> Result<Report, String> {
    let policies = Policy::ALL
        .into_iter()
        .map(verify_policy)
        .collect::<Result<_, _>>()?;
    Ok(Report {
        schema: "oak-stateright-remap-v1",
        evidence: "bounded protocol abstraction, not ARM weak-memory or Oak refinement proof",
        stateright: "0.31.0",
        observers: OBSERVERS,
        address_spaces: 1,
        mappings: 1,
        remaps: 1,
        distinct_pages: 2,
        state_upper_bound_per_policy: STATE_UPPER_BOUND,
        search: "single-thread BFS; no symmetry, state/depth/time limits, or property early exit; full-Eq reachable-set and transition-count cross-check; every reported trace replayed",
        safety_properties: SAFETY,
        reachability_properties: REACHABILITY,
        optimizer_permission: false,
        policies,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Descriptor, Page, Phase};

    #[test]
    fn safe_and_all_mutants_exhaust_the_same_declared_model_bounds() {
        let report = verify_all().unwrap();
        assert_eq!(report.policies.len(), 5);
        for row in report.policies {
            assert!(row.completed && row.full_state_set_matches);
            assert!(row.unique_states > 4);
            assert_eq!(row.reachability, [true; 3]);
        }
    }

    #[test]
    fn publication_drain_ack_and_completion_are_distinct_steps() {
        let model = Remap {
            policy: Policy::Safe,
        };
        let mut state = model.init_states()[0];
        state = model.next_state(&state, Action::StartAccess(0)).unwrap();
        state = model.next_state(&state, Action::Break).unwrap();
        assert!(model
            .next_state(&state, Action::IssueInvalidation)
            .is_none());
        for i in 0..OBSERVERS {
            state = model.next_state(&state, Action::PublishBreak(i)).unwrap();
        }
        state = model.next_state(&state, Action::IssueInvalidation).unwrap();
        assert!(model.next_state(&state, Action::Acknowledge(0)).is_none());
        assert!(model
            .next_state(&state, Action::ServiceInvalidation(0))
            .is_none());
        state = model.next_state(&state, Action::FinishAccess(0)).unwrap();
        for i in 0..OBSERVERS {
            state = model
                .next_state(&state, Action::ServiceInvalidation(i))
                .unwrap();
        }
        assert!(model
            .next_state(&state, Action::CompleteInvalidation)
            .is_none());
        for i in 0..OBSERVERS {
            state = model.next_state(&state, Action::Acknowledge(i)).unwrap();
        }
        state = model
            .next_state(&state, Action::CompleteInvalidation)
            .unwrap();
        state = model.next_state(&state, Action::Make).unwrap();
        state = model.next_state(&state, Action::Reclaim).unwrap();
        assert_eq!(state.safety(), [true; 3]);
    }

    #[test]
    fn reclamation_is_not_guarded_by_the_asserted_invariant() {
        let model = Remap {
            policy: Policy::Safe,
        };
        // Deliberately unreachable input: the global proof search must show
        // the preceding protocol prevents it, not filter it at Reclaim.
        let mut impossible = model.init_states()[3];
        impossible.phase = Phase::Made;
        let next = model.next_state(&impossible, Action::Reclaim).unwrap();
        assert_eq!(next.safety(), [false, false, true]);
    }

    #[test]
    fn finite_bound_and_invalid_observer_indices() {
        assert_eq!(STATE_UPPER_BOUND, 559_872);
        let model = Remap {
            policy: Policy::Safe,
        };
        let mut state = model.init_states()[0];
        state.phase = Phase::Made;
        for action in [
            Action::PublishBreak(2),
            Action::ServiceInvalidation(2),
            Action::Acknowledge(2),
            Action::PublishMake(2),
            Action::StartAccess(2),
            Action::FinishAccess(2),
            Action::AccessCached(2),
        ] {
            assert!(model.next_state(&state, action).is_none());
        }
    }

    #[test]
    fn replay_rejects_erased_reordered_and_forged_steps() {
        let model = Remap {
            policy: Policy::Safe,
        };
        let first = model.init_states()[0];
        let second = model.next_state(&first, Action::Break).unwrap();
        let third = model.next_state(&second, Action::PublishBreak(0)).unwrap();
        let good = vec![
            (first, Some(Action::Break)),
            (second, Some(Action::PublishBreak(0))),
            (third, None),
        ];
        assert!(replay(model, &good).is_ok());
        assert!(replay(model, &[]).is_err());
        assert!(replay(model, &[good[0], good[2]]).is_err());
        assert!(replay(model, &[good[1], good[0], good[2]]).is_err());
        let mut forged = good.clone();
        forged[1].0.observers[0].cached = Some(Page::New);
        assert!(replay(model, &forged).is_err());
        let mut partial = good;
        partial[2].1 = Some(Action::IssueInvalidation);
        assert!(replay(model, &partial).is_err());
    }

    #[test]
    fn coverage_rejects_missing_duplicate_and_extra_states() {
        let model = Remap {
            policy: Policy::Safe,
        };
        let states = model.init_states();
        let expected: HashSet<_> = states.iter().copied().collect();
        assert!(verify_coverage(&expected, &states, 4).is_ok());
        assert!(verify_coverage(&expected, &states[..3], 3).is_err());
        let mut duplicate = states.clone();
        duplicate.push(states[0]);
        assert!(verify_coverage(&expected, &duplicate, 4).is_err());
        let mut extra = states.clone();
        extra[0].observers[0].visible = Descriptor::New;
        assert!(verify_coverage(&expected, &extra, 4).is_err());
        assert!(verify_coverage(&expected, &states, 5).is_err());
    }
}
