import Oak
import Lean

/-! A build is not an axiom audit. Preserve the obligation definitions and check
actual proof authority, including imports. Native-evaluation assumptions elsewhere
in Oak are a separate trust boundary; the five session proofs below use none. -/
open Lean Elab Command

example : Oak.Session.loop_loop_1_terminates := Oak.Session.loop_loop_1_terminates_proved
example : Oak.Session.loop_countdown_2_terminates := Oak.Session.loop_countdown_2_terminates_proved
example : ¬ Oak.Session.loop_fill_3_terminates := Oak.Session.loop_fill_3_terminates_refuted
example : ¬ Oak.Session.loop_walk_4_terminates := Oak.Session.loop_walk_4_terminates_refuted
example : ¬ Oak.Session.loop_drive_5_terminates := Oak.Session.loop_drive_5_terminates_refuted

run_cmd do
  let env ← getEnv
  for name in [``Oak.Session.loop_loop_1_terminates, ``Oak.Session.loop_countdown_2_terminates,
      ``Oak.Session.loop_fill_3_terminates, ``Oak.Session.loop_walk_4_terminates,
      ``Oak.Session.loop_drive_5_terminates] do
    match env.find? name with
    | some (.defnInfo _) => pure ()
    | _ => throwError "{name} must remain a named proposition definition, not an admitted theorem"
  for name in [``Oak.Session.loop_loop_1_terminates_proved,
      ``Oak.Session.loop_countdown_2_terminates_proved,
      ``Oak.Session.loop_fill_3_terminates_refuted,
      ``Oak.Session.loop_walk_4_terminates_refuted,
      ``Oak.Session.loop_drive_5_terminates_refuted] do
    let axioms ← collectAxioms name
    for axiomName in axioms do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
        throwError "{name} depends on nonstandard axiom {axiomName}"
  -- The generated fixture must not leave proof authority in the aggregate.
  for (name, _) in env.constants.toList do
    if name.toString.startsWith "Oak." || name.toString.startsWith "_private.Oak." then
      let axioms ← collectAxioms name
      if axioms.contains ``sorryAx then
        throwError "aggregate declaration {name} depends on sorryAx"
