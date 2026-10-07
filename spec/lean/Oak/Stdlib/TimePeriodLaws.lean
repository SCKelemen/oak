import Oak.Stdlib.TimeRFC3339RoundtripLaws
import Oak.Stdlib.TimePeriodArithmeticLaws
import Oak.Stdlib.TimeParserSignLaws
import Oak.Stdlib.TimeParserNumericLaws

/-! # Temporal proof entry point
Period/duration arithmetic guards, numeric scanner invariants, main-loop
accumulator bounds, and successful-parse sign coherence supplement the complete
date, time, local datetime, and RFC3339 codec contracts. Period/duration grammar
completeness and universal text round trips remain open.
-/
