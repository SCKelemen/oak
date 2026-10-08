import Oak.Stdlib.TimePeriodFractionRoundtripLaws
import Oak.Stdlib.TimeRFC3339RoundtripLaws
import Oak.Stdlib.TimePeriodArithmeticLaws
import Oak.Stdlib.TimeParserSignLaws
import Oak.Stdlib.TimeParserNumericLaws
import Oak.Stdlib.TimeUnsignedRoundtripLaws

/-! # Temporal proof entry point
Period/duration arithmetic guards, numeric scanner invariants, main-loop
accumulator bounds, successful-parse sign coherence, and the complete UInt64
 and fractional decimal writer/scanner bridges supplement the complete
date, time, local datetime, and RFC3339 codec contracts. Period/duration grammar
completeness and universal text round trips remain open.
-/
