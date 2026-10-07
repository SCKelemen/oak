# Temporal values and ISO text

Status: implemented profile with initial implementation laws; not yet a fully
proved v1.0 library. Import `time`. The pure source fragment
`stdlib/time_calendar.oak` is composed with the existing `time.oak` implementation.
No allocation, host clock, locale, time zone database, or floating-point parsing
is involved in this profile. Existing time APIs retain their behavior.

## 1. Value model

| Type | Meaning and representation |
| --- | --- |
| `Duration` | Signed exact nanoseconds in `i64`; existing API. |
| `Instant` | Signed Unix-epoch nanoseconds in `i64`; existing approximately 1677–2262 range, without leap-second representation. |
| `Date` | Proleptic Gregorian calendar date; years 0000–9999 inclusive. |
| `Time` | Civil clock reading, 00:00:00 through 23:59:59.999999999. |
| `DateTime` | A `Date` and `Time`, without an offset or time zone. |
| `Period` | Signed `i32` calendar months, signed `i32` calendar days, and an exact `Duration` time component. |
| `OffsetDateTime` | A `DateTime`, minutes east of UTC in −1439…1439, and `OffsetKind`. This does not name a time zone. |
| `WeekDate` | ISO week year 0000–9999, week 1–52/53, weekday 1 (Monday)–7 (Sunday). |

Records are public values, not opaque refinement types. `date_create`,
`time_of_day`, and `datetime_create` are checked constructors. Operations and
formatters validate their inputs, including directly constructed records.
`date_valid`, `time_valid`, `datetime_valid`, and `offset_datetime_valid` expose
the corresponding predicates. `datetime_civil` is a structural projection;
`datetime_from_civil` validates the new, narrower civil-year domain.

`OffsetKind` preserves `UtcDesignator` (`Z`/`z`), `Numeric` (including `+00:00`),
and `UnknownLocal` (`-00:00`). The first and last require offset minutes zero.
Following RFC 3339 as updated by RFC 9557 section 2, `Z` and `-00:00` identify
known UTC time without asserting a preferred local offset; `+00:00` preserves
that assertion. Case and insignificant fractional zeros are not retained.
`offset_datetime_to_instant` accepts either zero-offset convention. An unknown
local offset is not an unknown instant. Conversion can return `Overflowed` even
when the civil text is valid, because `Instant` has a narrower range.

## 2. Arithmetic

`date_epoch_days` and `date_from_epoch_days` use 1970-01-01 as zero; the admitted
range is −719528 through 2932896 inclusive. `date_add_days` checks the output
range before addition, including for `i64` extrema.

`date_add_months(date, months, policy)` changes the year/month as a single
calendar operation. `MonthEnd.Reject` returns `InvalidCivil` if the original day
does not exist in the destination month. `MonthEnd.Clamp` uses its last day.
For example, January 31 plus one month in 2024 rejects or becomes February 29.
Neither policy carries excess days into March. Clamping is not invertible and
repeated month additions need not equal a single combined addition.

`date_add_period` applies months, then days. A nonzero time component is
`InvalidDuration`; it is never silently discarded. `datetime_add_period`
applies months, then days, then the time component. Components may have different
signs for arithmetic, but a mixed-sign period cannot use the text profile below.

`datetime_add_duration` advances on nominal 86400-second civil days, with exact
nanosecond carry in either direction. It splits an `i64` duration into days and
remainder before adding, so an intermediate nanosecond sum cannot overflow.
This is arithmetic on an unzoned civil value, not DST or leap-second arithmetic.
`P1D` and `PT24H` are distinct periods even when they produce the same result on
this nominal calendar. No implicit period-to-duration conversion is supplied.

`date_from_ordinal`, `date_from_week`, and `date_to_week` implement ordinal and
ISO week conversion. Week 1 contains January 4. Week 53 is admitted only when it
exists. A valid calendar date whose week-year is outside 0000–9999 returns
`Overflowed` from `date_to_week` (notably the first days of year 0000).

## 3. Admitted interchange profile

This is a declared subset, not a claim of complete ISO 8601 conformance.

| Function | Accepted input / canonical output |
| --- | --- |
| `parse_iso_date` | `YYYY-MM-DD`, `YYYYMMDD`, `YYYY-DDD`, `YYYYDDD`, `YYYY-Www-D`, `YYYYWwwD`; complete dates only. |
| `format_iso_date` | `YYYY-MM-DD`. |
| `parse_iso_time` | `HH:MM:SS` with optional `.` or `,` and 1–9 fractional second digits. |
| `format_iso_time` | `HH:MM:SS`, optional dot and fractional digits, trailing zeros removed. |
| `parse_iso_datetime` | Extended calendar date, uppercase `T`, extended time; no offset. |
| `format_iso_datetime` | Canonical extended calendar date/time. |
| `parse_rfc3339_datetime` | `YYYY-MM-DD(T\|t)HH:MM:SS[.fraction](Z\|z\|±HH:MM)`; 1–9 fractional digits. |
| `format_rfc3339_datetime` | Uppercase `T`/`Z`, trimmed exact fraction, original offset kind. |
| `parse_iso_period` | Date/time designators or week-only designator, described below. |
| `format_iso_period` | Total months, calendar days, then hours/minutes/seconds; zero is `PT0S`. |
| `parse_iso_duration` | Only `PT` hour/minute/second components; even `P0D` is rejected. |
| `format_iso_duration` | Signed `PT` hours/minutes/seconds; hours are not converted to calendar days. |

Designator grammar (ASCII, case-sensitive):

```text
period = [sign] "P" (weeks / components)
weeks = digits "W"
components = [digits "Y"] [digits "M"] [digits "D"]
             ["T" [digits "H"] [digits "M"] [seconds "S"]]
seconds = digits [("." / ",") 1*9DIGIT]
sign = "+" / "-"
```

At least one component is required, and `T` requires a time component. Units
must occur once in order. Weeks cannot mix with other units. Fractions are
seconds-only; leading integer digits are required. A leading sign is an explicit
Oak extension to the unsigned base profile, applied to all components. Embedded
signs and whitespace are invalid. Years become 12 months and weeks become 7
calendar days; days are not converted into nanoseconds. Components are checked
against the final signed field limits while accumulating, with `i64` and `i32`
negative minima supported. Fractions use integer arithmetic, never rounding.

Examples:

- `P1Y2M3DT4H5M6.000000007S` becomes 14 months, 3 days, 14706000000007 ns.
- `P2W` formats as `P14D`.
- `PT24H` stays `PT24H`; `P1D` stays `P1D`.
- `-PT9223372036.854775808S` represents `i64.min` exactly.
- `2024-02-29t12:34:56.1200-00:00` formats as
  `2024-02-29T12:34:56.12-00:00`.

All input must be consumed. RFC 3339 accepts neither comma fractions nor a space
separator in this profile. Leap seconds, end-of-day `24:00`, fractions beyond
nanoseconds, expanded years, reduced precision, basic clock forms, interval and
recurrence expressions, and RFC 9557 bracket annotations are outside this
profile. In particular, RFC 3339 itself admits longer fractions and contextual
leap seconds; the library does not claim full acceptance of its grammar.

The original `parse_rfc3339`/`format_rfc3339` still use `Zoned` and `Instant`,
normalize zero-offset metadata, and honor the existing explicit fraction-width
formatting API. The new civil API is the metadata-preserving alternative.
The original `parse_duration`/`format_duration` retain Go-style text.

## 4. Errors, storage, and cost

Existing `TimeError` variants are reused; no exhaustive match is broken.

- `InvalidFormat`: date/time text shape, separators, or fractional precision.
- `InvalidCivil`: impossible date/time, out-of-domain civil fields, missing week
  53, or month-end rejection.
- `InvalidOffset`: malformed numeric RFC offset, magnitude at least a day, or
  an inconsistent constructed `OffsetDateTime`.
- `InvalidDuration`: period grammar, mixed-sign serialization, a calendar unit
  in exact-duration parsing, or a nonzero time component applied to a `Date`.
- `Overflowed`: representable arithmetic result outside the chosen domain, or
  a decimal accumulator/component outside its numeric range. A malformed input
  that overflows while scanning can return this before a later grammar error.
- `DestinationTooSmall`: output capacity is less than the actual canonical text.

All new formatters validate and build in bounded local arrays before copying.
On any error, every destination byte is unchanged. On success, only the returned
prefix is written, and the suffix is unchanged. Capacity maxima are 10 bytes
for dates, 18 for times, 29 for local datetimes, 35 for RFC timestamps, and 64
for periods/durations. No alias to local storage escapes. Calendar operations
are constant work; parsing is O(input length), bounded by numeric overflow and
precision rejection where applicable; formatting is bounded work and memory.

## 5. Evidence and remaining proof obligations

`compiler/e2e_stdlib_time_iso_test.go` exercises real qualified imports through
compiled and interpreted execution. It covers grammar/rejection, canonical
formatting, zero-offset metadata, month-end behavior, signed minima/maxima,
range edges, and destination preservation. Deterministic random calendars,
ISO week numbers, and civil-duration additions are compared against Go's
independent `time` implementation. Duration text is round-tripped across the
full signed range. Existing time/clock tests remain the compatibility gate.

The Lean emitter also zero-extends unsigned fields before a wider signed
reinterpretation; this fixes missing Lean conversion methods for valid Oak
constructors such as `i64(u8)` and `i64(u32)`. The extractor regression suite
covers that conversion path.

`TimeCalendarExtracted.lean` is generated from the typechecked Oak fragment and
its callees. `TestLeanStdlibExtract/time` checks drift. The legacy
`offset_datetime_to_instant` bridge is excluded because checked-i64 intrinsics
are outside the current extractor subset; it is covered by runtime tests.
The temporal proof entry point, `TimeRFC3339RoundtripLaws.lean`, imports the
calendar, decimal, fractional-clock, offset, and buffer layers:

- Constructor acceptance/rejection, civil structural roundtrip, invalid-input
  rejection, and formatter error atomicity are kernel-checked over the extraction.
- `TimeGregorianLaws.lean` checks every one of the 3,652,425 supported epoch
  days and all 3,720,000 year/month/day slots (years 0–9999, months 1–12,
  days 1–31). The validity predicate filters impossible dates. The resulting
  theorems establish both conversion directions, valid output dates, and the
  supported epoch-day range, for arbitrary fuel. These two finite certificates
  use **`native_decide`**, which trusts Lean's native evaluator and adds
  native decision axioms; they are not kernel-only arithmetic proofs. The arguments
  lifting the finite certificates to arbitrary supported inputs also use
  bit-vector certificates for the validity predicate's field bounds.
- `TimeCalendarArithmeticLaws.lean` proves the day-addition guard equivalent to
  an unbounded integer range check, and proves accepted sums cannot wrap. It also
  states successful addition and zero-day identity using the Gregorian facts.
  Reject-policy day preservation is kernel checked. Month-index bounds,
  validity-field bounds, and bounded day-range lemmas use `bv_decide`; its verified
  LRAT checker runs through native evaluation in the pinned Lean toolchain and adds native decision axioms.
  Clamp validity/minimum-day selection and exact Reject behavior use these
  bounds. Day-addition success also inherits the Gregorian certificates' native
  evaluation trust. An axiom audit distinguishes these dependencies from the
  kernel-only integer guard and non-wrapping sum laws.
- `TimeDecimalLaws.lean` reconstructs two- and four-digit fields and relates
  the actual date writer and reader to a ten-byte canonical calendar spelling.
  Its bounded arithmetic uses `bv_decide` and therefore the pinned native LRAT
  checker, with native decision axioms.
- `TimeCodecLaws.lean` proves that every valid date formats canonically and
  parses back to itself through any ten-byte destination; eleven units of
  extraction fuel suffice. It also proves that successful date, clock, and
  local-datetime parses return valid civil values. The clock-validity argument
  is kernel checked; date/local-datetime validity inherits the Gregorian native
  certificates through ordinal/week parsing. These are valid-result contracts,
  not proofs of grammar soundness or completeness.
- `TimeFractionLaws.lean` and `TimeFractionTrimLaws.lean` prove decimal
  reconstruction and trailing-zero trimming for every valid nanosecond value.
  These arithmetic arguments are kernel checked. `TimeCopyLaws.lean` proves
  exact prefix copying and sufficient-fuel completion.
- `TimeRoundtripLaws.lean`, `TimeTimestampLaws.lean`, and
  `TimeRFC3339RoundtripLaws.lean` prove universal canonical round trips for
  valid clocks, local datetimes, and RFC3339 offset datetimes. Destinations
  must have at least 18, 29, or 35 bytes respectively, and fewer than 2^32 bytes
  so the extracted UInt32 length is exact. Forty units of extraction fuel
  suffice. Successful lengths are respectively 8–18, 19–29, and 20–35 bytes;
  the entire unused suffix and destination size are preserved. RFC3339 returns
  the original offset kind, keeping `Z`, `+00:00`, and `-00:00` distinct.
  These composition proofs inherit the decimal/calendar native trust noted
  above; clock field bounds and numeric offset reconstruction also use
  `bv_decide` with the pinned native LRAT checker.
- `TimeBufferLaws.lean` proves error atomicity and success frame properties for
  **all six new formatters**, for arbitrary destinations and extraction fuel.
  Every returned `Err` preserves the entire destination. Every returned `Ok n`
  preserves its size and all bytes at indices at least `n`. These are kernel-only
  control-flow and array proofs; they do not establish prefix contents, output
  length bounds, or termination with sufficient fuel for every formatter.

`TestLeanTimeCalendarFaithful` builds one deterministic corpus of 1,468 cases
and compares every returned field and error constructor with an independent Go
calendar oracle in compiled Oak, interpreted Oak, and extracted Lean. It covers
both conversion directions, day addition, both month-end policies, year zero,
century exceptions, invalid/high-bit fields, domain edges, and signed integer
extrema. The day-addition oracle uses unbounded integers to avoid reproducing
an overflow bug. This corpus checks executable correspondence on these inputs;
it is not a proof of extraction or compiler correctness.

`TestLeanTimeCodecFaithful` runs **1,782 shared checks** across the same three
execution paths. It compares every parsed field, exact error constructors,
canonical text, returned lengths, and entire destination arrays. Go supplies
independent civil/calendar spellings; a separate unsigned-magnitude oracle
supplies period/duration spellings, including signed minima. Explicit cases
cover the declared profile's restrictions instead of assuming Go accepts the
same grammar. Coverage includes basic/ordinal/week dates, every supported
fractional width, leading zeros down to one nanosecond, comma ISO fractions,
every trailing-zero trim boundary, all three RFC
zero-offset kinds, malformed/non-ASCII/NUL input, signed limits, and every
capacity from zero through two bytes beyond each documented maximum. The
capacity sweep uses maximum-width values; other cases exercise shorter text
and suffix preservation. This is finite executable evidence, not a universal
codec or extraction proof.

The focused Temporal library proofs workflow and the main formal workflow
require these laws and both shared corpora. `OAK_REQUIRE_TIME_LEAN=1` makes a
missing Lean toolchain a failure in CI. Fuel, array totalization, and machine
integer modeling retain the qualifications in `95-extraction.md`.

Open release gates, explicitly not implied by successful tests or extraction:

1. Replace the exhaustive Gregorian certificates with kernel-only arithmetic
   proofs if the native-evaluator trust boundary is unacceptable. Prove
   ordinal/week conversion, the remaining calendar success laws, and duration
   carry arithmetic.
2. Prove parser grammar soundness/completeness and checked-component overflow
   equivalence. Extend canonical round-trip proofs to periods and durations. Establish
   successful prefix contents, output bounds, and sufficient-fuel termination
   for those remaining formatters, and date round trips through larger
   destinations. Extend
   shared executable correspondence to civil-duration arithmetic.
3. Extend extraction/refinement through checked instant conversion. Preserve
   proofs through compilation, ABI, instruction encoding, and linking on both
   mandatory ARM64 and RV64 targets.
4. Design explicit leap-second/time-scale and named-zone rule capabilities
   before accepting contextual leap seconds or zoned calendar arithmetic.
5. Expand ISO support through individually specified reduced/basic/end-of-day,
   interval/recurrence, expanded-year, and precision profiles as needed.

## References

- [RFC 3339, sections 4.3 and 5.6–5.7](https://www.rfc-editor.org/rfc/rfc3339.html)
- [RFC 9557, section 2](https://www.rfc-editor.org/rfc/rfc9557.html#section-2)
- [ISO 8601-1:2019](https://www.iso.org/standard/70907.html) and
  [Amendment 1:2022](https://www.iso.org/standard/81801.html)
- [Gregorian conversion algorithms](https://howardhinnant.github.io/date_algorithms.html),
  already used by Oak's original civil-time implementation.
