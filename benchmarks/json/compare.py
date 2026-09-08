#!/usr/bin/env python3
"""Report paired native measurements without treating CI noise as a proof."""
import argparse
import json
from pathlib import Path


def compare(baseline, candidate):
    before, after = baseline["metadata"], candidate["metadata"]
    for key in ("schema", "workload", "corpus", "mode", "machine", "cpu", "cc", "cxx", "flags", "documents_per_round", "rounds", "samples", "simdjson_implementation"):
        if before[key] != after[key]:
            raise ValueError("incomparable metadata: " + key)
    if before["simdjson"]["sha"] != after["simdjson"]["sha"]:
        raise ValueError("simdjson revisions differ")
    if before["mode"] == "sanitizer correctness":
        raise ValueError("sanitizer runs are not performance measurements")
    old = baseline["summary"]["oak"]["median_ns_per_document"]
    new = candidate["summary"]["oak"]["median_ns_per_document"]
    simd_old = baseline["summary"]["simdjson_ondemand"]["median_ns_per_document"]
    simd_new = candidate["summary"]["simdjson_ondemand"]["median_ns_per_document"]
    return {
        "machine": after["machine"], "cpu": after["cpu"],
        "baseline_sha": before["oak"]["sha"], "candidate_sha": after["oak"]["sha"],
        "baseline_ns_per_document": old, "candidate_ns_per_document": new,
        "oak_speedup": old / new, "simdjson_ns_per_document": simd_new,
        "oak_over_simdjson_time": new / simd_new,
        "simdjson_time_drift": simd_new / simd_old,
        "limitation": "One hosted runner, one schema, resident corpus. No affinity/frequency control; no statistical or universal parity claim.",
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("baseline", type=Path)
    parser.add_argument("candidate", type=Path)
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()
    result = compare(json.loads(args.baseline.read_text()), json.loads(args.candidate.read_text()))
    text = json.dumps(result, indent=2) + "\n"
    args.output.write_text(text)
    print(text, end="")


if __name__ == "__main__":
    main()
