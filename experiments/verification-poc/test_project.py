"""Behavioral tests for the supported fragment and result boundary."""
import itertools
import json
from pathlib import Path
import re
import tempfile
import unittest
from unittest.mock import patch

from project import Model, ModelError, emit, evaluate, external_check, finite_check, load_project

ROOT = Path(__file__).parent


def smt_query(text, values):
    """Independent interpreter for the actual generated SMT assertion."""
    tokens = iter(re.findall(r"\(|\)|[^\s()]+", re.sub(r";[^\n]*", "", text)))

    def parse(token):
        if token != "(":
            return token
        result = []
        for token in tokens:
            if token == ")":
                return result
            result.append(parse(token))
        raise AssertionError("unbalanced SMT")

    def calc(tree):
        if isinstance(tree, str):
            return {"true": True, "false": False, **values}[tree]
        op, *args = tree
        args = [calc(x) for x in args]
        if op == "not":
            return not args[0]
        if op == "and":
            return all(args)
        if op == "or":
            return any(args)
        if op == "=":
            return args[0] == args[1]
        if op == "distinct":
            return args[0] != args[1]
        raise AssertionError(op)

    forms = [parse(token) for token in tokens]
    assertions = [form[1] for form in forms if form[0] == "assert"]
    assert len(assertions) == 1
    return calc(assertions[0])


class PrototypeTests(unittest.TestCase):
    def load(self, name="borrow"):
        return load_project(ROOT / "examples" / f"{name}.json")

    def test_safe_model_and_exact_transition_relation(self):
        model, terms, _ = self.load()
        report = finite_check(model, terms)
        self.assertEqual(report["reachable_states"], 3)
        self.assertTrue(report["inductive"])
        self.assertEqual(report["status"], "passed")
        expected = {((False, False), (True, False)), ((True, False), (True, False)),
                    ((True, False), (False, False)), ((False, False), (False, True)),
                    ((False, True), (False, False))}
        actual = set()
        for source, target in itertools.product(itertools.product((False, True), repeat=2), repeat=2):
            if evaluate(terms["step"], {"s": dict(zip(model.fields, source)), "t": dict(zip(model.fields, target))}):
                actual.add((source, target))
        self.assertEqual(actual, expected)

    def test_broken_model_has_replayable_shortest_trace(self):
        model, terms, _ = self.load("broken")
        result = finite_check(model, terms)
        self.assertEqual(result["status"], "counterexample")
        trace = result["trace"]
        self.assertEqual(len(trace), 3)
        self.assertTrue(evaluate(terms["initial"], {"s": trace[0]}))
        for source, target in zip(trace, trace[1:]):
            self.assertTrue(evaluate(terms["step"], {"s": source, "t": target}))
        self.assertFalse(evaluate(terms["invariant"], {"s": trace[-1]}))

    def test_generated_smt_exhaustively_matches_source_obligations(self):
        for name in ("borrow", "broken"):
            model, terms, digest = self.load(name)
            with tempfile.TemporaryDirectory() as folder:
                out = Path(folder)
                emit(model, terms, digest, out)
                files = {query: (out / f"{query}.smt2").read_text() for query in ("initial", "base", "step")}
                counts = dict.fromkeys(files, 0)
                for bits in itertools.product((False, True), repeat=4):
                    source = dict(zip(model.fields, bits[:2]))
                    target = dict(zip(model.fields, bits[2:]))
                    values = {f"{p}_f_{f}": state[f] for p, state in (("s", source), ("t", target)) for f in model.fields}
                    ini = evaluate(terms["initial"], {"s": source})
                    inv = evaluate(terms["invariant"], {"s": source})
                    step = evaluate(terms["step"], {"s": source, "t": target})
                    inv_t = evaluate(terms["invariant"], {"s": target})
                    expected = {"initial": ini, "base": ini and not inv, "step": inv and step and not inv_t}
                    for query, text in files.items():
                        actual = smt_query(text, values)
                        self.assertEqual(actual, expected[query])
                        counts[query] += actual
                self.assertGreater(counts["initial"], 0)
                self.assertEqual(counts["base"], 0)
                self.assertEqual(counts["step"] > 0, name == "broken")

    def test_fail_closed_on_unsupported_or_ill_typed_source(self):
        source = (ROOT / "examples/borrow.oak").read_text()
        mutations = [source.replace("reader: Bool", "reader: u8"),
                     source.replace("!s.reader && !s.writer", "s && !s.writer", 1),
                     source.replace("!s.reader", "!s.missing", 1),
                     source.replace("acquire_read(s, t)", "missing(s, t)"),
                     source.replace("acquire_read(s, t)", "acquire_read(s)"),
                     source.replace("acquire_read(s, t)", "step(s, t)"),
                     source + "\nunsafe {}", source + "\n???"]
        for mutation in mutations:
            with self.subTest(source=mutation), self.assertRaises(ModelError):
                Model(mutation)

    def test_forward_calls_and_boolean_precedence(self):
        model = Model("S: type = {x: Bool}\np: (s: S) -> Bool = q(s)\nq: (s: S) -> Bool = true || false && !s.x")
        self.assertTrue(evaluate(model.expand("p", ["s"]), {"s": {"x": True}}))

    def test_reachability_is_distinct_from_inductiveness(self):
        model, _, _ = self.load()
        source = """S: type = {x: Bool, y: Bool}
initial: (s: S) -> Bool = !s.x && !s.y
safe: (s: S) -> Bool = !s.y
step: (s: S, t: S) -> Bool = s.x && !s.y && t.y
"""
        model = Model(source)
        terms = {"initial": model.expand("initial", ["s"]), "invariant": model.expand("safe", ["s"]), "step": model.expand("step", ["s", "t"])}
        result = finite_check(model, terms)
        self.assertEqual(result["status"], "passed")
        self.assertFalse(result["inductive"])
        self.assertEqual(result["reachable_states"], 1)
        self.assertEqual(len(result["deadlocks"]), 1)

    def test_empty_initial_set_is_not_success(self):
        model, terms, _ = self.load()
        terms["initial"] = ("bool", False)
        self.assertEqual(finite_check(model, terms)["status"], "error")

    def test_emit_invalidates_previous_report_and_is_deterministic(self):
        model, terms, digest = self.load()
        with tempfile.TemporaryDirectory() as folder:
            out = Path(folder)
            emit(model, terms, digest, out)
            before = {p.name: p.read_bytes() for p in out.iterdir()}
            (out / "report.json").write_text('{"status":"passed"}')
            emit(model, terms, digest, out)
            self.assertFalse((out / "report.json").exists())
            self.assertEqual(before, {p.name: p.read_bytes() for p in out.iterdir()})

    def test_missing_tools_and_unknown_are_not_success(self):
        with patch("project.shutil.which", return_value=None):
            self.assertEqual(external_check("lean", ROOT, 1)["status"], "unavailable")
        with patch("project.shutil.which", return_value="z3"), patch("project.run", return_value={"exit_code": 0, "stdout": "unknown\n", "stderr": ""}):
            self.assertEqual(external_check("z3", ROOT, 1)["status"], "unknown")

    def test_project_roles_are_checked(self):
        with tempfile.TemporaryDirectory() as folder:
            root = Path(folder)
            (root / "model.oak").write_text((ROOT / "examples/borrow.oak").read_text())
            (root / "project.json").write_text(json.dumps({"source": "model.oak", "initial": "step", "step": "step", "invariant": "safe"}))
            with self.assertRaises(ModelError):
                load_project(root / "project.json")


if __name__ == "__main__":
    unittest.main()
