#!/usr/bin/env python3
"""Disposable Oak Boolean-model projection experiment. Python standard library only."""
import argparse
from collections import deque
from dataclasses import dataclass
import hashlib
import itertools
import json
from pathlib import Path
import re
import shutil
import subprocess
import sys

VERSION = "0.1.0"


class ModelError(ValueError):
    pass


@dataclass
class Function:
    params: list
    body: tuple


class Model:
    """Small explicit subset parser, not Oak's compiler or a replacement for it."""
    def __init__(self, source):
        self.tokens = []
        token = re.compile(r"\s+|//[^\n]*|->|&&|\|\||==|!=|[A-Za-z_][A-Za-z_0-9]*|[{}():=,.!]")
        pos = 0
        while pos < len(source):
            match = token.match(source, pos)
            if not match:
                raise ModelError(f"unsupported token at line {source.count(chr(10), 0, pos) + 1}: {source[pos:pos+16]!r}")
            value = match.group()
            if not value.isspace() and not value.startswith("//"):
                self.tokens.append(value)
            pos = match.end()
        self.tokens.append("<end>")
        self.i = 0
        self.state = self.identifier()
        self.take(":")
        self.take("type")
        self.take("=")
        self.take("{")
        self.fields = []
        while self.peek() != "}":
            field = self.identifier()
            if field in self.fields:
                raise ModelError(f"duplicate field {field}")
            self.fields.append(field)
            self.take(":")
            self.take("Bool")
            if self.peek() == ",":
                self.take(",")
        self.take("}")
        if not 1 <= len(self.fields) <= 6:
            raise ModelError("prototype requires 1..6 Boolean state fields")
        self.functions = {}
        while self.peek() != "<end>":
            name = self.identifier()
            if name == self.state or name in self.functions:
                raise ModelError(f"duplicate declaration {name}")
            self.take(":")
            self.take("(")
            params = []
            while self.peek() != ")":
                param = self.identifier()
                if param in params:
                    raise ModelError(f"duplicate parameter {param}")
                params.append(param)
                self.take(":")
                self.take(self.state)
                if self.peek() != ",":
                    break
                self.take(",")
            self.take(")")
            if self.peek() not in ("->", ":"):
                raise ModelError("expected return type separator")
            self.take()
            self.take("Bool")
            self.take("=")
            self.functions[name] = Function(params, self.expression())
        # Resolve forward references, reject recursion, and check every body.
        done = set()

        def visit(name, active):
            if name in active:
                raise ModelError(f"recursive definition {name} is unsupported")
            if name in done:
                return
            fn = self.functions[name]
            if self.type_of(fn.body, set(fn.params), lambda callee: visit(callee, active | {name})) != "Bool":
                raise ModelError(f"{name} must return Bool")
            done.add(name)

        for name in self.functions:
            visit(name, set())

    def peek(self):
        return self.tokens[self.i]

    def take(self, expected=None):
        value = self.peek()
        if value == "<end>" or (expected is not None and value != expected):
            raise ModelError(f"expected {expected or 'token'}, found {value!r}")
        self.i += 1
        return value

    def identifier(self):
        value = self.take()
        if not re.fullmatch(r"[A-Za-z_][A-Za-z_0-9]*", value) or value in {"true", "false", "type", "Bool"}:
            raise ModelError(f"expected identifier, found {value!r}")
        return value

    def expression(self, minimum=0):
        if self.peek() == "!":
            self.take()
            left = ("!", self.expression(4))
        elif self.peek() == "(":
            self.take()
            left = self.expression()
            self.take(")")
        elif self.peek() in ("true", "false"):
            left = ("bool", self.take() == "true")
        else:
            name = self.identifier()
            if self.peek() == ".":
                self.take()
                left = ("field", name, self.identifier())
            elif self.peek() == "(":
                self.take()
                args = []
                while self.peek() != ")":
                    args.append(self.expression())
                    if self.peek() != ",":
                        break
                    self.take()
                self.take(")")
                left = ("call", name, tuple(args))
            else:
                left = ("ref", name)
        precedence = {"||": 1, "&&": 2, "==": 3, "!=": 3}
        while self.peek() in precedence and precedence[self.peek()] >= minimum:
            op = self.take()
            left = (op, left, self.expression(precedence[op] + 1))
        return left

    def type_of(self, expr, params, visit):
        op = expr[0]
        if op == "bool":
            return "Bool"
        if op in ("ref", "field"):
            if expr[1] not in params:
                raise ModelError(f"unbound state parameter {expr[1]}")
            if op == "ref":
                return self.state
            if expr[2] not in self.fields:
                raise ModelError(f"unknown field {expr[2]}")
            return "Bool"
        if op == "call":
            name, args = expr[1:]
            if name not in self.functions:
                raise ModelError(f"unknown function {name}")
            if len(args) != len(self.functions[name].params):
                raise ModelError(f"wrong argument count for {name}")
            for arg in args:
                if self.type_of(arg, params, visit) != self.state:
                    raise ModelError(f"{name} requires {self.state} arguments")
            visit(name)
            return "Bool"
        for arg in expr[1:]:
            if self.type_of(arg, params, visit) != "Bool":
                raise ModelError(f"{op} requires Bool operands; record equality is unsupported")
        return "Bool"

    def expand(self, name, arguments):
        """Inline checked, acyclic predicate calls into a tiny Boolean tree."""
        fn = self.functions[name]
        env = dict(zip(fn.params, arguments))

        def walk(expr):
            op = expr[0]
            if op == "bool":
                return expr
            if op == "field":
                return ("var", env[expr[1]], expr[2])
            if op == "call":
                return self.expand(expr[1], [env[arg[1]] for arg in expr[2]])
            return (op, *(walk(arg) for arg in expr[1:]))

        return walk(fn.body)


def evaluate(expr, env):
    op = expr[0]
    if op == "bool":
        return expr[1]
    if op == "var":
        return env[expr[1]][expr[2]]
    if op == "!":
        return not evaluate(expr[1], env)
    left, right = evaluate(expr[1], env), evaluate(expr[2], env)
    return {"&&": left and right, "||": left or right, "==": left == right, "!=": left != right}[op]


def render(expr, backend):
    op = expr[0]
    if op == "bool":
        return str(expr[1]).upper() if backend == "tla" else str(expr[1]).lower()
    if op == "var":
        return f"{expr[1]}_f_{expr[2]}" if backend == "smt" else f"{expr[1]}.f_{expr[2]}"
    args = [render(arg, backend) for arg in expr[1:]]
    if backend == "smt":
        operator = {"!": "not", "&&": "and", "||": "or", "==": "=", "!=": "distinct"}[op]
        return f"({operator} {' '.join(args)})"
    if op == "!":
        return f"({'~' if backend == 'tla' else '!'}{args[0]})"
    operator = ({"&&": "/\\", "||": "\\/", "==": "=", "!=": "#"} if backend == "tla" else {"&&": "&&", "||": "||", "==": "==", "!=": "!="})[op]
    return f"({args[0]} {operator} {args[1]})"


def load_project(path):
    config = json.loads(path.read_text())
    required = {"source", "initial", "step", "invariant"}
    if not isinstance(config, dict) or set(config) != required or not all(isinstance(x, str) for x in config.values()):
        raise ModelError(f"project must contain exactly these string fields: {sorted(required)}")
    source_path = (path.parent / config["source"]).resolve()
    if not source_path.is_relative_to(path.parent.resolve()):
        raise ModelError("source must be inside the project directory")
    source = source_path.read_text()
    model = Model(source)
    for role, arity in (("initial", 1), ("step", 2), ("invariant", 1)):
        fn = model.functions.get(config[role])
        if fn is None or len(fn.params) != arity:
            raise ModelError(f"{role} must name a predicate with {arity} state parameter(s)")
    terms = {role: model.expand(config[role], ["s", "t"][:arity]) for role, arity in (("initial", 1), ("step", 2), ("invariant", 1))}
    digest = hashlib.sha256((source + "\n" + json.dumps(config, sort_keys=True) + "\n" + VERSION).encode()).hexdigest()
    return model, terms, digest


def finite_check(model, terms):
    states = [dict(zip(model.fields, values)) for values in itertools.product((False, True), repeat=len(model.fields))]
    initial = [i for i, state in enumerate(states) if evaluate(terms["initial"], {"s": state})]
    if not initial:
        return {"status": "error", "reason": "no initial states (vacuous model)"}
    valid = [evaluate(terms["invariant"], {"s": state}) for state in states]
    edges = [[j for j, target in enumerate(states) if evaluate(terms["step"], {"s": source, "t": target})] for source in states]
    parents = {i: None for i in initial}
    queue = deque(initial)
    while queue:
        i = queue.popleft()
        if not valid[i]:
            trace = []
            cursor = i
            while cursor is not None:
                trace.append(states[cursor])
                cursor = parents[cursor]
            return {"status": "counterexample", "trace": trace[::-1], "scope": "reachable finite model"}
        for j in edges[i]:
            if j not in parents:
                parents[j] = i
                queue.append(j)
    witness = next(((i, j) for i in range(len(states)) if valid[i] for j in edges[i] if not valid[j]), None)
    result = {"status": "passed", "scope": "complete reachable Boolean state space", "total_states": len(states), "reachable_states": len(parents), "initial_states": len(initial), "inductive": witness is None, "deadlocks": [states[i] for i in parents if not edges[i]], "stuttering": "permitted; deadlocks are not safety violations"}
    if witness:
        result["noninductive_witness"] = [states[i] for i in witness]
    return result


def emit(model, terms, digest, output):
    output.mkdir(parents=True, exist_ok=True)
    # An emission never inherits a result from a previous model revision.
    (output / "report.json").unlink(missing_ok=True)
    smt_vars = "\n".join(f"(declare-const {p}_f_{f} Bool)" for p in ("s", "t") for f in model.fields)
    init, step, inv = [render(terms[k], "smt") for k in ("initial", "step", "invariant")]
    inv_t = render(rename_state(terms["invariant"], "s", "t"), "smt")
    # Separate files make each result unambiguous. Initial satisfiability rejects vacuity.
    for name, query in (("initial", init), ("base", f"(and {init} (not {inv}))"), ("step", f"(and {inv} {step} (not {inv_t}))")):
        (output / f"{name}.smt2").write_text(f"; Oak experiment {VERSION}; semantic digest {digest}\n(set-logic QF_UF)\n{smt_vars}\n(assert {query})\n(check-sat)\n")
    lean = [f"-- Generated; semantic digest {digest}", "import Lean", "namespace OakPoc", "structure State where"]
    lean += [f"  f_{f} : Bool" for f in model.fields]
    lean += ["  deriving DecidableEq", ""]
    for role, name in (("initial", "oakInitial"), ("step", "oakStep"), ("invariant", "oakInvariant")):
        params = "(s t : State)" if role == "step" else "(s : State)"
        lean += [f"def {name} {params} : Bool :=", f"  {render(terms[role], 'lean')}", ""]
    for name, statement, params in (("initial_safe", "oakInitial s = true → oakInvariant s = true", ("s",)), ("step_preserves", "oakInvariant s = true → oakStep s t = true → oakInvariant t = true", ("s", "t"))):
        lean += [f"theorem {name} ({' '.join(params)} : State) :", f"    {statement} := by"]
        for p in params:
            lean += [f"  rcases {p} with ⟨{', '.join(p+'_'+str(i) for i in range(len(model.fields)))}⟩"]
        cases = [f"cases {p}_{i}" for p in params for i in range(len(model.fields))]
        lean += ["  " + " <;> ".join(cases + ["decide"]), ""]
    lean += ["end OakPoc", ""]
    (output / "Model.lean").write_text("\n".join(lean))
    domain = "[" + ", ".join(f"f_{f} : BOOLEAN" for f in model.fields) + "]"
    tla = ["---- MODULE Model ----", f"\\* Generated; semantic digest {digest}", "EXTENDS TLC", "VARIABLE state", f"StateSpace == {domain}"]
    for role, name in (("initial", "OakInitial"), ("step", "OakStep"), ("invariant", "OakInvariant")):
        params = "s, t" if role == "step" else "s"
        tla += [f"{name}({params}) == {render(terms[role], 'tla')}"]
    tla += ["Init == state \\in StateSpace /\\ OakInitial(state)", "Next == \\E target \\in StateSpace : state' = target /\\ OakStep(state, target)", "Spec == Init /\\ [][Next]_state", "TypeOK == state \\in StateSpace", "Safe == OakInvariant(state)", "====", ""]
    (output / "Model.tla").write_text("\n".join(tla))
    (output / "Model.cfg").write_text("SPECIFICATION Spec\nINVARIANT TypeOK\nINVARIANT Safe\nCHECK_DEADLOCK FALSE\n")
    (output / "manifest.json").write_text(json.dumps({"prototype_version": VERSION, "semantic_digest": digest, "state_fields": model.fields, "fragment": "Boolean finite-state safety", "translation_trusted": True, "generated_is_not_verified": True}, indent=2) + "\n")


def rename_state(expr, old, new):
    if expr[0] == "var":
        return ("var", new if expr[1] == old else expr[1], expr[2])
    if expr[0] == "bool":
        return expr
    return (expr[0], *(rename_state(arg, old, new) for arg in expr[1:]))


def run(command, timeout):
    try:
        completed = subprocess.run(command, capture_output=True, text=True, timeout=timeout)
        return {"exit_code": completed.returncode, "stdout": completed.stdout, "stderr": completed.stderr}
    except subprocess.TimeoutExpired:
        return {"status": "timeout"}
    except OSError as error:
        return {"status": "error", "reason": str(error)}


def external_check(backend, output, timeout, tla_jar=None):
    if backend == "tlc":
        if not tla_jar or not Path(tla_jar).is_file() or not shutil.which("java"):
            return {"status": "unavailable", "reason": "requires java and --tla-jar /path/to/tla2tools.jar"}
        command = ["java", "-cp", str(Path(tla_jar).resolve()), "tlc2.TLC", "-workers", "1", "-metadir", str(output / "tlc-states"), "-config", str(output / "Model.cfg"), str(output / "Model.tla")]
    else:
        if not shutil.which(backend):
            return {"status": "unavailable", "reason": f"{backend} is not on PATH"}
        command = [backend, str(output / "Model.lean")]
    if backend == "z3":
        queries = {}
        for name in ("initial", "base", "step"):
            result = run(["z3", "-smt2", str(output / f"{name}.smt2")], timeout)
            if "status" in result:
                return result | {"query": name}
            answer = result["stdout"].strip()
            if result["exit_code"] != 0 or answer not in ("sat", "unsat", "unknown"):
                return {"status": "error", "query": name, **result}
            queries[name] = answer
        status = "unknown" if "unknown" in queries.values() else "passed" if queries == {"initial": "sat", "base": "unsat", "step": "unsat"} else "failed"
        return {"status": status, "scope": "nonvacuous initialization and inductive preservation", "queries": queries, "evidence": "solver-backed, not kernel-checked"}
    result = run(command, timeout)
    if "status" in result:
        return result
    return {"status": "passed" if result["exit_code"] == 0 else "failed", "scope": "initialization and inductive preservation" if backend == "lean" else "reachable finite-state safety", **result}


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("action", choices=("emit", "check"))
    parser.add_argument("project", type=Path)
    parser.add_argument("--out", type=Path)
    parser.add_argument("--backend", choices=("finite", "z3", "lean", "tlc", "all"), default="finite")
    parser.add_argument("--timeout", type=float, default=30)
    parser.add_argument("--tla-jar")
    args = parser.parse_args(argv)
    try:
        if args.timeout <= 0:
            raise ModelError("timeout must be positive")
        model, terms, digest = load_project(args.project)
        output = (args.out or Path(__file__).parent / "build" / args.project.stem).resolve()
        emit(model, terms, digest, output)
        if args.action == "emit":
            print(f"Generated projections in {output}; no backend has been run.")
            return 0
        results = {"finite": finite_check(model, terms)}
        backends = ("z3", "lean", "tlc") if args.backend == "all" else () if args.backend == "finite" else (args.backend,)
        for backend in backends:
            results[backend] = external_check(backend, output, args.timeout, args.tla_jar)
        report = {"semantic_digest": digest, "prototype_version": VERSION, "results": results}
        (output / "report.json").write_text(json.dumps(report, indent=2) + "\n")
        print(json.dumps(report, indent=2))
        if any(r["status"] in ("failed", "counterexample") for r in results.values()):
            return 1
        if any(r["status"] != "passed" for r in results.values()):
            return 2
        return 0
    except (ModelError, OSError, ValueError, RecursionError) as error:
        print(f"error: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    sys.exit(main())
