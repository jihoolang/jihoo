"""The core specification against the kernel, called by tests/core.py.

Every term of `Term` in compiler/core.jh has an entry in docs/internals/core-spec.md
giving its type, uses, reductions and what it runs as, and the kernel functions the
page names exist. This keeps the page from falling behind by a whole term or rule; it
cannot tell whether a rule's text is accurate.
"""
import re

LABELS = ("**Type.**", "**Uses.**", "**Reduces.**", "**Runs.**")


def validate_preservation(compiler, root, environment, run):
    programs = [*sorted((root / "examples").glob("*.jhc")),
                *sorted((root / "tests/core_accepted").glob("*.jhc")),
                *sorted((root / "tests/core_preserves").glob("*.jhc"))]
    assert len(programs) > 30, programs
    for path in programs:
        run([compiler, "core", "preserves", str(path)], env=environment)


def validate_guide(compiler, root, temporary, environment, run):
    """Every program on the language page compiles and returns what the page says."""
    text = (root / "docs/language/dependent-types.md").read_text()
    programs = re.findall(r"```jihoo\n(.*?)```", text, re.S)
    assert len(programs) == 5, len(programs)
    for i, (program, status) in enumerate(zip(programs, (19, 0, 30, 0, 42))):
        path = temporary / f"guide-{i}.jh"
        path.write_text(program)
        result = run([compiler, "run", str(path)], success=status == 0, env=environment)
        assert result.returncode == status, (i, result.returncode, result.stderr)


def validate_spec(root):
    source = (root / "compiler/core.jh").read_text()
    lower = (root / "compiler/core_lower.jh").read_text()
    enum = source[source.index("pub enum Term {"):]
    enum = enum[:enum.index("\n}\n")]
    terms = re.findall(r"^    ([A-Z][A-Za-z0-9]*)(?:\(|$)", enum, re.M)
    assert len(terms) > 50, terms
    page = (root / "docs/internals/core-spec.md").read_text()
    body = page[page.index("## The terms"):page.index("## Modes of normalization")]
    documented = []
    for entry in re.split(r"^### ", body, flags=re.M)[1:]:
        heading, text = entry.split("\n", 1)
        names = re.findall(r"`([A-Za-z0-9]+)`", heading)
        for label in LABELS:
            assert label in text, (heading, label)
        documented.extend(names)
    assert sorted(documented) == sorted(terms), (
        "not in the specification: " + str(sorted(set(terms) - set(documented))) +
        ", not in the kernel: " + str(sorted(set(documented) - set(terms))))
    # Each named kernel function exists, and the limits are as stated.
    functions = set(re.findall(r"\bfn ([a-z_]+)", source)) | set(re.findall(r"\bfn ([a-z_]+)", lower))
    for name in ("infer", "normal", "equal", "uses", "require", "check", "binder", "owned", "linear",
                 "uses_function", "unsaturated", "not_function", "erased_function", "first_order",
                 "signature", "declare", "case_type", "data_case_type", "recursion_case_type",
                 "view_case_type", "eliminate", "back_motive", "dependent_lend", "outlived", "lending",
                 "sum", "effectful", "may_trap", "reads", "identical", "runtime", "compile"):
        assert name in functions, name
    assert "pub const LIMIT: i64 = 200000" in source and "200,000 terms" in page
    assert "const STEPS: i64 = 1000000" in source and "1,000,000" in page
    assert "pub const DEPTH: u32 = 128" in source and "depth 128" in page
