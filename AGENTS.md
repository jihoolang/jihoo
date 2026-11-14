# Repository instructions

Write README.md in English.

## Local build resources

This workstation has 32 GB of RAM. Unbounded Lean jobs have caused system OOMs.

- Run every local compiler, Lean/Lake check, and test that launches a compiler
  through `scripts/proof-limits.sh COMMAND ...`, including in isolated copies.
- The wrapper serializes heavy jobs across all agents and puts their complete
  process trees in a separate cgroup: 6 GiB hard limit per job, 8 GiB aggregate.
- Never bypass these limits or increase them to make a failing proof pass.
  Investigate excessive allocation instead. Read-only inspection and editing
  may run concurrently; compiler/checker jobs must remain serialized.
- Use one Lean thread and one Jihoo code generation unit. Pass `-M 4096 -j 1`
  to standalone Lean invocations. The Lake configuration applies the same
  limits to module compilation.
- Keep large build output in log files and inspect concise failure summaries.
