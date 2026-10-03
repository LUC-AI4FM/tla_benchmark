# Dependency modules

These modules are not benchmark items. They are included only so that the grader can resolve
modules that a generated specification imports.

| File | Source | Why it is here |
|---|---|---|
| `MultiNodeReads.tla` | microsoft/CCF, `tla/consistency/MultiNodeReads.tla` (redistributed unchanged under the repository's license) | Gemini-2.5-pro's default-regime output for specification 577 imports it. The project grader resolved it from the crawled corpus. Without it, that output does not parse in the release layout. |
| `test219a.tla` | apalache-mc/apalache, `test/tlaplus-suite/test219a.tla` (redistributed unchanged under the repository's license) | The gold reference 392 (`test219`, a tool regression test) instantiates it. Without it, that reference does not parse in the release layout. |
