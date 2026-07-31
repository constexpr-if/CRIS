# `extract` — OCaml extraction

Logical path: `CRIS` (the directory is mapped into the `CRIS` namespace by
[`_CoqProject`](../_CoqProject)).

Built with `make extract` (see the `extract` / `extract-quick` targets in
[`Makefile`](../Makefile)). Besides the single `.v` file below, the directory
holds the OCaml side of the pipeline: `bin/` (the driver `main.ml` and its
`dune` file), `coq_extracted/` (the extraction output), `dune-project`,
`test.sh`, `clean.sh`, and `Example0.v.example`.

## `ExtrOcamlCRIS.v`

The extraction configuration. It requires `Extraction`,
`ExtrOcamlBasic`, `ExtrOcamlNativeString` and `CRIS.scheduler.SchI` /
`SchHeader`, blacklists the module names `List`, `String` and `Int`, and then
overrides three constants that cannot be extracted meaningfully:

- **`excluded_middle_informative ⇒ "true"`** — classical case analysis is
  erased; the extracted code always takes the left branch. This is sound for
  running programs because in CRIS's operational code the two branches differ
  only in ghost content.
- **`SchI.choose_index`** — the scheduler's angelic choice of which thread to
  run next cannot be computed, so it is replaced by an *observable*
  interaction: the extracted code emits `IO ("choose_index", tids)` and lets
  the driver in [`bin/main.ml`](bin/main.ml) resolve it. The replacement is
  written out as raw OCaml because it has to reconstruct the `subevent`
  coercion tower by hand. (The `Unreleased` entry in
  [`CHANGELOG.md`](../CHANGELOG.md) records a change to this setting.)
- **`Sch.choose_optbool`** — likewise, the client-side yield loop's
  `Choose (option bool)` becomes `IO ("choose_optbool", ())`.

In other words: everything angelic in the semantics becomes an external
oracle in the extracted executable.
