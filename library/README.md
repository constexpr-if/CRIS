# `library` — reusable verified modules

Logical path: `CRIS.*` (the directory shares the `CRIS` namespace with
[`theories/`](../theories/); see [`_CoqProject`](../_CoqProject)).

Four libraries built with the framework. Each is at once a *client* of
[`theories/`](../theories/) and a *component* other developments can link
against. Every one of them follows the same shape:

1. a **header** fixing the interface (function signatures, the `exports` set);
2. an **implementation** module (suffix `I`) with no specifications;
3. an **abstraction** module (suffix `A`) with the same interface but with
   specifications and ghost state, and typically a trivial body;
4. a **proof** (`…IAproof.v`) that the implementation refines the abstraction,
   packaged as a `ctx_refines` via `main_adequacy`;
5. a **tactics** file giving client-side simulation rules.

| Directory | Files | What it provides |
| --- | --- | --- |
| [`apc/`](apc/) | 8 | **Abstract pure computation** — a call that angelically runs an unbounded but ordinal-bounded number of pure functions |
| [`scheduler/`](scheduler/) | 6 | A **user-level scheduler** (`spawn`/`yield`/`join`) on top of the primitive concurrency events, and the **logically atomic triples** `{{{ P }}} … {{{ Q }}} @ N` / `<<{ αP, αQ }>> @ N` |
| [`helping/`](helping/) | 10 | The **helping** pattern: reasoning as if every thread does its own work, even when threads complete each other's operations |
| [`prophecy/`](prophecy/) | 9 | **Prophecy variables**, with their own extended-trace theory and adequacy proof |

---

## Dependencies between them

```
        scheduler  ──────────┐
         │      │            │
         │      └──► helping │  (helping is stated against a filtered SchI)
         │                   │
         └──► apc            └──► prophecy   (prophecy is independent of the
                                              scheduler, but shares the
                                              fresh-module-name machinery)
```

`scheduler/Atomic.v` is the one most developments will want: it is where a
concurrent data structure's specification is written.

## Why the "I / A" split

CRIS's whole point is that the *specification* module may be physically
impossible. Concretely:

- `SchI` really maintains a thread pool and calls the primitive `Yield`;
  `SchA` hands out `Tid` tokens and lets `join` have a Hoare specification.
- `ProphecyI.new` returns `tt`; `ProphecyA.new` returns a `proph` resource
  recording a value that has not been chosen yet.
- `HelpingOff.run` does its own work; `HelpingOn.run` may discover the work
  already done.
- `APCI.apc` does nothing; `APCA.apc` runs an angelically-chosen sequence of
  pure calls.

In each case the refinement goes *implementation ⊒ abstraction* — the client
reasons against the abstraction, and the refinement transfers its conclusion
to the implementation. The three-module variants (`APCI`/`APCA`/`APCC`,
`HelpingOff`/`HelpingOn`/`HelpingDummy`) additionally have a "client view"
module that is trivial again, so the scaffolding disappears at the end.

## The fresh-name problem

`helping/` and `prophecy/` are both parameterised by a module name `mn`, and
their main theorems (`helping_main`, `prophecy_main`) quantify over it. The
name is instantiated with `mname_long sz` for an `sz` larger than anything in
the client, using `maxlen` / `string_ex_not_in` from
[`theories/lib/Coqlib.v`](../theories/lib/Coqlib.v) and
`maxlen_get_fids_union` from [`theories/common/Fn.v`](../theories/common/Fn.v).
That is what makes it sound to link a *fresh* instance of the library into an
arbitrary program.
