# `library/apc` — APC: abstract "pure" computation

Logical path: `CRIS.apc`.

APC ("**a**bstract **p**ure **c**omputation") is the CRIS idiom for *hiding an
unbounded but terminating amount of specification-level work*. A client that
needs some pure functions to have run — but does not care which, or how many —
calls `APC.apc o`, whose body angelically chooses a finite sequence of calls to
functions in the "pure" spec map. Termination is enforced by two ordinals: a
**width** ordinal that strictly decreases at each iteration and a **depth**
ordinal that bounds the callees.

The directory follows the standard CRIS three-module pattern (I → A → C), and
proves that the chain refines:

```
APCI.t        (implementation: apc is just Choose _, i.e. does nothing)
   ⊒ APCA.t   (abstraction:    apc actually runs the APC loop)
   ⊒ APCC.t   (client view:    apc is again trivial, but carries apc_spec)
```

Ordinals come from the external `Ordinal` library (`Ordinal`, `Arithmetic`,
`Inaccessible`).

---

## `APCHeader.v`

The interface: `APC.apc := fnsig "APC.apc" (fntyp Ord.t ())` and
`APC.exports := {[ fn_name apc ]}`.

## `APC.v` — the APC loop itself

- **`fspec_apc o DPQ`** — the shape every "pure" function must have: the
  precondition is `DPQ x`'s first component together with
  `⌜∃ vo, y = vo↑ ∧ o x ≤ vo⌝`, i.e. the *virtual* argument must be an
  ordinal at least as large as the function's own depth `o x`; the
  postcondition is `DPQ x`'s second component.
- `pure_body` — the canonical body of a pure function: call `APC.apc` with the
  depth ordinal and return.
- **`_APC dep_ord SpPure wid_ord`** — the loop, defined by well-founded
  recursion on `Ord.lt`. Each iteration angelically chooses whether to break;
  if not, it chooses a smaller width ordinal `wid_next`, a function name `fn`,
  and a depth ordinal `o`, *guarantees* that `fn` has a spec in `SpPure` and
  that `o < dep_ord`, calls `fn` with `o↑`, and recurses.
  `APC dep_ord SpPure` chooses the initial width ordinal.
  `unfold_APC` is the unfolding lemma; `_APC` is then `Opaque`.
- `Section aux`: `map_fst_map_map_snd_refl`, `find_body`, `pure_specbody`
  (the sandboxed, Hoare-wrapped `pure_body`), and `pure` (choose an ordinal
  and call `apc`).

## The three modules

| File | Module | `apc`'s body | spec |
| --- | --- | --- | --- |
| `APCI.v` | `APCI.smod` / `APCI.t` | `fbody_trivial` (a bare `Choose`) | none; mask is `msk_real (msk_scp ["APC"] msk_true)` |
| `APCA.v` | `APCA.smod SpPure` / `APCA.t SpPure sp` | `cfunN … (apc_body SpPure)` = the real APC loop | `apc_spec` |
| `APCC.v` | `APCC.smod` / `APCC.t Sp` | `fbody_trivial` again | `APCA.apc_spec` |

`APCA.apc_spec` says the argument is an ordinal and the virtual and physical
arguments agree; the postcondition is `True`. `APCA.sp` / `APCC.Sp` are the
singleton spec maps `{[fid APC.apc @ apc_spec]}`; `APCA.init_cond` and
`APCC.init_cond` are `emp`. All three modules use `scp := ["APC"]` and an
empty initial state, and discharge their record obligations with `mod_tac`.

## `APCIAproof.v` — `APCI ⊒ APCA`

`APCIA.Ist := λ _ _, True`. `simF_apc` proves the single function: the
abstract side runs the loop but can immediately `Choose true` to break, so it
matches the trivial implementation. `sim : ⊢ ISim.t open APCAMod APCIMod Ist`,
and `ctxr : ⊢ ctx_refines APCI.t (APCA.t SpPure SpA)` via `main_adequacy`.

## `APCACproof.v` — `APCA ⊒ APCC` in an arbitrary context

The interesting direction: showing that the APC loop can be *introduced*. It is
proved in the presence of an arbitrary context module `md`, under the
hypotheses

- `APCA.sp ⊆ sp_a` and `sp_pure ⊆ sp_a`;
- **`PureIsPure`** — every function in `sp_pure` is implemented in `md` by
  exactly `pure_specbody sp_a msk (Some fsp)`, with a mask that permits the
  call to `APC.apc` and all of `Take`, `Choose`, `Assume`, `Guarantee`.

`IstFull := IstProd (IstSB APCC.scopes Ist) IstEq`. `simF_apc` is the main
proof (a `cCoind` over the loop, using `prependRetS` and `cBind` to line the
two sides up), `sim` assembles the module simulation, and
`ctxr : ⊢ ctx_refines (APCA.t sp_pure sp_a ★ md) (APCC.t sp_c ★ md)`.

## `APCTactics.v` — client-side reasoning

`Section LEMMAS` (parameterised by the usual `wsim` context) proves:

- **`wsim_apc_src`** — when the *source* is running an APC loop, break out of
  it immediately (choose `true`), leaving the continuation.
- **`wsim_apc_src_call_tgt_weaker`** — the key rule: a source APC loop can
  simulate a *target* `Call fn args`, provided `fn` is in `sp_pure` with a
  spec implied (`fspec_imply`) by an `fspec_apc`, and the width/depth ordinals
  decrease (`ow_fn < ow_src`, `od_fn < od_src`). The caller supplies `P` and
  receives `Q`, exactly as for an ordinary call.
- **`wsim_apc_src_call_tgt`** — the same with `fspec_imply_refl`.

Tactics: `apcS/` and `apcS` (break out of an APC loop),
`apcCallWeak/` / `apcCallWeak` and `apcCall/` / `apcCall`
(`… hyps as (vret st_src st_tgt) IST`) for matching a target call against one
iteration of the loop. The `/`-suffixed variants leave the goal unfolded; the
plain ones re-hide the continuations with `cHideS`/`cHideT`.
