# `theories/filter` — event filters and module introduction/elimination

Logical path: `CRIS.filter`.

A *filter* shrinks a module's event mask so that certain events become
undefined behaviour. Since a module with a smaller mask can do strictly less,
filtering is always a refinement in one direction; the interesting content of
this directory is the *other* direction — when may a filter be **eliminated**,
and when may a whole module be **introduced** into a program?

Together these give the two structural rules a client needs when building a
program bottom-up:

- `intro_filter` / `intro_module` — you may add a module and blacklist the
  calls it provides;
- `elim_filter` / `elim_module` — you may drop them again.

(This directory used to live at `theories/simulations/filter`; see the
`Unreleased` entry in [`CHANGELOG.md`](../../CHANGELOG.md).)

---

## `CallFilter.v` — filtering by function name

**`Module CFilter`.** A `gset string` `bl` ("blacklist") selects which
function names a module may call or spawn.

- `msk_filter_in s msk` / **`msk_filter_out s msk`** — restrict a mask so that
  `Call fn` and `Spawn fn` are allowed only when `fn ∈ s` (resp. `fn ∉ s`);
  every other event is untouched.
- **`CFilter.filter bl m : Mod.t`** — apply `msk_filter_out bl` to every
  function's mask, leaving scopes and initial state alone (the four record
  obligations are inherited from `m`).
- `fnsem_lookup_result_filter` (cost 20) plus a matching `Hint Extern` so
  certificate-based lookup sees through `filter`.
- Algebraic facts: `filter_app` (`filter` distributes over `★`),
  `filter_empty` (`filter ∅ = id`), `filter_union`
  (`filter (s1 ∪ s2) = filter s1 ∘ filter s2`).
- **`sim_filter_intro`** : `⊢ ISim.t open (filter bl m) m IstEq` — the filtered
  module simulates the unfiltered one (proved by `cStartModSim` + `cCoind` +
  a case analysis via `case_itrH`).
- **`sim_filter_elim`** : `⊢ ISim.t closed m (filter bl m) IstEq`, provided the
  module's own function names are disjoint from `bl` (`get_fids (dom …) ## bl`)
  — i.e. the filter never blocks a call the module could actually service.
- `intro_filter : ⊢ ctx_refines m (filter bl m)` and
  `elim_filter : ⊢ refines (filter bl m) m` (the latter under the same
  disjointness hypothesis).
- **`intro_module bl m mc`** : `⊢ refines (filter bl m) (filter bl m ★ mc)` —
  a fresh module `mc` may be linked in, provided `mc` is well-formed, the
  scopes are disjoint, `m`'s functions avoid `bl`, `mc`'s functions are
  *inside* `bl`, and `mc` does not define `entry`. Proved via
  `gsim_closed_adequacy` and `gsim_mod_intro`; the file marks the `Qed` as
  `(*SLOW*)`.
- `real_mod` — filtering preserves realness.
- `smod_filter_intro` : the `SMod`-level counterpart,
  `⊢ ctx_refines (SMod.to_mod sp md) (SMod.to_mod sp (SMod.filter (msk_filter_out bl) md))`.
- `filter_masked` (a blacklisted `Call`/`Spawn` really is masked out),
  `filter_cancellable` (filtering preserves `SMod.cancellable`).
- Outside the module: the `fnsem_lookup` `Hint Extern`, and the tactic
  **`cfilter_solver`** for discharging `filter`-equality goals.

## `SysFilter.v` — filtering out the concurrency events

**`Module SFilter`.** The same construction, but the mask being removed is
fixed: the *system* events.

- `is_sysE : emask` — true exactly on `Spawn`, `Yield` and `GetTid`.
- `msk_filter_out msk := λ X e, negb (is_sysE _ e) && msk X e`.
- `SFilter.filter m : Mod.t` — apply it to every function of `m`.
- `sim_filter_intro : ⊢ ISim.t open (filter m) m IstEq`.
- `smod_filter_intro : ⊢ ctx_refines (SMod.to_mod sp md) (SMod.to_mod sp (SMod.filter msk_filter_out md))`.
- `filter_masked` — a system event is masked out after filtering.
- `filter_cancellable` — filtering preserves `SMod.cancellable`.
- **`cfilter_comm`** — the two filters commute:
  `SMod.filter (CFilter.msk_filter_out bl) ∘ SMod.filter SFilter.msk_filter_out
   = SMod.filter SFilter.msk_filter_out ∘ SMod.filter (CFilter.msk_filter_out bl)`.
