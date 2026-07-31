# Contextual Refinement with Imaginary Specifications (CRIS)

## Repository layout

| Directory | Contents |
| --- | --- |
| [`theories/`](theories/) | The framework: support library, separation logic, events and behaviours, modules, the simulation tower, filters, and cancellation |
| [`library/`](library/) | Verified reusable modules: APC, a user-level scheduler with logically atomic triples, helping, and prophecy variables |
| [`itreeS/`](itreeS/) | A stripped-down fork of the Interaction Trees library in which strong bisimulation *is* equality |
| [`extract/`](extract/) | OCaml extraction settings and driver |

Every directory containing Coq sources has its own `README.md` describing each
file; start from [`theories/README.md`](theories/README.md).

## Development environment
CRIS requires Coq 8.20. We offer two options for installing dependencies.

### Using opam
Requirement: opam (>=2.0.0)
```
./configure
```

### Using nix flake
Requirement: nix with flake enabled
```
nix develop
```

## Build
Build the project
```
make -j
```

## Contributing
Submit pull requests against the `master` branch.

Before requesting review:
- Rebase the branch to remove `WIP`, `fixup`, and other incidental commits.
- Keep each commit focused on one logical change.
- Add user-visible changes to the `Unreleased` section of
  [`CHANGELOG.md`](CHANGELOG.md).
- Ensure the project builds successfully.

Accepted pull requests preserve their individual commits rather than being
squashed, so the commit history should be ready for publication.
