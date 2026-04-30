# MooncakeFormal

Mooncake KV cache disaggregated serving — Coq formalization using the formalities architecture.

## Build

```
coq_makefile -f _CoqProject -o Makefile && make
make quality    # health score (A-F)
make lint       # fast lint
make ci         # CI gate (blocks on tier violations, admitted proofs)
```

## Rules for .v files

Every file must have a header with LAYER, Tier, @source, @fidelity, @abstraction.
See `theories/Core/Core.v` for the template.

- Layer N may only import Layer <= N
- Layer 4 must never unfold — work through the typeclass interface
- Core tier: fully proven (Qed), no Axiom/Parameter outside Module Type
- Exploratory tier: Admits allowed, must declare count in header
- Use `#[export]` or `#[local]` on all Instance/Hint declarations
- Use `lia` not `omega`
- Run `make lint` before committing

## Adding new files

1. Create the .v file under `theories/` with a proper header
2. Add the file path to `_CoqProject`
3. Re-run `coq_makefile -f _CoqProject -o Makefile`

## Formalization workflow

1. **Survey** source code — identify types, functions, invariants worth modeling
2. **Transliterate** — source types become Coq Record/Inductive, source functions
   become Definition/Fixpoint, source invariants become Lemma/Theorem
3. **Annotate** — set @source to file:lines, choose @fidelity and @abstraction level
4. **Prove** layer by layer (Russian Dolls pattern):
   definitions → base lemmas → typeclass instances → domain lemmas → application theorems
5. **Validate** — `make ci` must pass before merging

## Libraries

DML (DistributedML) is always available at `lib/distributed_ml_coq/` (git submodule).
Core import: `Require Import DistributedML.Core.DecidableEq.`

After cloning: `git submodule update --init --recursive`

## Key files

- `design.txt` — architecture, modeling decisions, headline theorems, known gaps
- `_CoqProject` — build configuration (update when adding .v files)
- `Makefile.local` — quality and build targets

## Source alignment

Source code is at `data_source/Mooncake/`.

- `make alignment` shows coverage (which source entities are modeled)
- `make drift` detects structural changes in source
- Run `make drift` before pulling source submodule updates
- Every .v file that models source code needs @source annotation pointing
  to the specific file and line range it formalizes
