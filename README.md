# Interval Scheduling with Eligible Machine Sets

A [Lax archive](https://github.com/lax-archive/lax) submission (`lax-470956`) formalizing
the three results of Hermelin, Itzhaki, Molter and Shabtay, *On the Parameterized
Complexity of Interval Scheduling with Eligible Machine Sets*, Journal of Computer and
System Sciences 144 (2024): W[1]-hardness for the number of machines, para-NP-hardness for
the largest processing time, and fixed-parameter tractability for the two combined.

**Status.** All statements are proved, with no `sorry`. Theorems 1 and 3 rest on nothing
beyond Lean's three standard axioms. Theorem 2 rests, in addition, on the NP-hardness of
(3,4)-satisfiability (Tovey 1984), which is proved in the submission `lax-345332` and used here
through its statement (`SatVariant.sat34_npHard` is discharged from
`Lax345332.ThreeFourSat.npHard`); the archive counts Theorem 2 as proved once that submission
is. The class W[1] is not formalized; Theorem 1 is stated as the fpt-reduction from
Multicoloured Clique, whose W[1]-completeness is cited. See `abstract.md` for the mathematics.

## Prerequisites

Lean `v4.33.0` via [elan](https://github.com/leanprover/elan), and the
[`lax` CLI](https://github.com/lax-archive/lax). The mathlib revision is pinned in
`manifest.yaml`; Lake fetches it on first build.

## Verification

Run the archive validation:

    lax build .

Its last stage, *Inspecting the statements*, pairs every statement with its proof and
reports `17 concepts · 27 proofs`.

To check a single module while editing, from `proofs/`:

    lake build Lax470956Proofs.Theorem3Fpt

To audit axioms yourself, write a scratch file **outside** the package:

    cat > /tmp/ax.lean <<'LEAN'
    import Lax470956Proofs
    #print axioms Lax470956Proofs.Construction1Main.mcc_fptReduces_byMachines
    #print axioms Lax470956Proofs.Theorem2.npHardOn_allSchedulable_pmax_le
    #print axioms Lax470956Proofs.Theorem3.fptTime_byMachinesAndPmax
    LEAN

and run `lake env lean /tmp/ax.lean` from `proofs/`. Expect `propext`, `Classical.choice`
and `Quot.sound` for all three, and `Lax345332.ThreeFourSat.npHard` for the second.

> Anything placed inside `proofs/Lax470956Proofs/` must also be imported by
> `Lax470956Proofs.lean`, or the build is rejected. Keep scratch work elsewhere.

## Reading Guide

The `concepts/` directory contains the definitions and theorem statements; `proofs/`
contains their Lean proofs. Start with the definitions, encodings, and main theorems.

Suggested order:

1. `abstract.md` — the three results in prose.
2. `concepts/Lax470956/Scheduling.lean` — the problem: instances, feasible schedules, the
   optimum.
3. `concepts/Lax470956/InstanceEncoding.lean` and `BinaryEncoding.lean` — how an instance
   becomes a word. This is where a scheduling problem becomes something a machine is handed,
   so it deserves the closest reading.
4. `concepts/Lax470956/ParameterizedComplexity.lean`, `NPHardness.lean` and
   `PolynomialReduction.lean` — what FPT, fpt-reduction and NP-hardness mean here, on the
   word RAM.
5. `concepts/Lax470956/SchedulingProblems.lean` — the problems the theorems are about.
6. `concepts/Lax470956/Theorem1.lean`, `Theorem2.lean`, `Theorem3.lean` — the results.
7. The machinery behind each: `MulticolouredClique.lean` and `Construction1.lean` for
   Theorem 1; `SatVariant.lean`, `Exact34Encoding.lean` and `Construction2.lean` for
   Theorem 2; `Preprocessing.lean` and `DynamicProgram.lean` for Theorem 3.

In `proofs/`, the entry points are `Construction1Main.lean` (Theorem 1), `Theorem2.lean`
(Theorem 2) and `Theorem3.lean` with `Theorem3Fpt.lean` (Theorem 3, in its explicit and
its qualitative form). The `Construction1*.lean` and `Construction2*.lean` files carry the
correctness of the two reductions and the word-RAM programs that compute them;
`DynamicProgram.lean`, `FptProg.lean` and `FptMain.lean` carry the dynamic program and its
running time.

## Layout

    manifest.yaml     id, title, authors, pinned Lean + mathlib, bibliography
    abstract.md       the prose account, rendered on the archive website
    concepts/         statements only, as axioms — 17 modules
    proofs/           the proofs, each tagged with the statement it discharges — 81 modules

A concept module states results as `axiom`s. A proof is a `theorem` whose docstring carries
`conclusion: <that axiom's full name>`; the build checks the pairing. Every axiom has a proof;
`SatVariant.sat34_npHard`, Tovey's theorem, is discharged from the statement of `lax-345332`.

## Dependencies

Beyond mathlib, this submission builds on six others in the archive:

- `lax-434930`, *Classical Complexity Classes* (Édouard Bonnet): P and NP.
- `lax-429075`, *The Cook–Levin Theorem* (Édouard Bonnet): CNF formulas and polynomial
  many-one reductions.
- `lax-808846`, *The Word RAM* (Jan Dreier): the machine model, the IMP+ language and its
  verified compiler.
- `lax-271696`, *Algorithmic Experiments on a Random Access Machine* (Jan Dreier): the
  encoding of a graph as a word.
- `lax-759944`, *Computability and Polynomial-Time Equivalence of Turing Machines and Word
  RAMs* (Szymon Toruńczyk).
- `lax-345332`, *(3,4)-SAT and [2,3]-Bounded 3-SAT Are NP-Hard* (Yuval Itzhaki, Claude): Tovey's theorem, cited through
  its statement. While that submission is a draft the build has to admit it as a sibling
  checkout: `lax build . --nonstrict`.

Three packages are required with their proofs, and the build warns about each
(`proof-dependency`): the IMP+ language and its `run_vcg` tactic from `lax-808846`, the
composition of polynomial-time machines from `lax-434930`, and the transfer of a word-RAM
time bound to a Turing machine from `lax-759944`. None of these is stated as a result in
its submission, so there is no statement to cite instead.

The archive itself is described in `lax-242665`, *An Introduction to Lax* (Édouard Bonnet,
Jan Dreier, Clemens Kuske).

## License

Apache 2.0, as required by the archive. See `LICENSE`.
