# The Tamarin Prover with Cyclic Induction

This branch of the Tamarin prover repository contains an implementation of cyclic induction for protocol verification.
It comes with two sets of case studies.

## Installation

Follow the instructions for [Compiling from source in the Tamarin manual](https://tamarin-prover.com/manual/master/book/002_installation.html#sec:LinuxSrcInstall).

Be sure to use the repository: `https://github.com/felixlinker/tamarin-prover.git` and branch `cyclic`.

## Case Studies

Our paper references three sets of case studies.
We provide these case studies in two directories.
We provide a table that maps each case study theory to the corresponding source files below.
As we prove each case study with cyclic induction (CI) and trace induction (TI), we provide two source files.

To provide a high-level overview, all our case studies are contained in the directories `examples/loops` and `examples/features/cyclic`.
Each directory contains a README providing details on how to verify each case study and a subdirectory, `cyclic` and `trace-induction` respectively, for the corresponding CI/TI proofs of the theories in the parent directory.

| Case Study Set | Case Study | Source File Name | Path CI | Path TI |
| -------------- | ---------- | ---------------- | ------- | ------- |
| 1 | Loop | `Minimal_Loop_Example.spthy`| `examples/loops/cyclic` | `examples/loops` |
| 1 | Hash Chain | `Minimal_HashChain.spthy` | `examples/loops/cyclic` | `examples/loops` |
| 1 | Crypto API | `Minimal_Crypto_API.spthy` | `examples/loops/cyclic` | `examples/loops` |
| 1 | Key Renegotiation | `Minimal_KeyRenegotiation.spthy` | `examples/loops/cyclic` | `examples/loops` |
| 1 | Create, Use, Destroy | `Minimal_Create_Use_Destroy.spthy` | `examples/loops/cyclic` | `examples/loops` |
| 1 | Alternating Loop | `alternating-loop.spthy` | `examples/features/cyclic` | `examples/features/cyclic/trace-induction` |
| 1 | Nested Loop | `nested-loop.spthy` | `examples/features/cyclic` | `examples/features/cyclic/trace-induction` |
| 1 | Revealing Loop | `revealing-loop.spthy` | `examples/features/cyclic` | `examples/features/cyclic/trace-induction` |
| 2 | Signal 1 | `Signal.spthy` | `examples/features/cyclic` | `examples/features/cyclic/trace-induction` |
| 2 | Signal 2 | `SignalRevealing.spthy` | `examples/features/cyclic` | `examples/features/cyclic/trace-induction` |
| 3 | Up and Down | `up_and_down.spthy` | `examples/features/cyclic` | `examples/features/cyclic/trace-induction` |
| 3 | Loop Exits | `loop-exits.spthy` | `examples/features/cyclic` | `examples/features/cyclic/trace-induction` |
| 3 | TESLA 1 | `TESLA_Scheme1.spthy` | `examples/loops/cyclic` | `examples/loops` |
| 3 | TESLA 2 | `TESLA_Scheme2.spthy` | `examples/loops/cyclic` | `examples/loops` |

## Implementation Details

We describe relevant source files.
Our implementation is not limited to these files, but they provide the most important aspects.

| Source File | Description |
| ----------- | ----------- |
| `lib/theory/src/Theory/Proof/Cyclic.hs` | Provides data structures to manage a cyclic (pre)proof. |
| `lib/theory/src/Theory/Constraint/System/Inclusion.hs` | Provides the inclusion check between two constraint systems. |
| `lib/theory/src/Theory/Constraint/SystemMatch.hs` | Provides a data structure to rename one constraint system to another. |
