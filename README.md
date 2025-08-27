# The Tamarin Prover with Cyclic Induction

This branch of the Tamarin prover repository contains an implementation of cyclic induction for protocol verification as well as case studies.

## Installation

Follow the instructions for [Compiling from source in the Tamarin manual](https://tamarin-prover.com/manual/master/book/002_installation.html#sec:LinuxSrcInstall).

Be sure to use the repository: `https://github.com/felixlinker/tamarin-prover.git` and branch `cyclic`.

## Case Studies

Our paper references three sets of case studies.
We provide these case studies in two directories.
We provide a table that maps each case study theory to the corresponding source files below.
As we prove each case study with cyclic induction (CI) and trace induction (TI), we provide two source files.
We timed proof construction on a MacBook with an Apple M2 Max CPU and 32 GB of memory and provide timings for each case study in seconds below.
Timings are also provided in `timings.xslx`.

To provide a high-level overview, all our case studies are contained in the directories `examples/loops` and `examples/features/cyclic`.
Each directory contains a README providing details on how to verify each case study and a subdirectory, `cyclic` and `trace-induction` respectively, for the corresponding CI/TI proofs of the theories in the parent directory.

| Case Study Set | Case Study | Source File Name | Path CI | Path TI | Time CI | Time TI | Time Diff | Relative Diff |
| -------------- | ---------- | ---------------- | ------- | ------- | ------- | ------- | --------- | ------------- |
| 1 | Loop | `Minimal_Loop_Example.spthy`| `examples/loops/cyclic` | `examples/loops` |0.04|0.05|-0.01|-20.00%|
| 1 | Hash Chain | `Minimal_HashChain.spthy` | `examples/loops/cyclic` | `examples/loops` |0.08|0.08|0|0.00%|
| 1 | Crypto API | `Minimal_Crypto_API.spthy` | `examples/loops/cyclic` | `examples/loops` |0.05|0.05|0|0.00%|
| 1 | Key Renegotiation | `Minimal_KeyRenegotiation.spthy` | `examples/loops/cyclic` | `examples/loops` |0.07|0.05|0.02|40.00%|
| 1 | Create, Use, Destroy | `Minimal_Create_Use_Destroy.spthy` | `examples/loops/cyclic` | `examples/loops` |0.05|0.07|-0.02|-28.57%|
| 1 | Alternating Loop | `alternating-loop.spthy` | `examples/features/cyclic` | `examples/features/cyclic/trace-induction` |0.11|0.14|-0.03|-21.43%|
| 1 | Nested Loop | `nested-loop.spthy` | `examples/features/cyclic` | `examples/features/cyclic/trace-induction` |0.1|0.08|0.02|25.00%|
| 1 | Revealing Loop | `revealing-loop.spthy` | `examples/features/cyclic` | `examples/features/cyclic/trace-induction` |0.07|0.08|-0.01|-12.50%|
| 2 | Signal 1 | `Signal.spthy` | `examples/features/cyclic` | `examples/features/cyclic/trace-induction` |38.25|36.89|1.36|3.69%|
| 2 | Signal 2 | `SignalRevealing.spthy` | `examples/features/cyclic` | `examples/features/cyclic/trace-induction` |48.48|44.98|3.5|7.78%|
| 3 | Up and Down | `up_and_down.spthy` | `examples/features/cyclic` | `examples/features/cyclic/trace-induction` |0.06|0.21|-0.15|-71.43%|
| 3 | Loop Exits | `loop-exits.spthy` | `examples/features/cyclic` | `examples/features/cyclic/trace-induction` |0.12|0.06|0.06|100.00%|
| 3 | TESLA 1 | `TESLA_Scheme1.spthy` | `examples/loops/cyclic` | `examples/loops` |2.51|2.54|-0.03|-1.18%|
| 3 | TESLA 2 | `TESLA_Scheme2.spthy` | `examples/loops/cyclic` | `examples/loops` |2.62|0.87|1.75|201.15%|

We also timed both Signal case studies without proving any auxiliary lemmas when using cyclic induction.
Results of that are below.

| Case Study | Source File Name | Path CI | Path TI | Time CI | Time TI | Time Diff | Relative Diff |
| ---------- | ---------------- | ------- | ------- | ------- | ------- | --------- | ------------- |
| Signal 1 | `Signal.spthy` | `examples/features/cyclic` | `examples/features/cyclic/trace-induction` |37.85|36.89|0.96|2.60%|
| Signal 2 | `SignalRevealing.spthy` | `examples/features/cyclic` | `examples/features/cyclic/trace-induction` |44.82|44.98|-0.16|-0.36%|


## Implementation Details

We describe relevant source files.
Our implementation is not limited to these files, but they provide the most important aspects.

| Source File | Description |
| ----------- | ----------- |
| `lib/theory/src/Theory/Proof/Cyclic.hs` | Provides data structures to manage a cyclic (pre)proof. |
| `lib/theory/src/Theory/Constraint/System/Inclusion.hs` | Provides the inclusion check between two constraint systems. |
| `lib/theory/src/Theory/Constraint/SystemMatch.hs` | Provides a data structure to rename one constraint system to another. |
