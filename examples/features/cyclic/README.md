# Cyclic Proof Examples

This directory contains models that were added to evaluate cyclic proofs for Tamarin.
These examples are referenced in the paper "Looping for Good: Cyclic Proofs for Security Protocols."
This directory contains models proven with cyclic induction.
The subdirectory `/trace-induction` contains the corresponding models proven with trace induction.
All models can be proven automatically.
Some models use custom tactics for that purpose.
To construct proofs for a theory, run (`PROOF_FILE` to be replaced):

```sh
stack run -- --derivcheck-timeout=0 --prove PROOF_FILE
```

> [!NOTE]
> Not all proofs in the theories "Up and Down", "Signal 1," and "Signal 2" terminate.
> To avoid non-termination, pass the option `--prove="Auto_*"` instead of `--prove` when proving these theories.

`stack run` will compile Tamarin from source and use that binary.

We provide a table that maps theory names as referenced in the paper with file names below.
The paper also references other examples not included in this folder, which can be found in the directory `examples/loops`.

| Theory Name | File Name |
|-------------|-----------|
| Alternating Loop | `alternating-loop.spthy` |
| Nested Loop | `nested-loop.spthy` |
| Revealing Loop | `revealing-loop.spthy` |
| Signal 1 | `Signal.spthy` |
| Signal 2 | `SignalRevealing.spthy` |
| Up and Down | `up_and_down.spthy` |
| Loop Exits | `loop-exits.spthy` |
