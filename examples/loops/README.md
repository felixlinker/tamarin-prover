# Loop Examples

This directory contains models of loops and protocols that use them.
Some of these examples are referenced in the paper "Looping for Good: Cyclic Proofs for Security Protocols."
This directory contains models proven with trace induction.
The subdirectory `/cyclic` contains the corresponding models proven with cyclic induction.
All models can be proven automatically.
Some models use custom tactics for that purpose.
To construct proofs for a theory, run (`PROOF_FILE` to be replaced):

```sh
tamarin-prover --prove PROOF_FILE
```

We provide a table that maps theory names as referenced in the paper with file names below.
The paper also references other examples not included in this folder, which can be found in the directory `examples/features/cyclic`.

| Theory Name | File Name |
|-------------|-----------|
| Loop | `Minimal_Loop_Example.spthy` |
| Hash Chain | `Minimal_Hash_Chain.spthy` |
| Crypto API | `Minimal_Crypto_API.spthy` |
| Key Renegotiation | `Minimal_KeyRenegotiation.spthy` |
| Create, Use, Destroy | `Minimal_Create_Use_Destroy.spthy` |
| TESLA 1 | `TESLA_Scheme1.spthy` |
| TESLA 2 | `TESLA_Scheme2_lossless.spthy` |
