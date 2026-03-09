# Embed Maude as a Library

## Goal

Replace Tamarin's current process-based Maude integration with an embedded library-based integration built on `maude-bindings`.

## Required Outcomes

- No communication with Maude over stdin/stdout.
- No runtime dependency on an external `maude` executable.
- AC unification is no longer delayed because Maude is external.
- Tamarin keeps one stable Maude context per loaded theory.

## Design Decisions

- Keep a theory-scoped Maude context for the lifetime of the loaded theory.
- Preserve the existing context-carrying abstraction initially (`SignatureWithMaude`, `WithMaude`, or renamed equivalents) if it remains useful for threading theory-local state.
- Do not integrate Haskell directly with SWIG-generated bindings.
- Use Haskell FFI against a small handwritten C ABI shim implemented on top of the existing `maude-bindings` C++ wrappers.
- Reuse existing Maude theory generation (`ppTheory :: MaudeSig -> ByteString`) in the first implementation.

## Target Architecture

### Current
- Tamarin spawns `maude` as a subprocess.
- Commands are sent over stdin.
- Results are parsed from stdout.
- `MaudeHandle` represents a subprocess.
- Some AC work is delayed because Maude is out-of-process.

### Target
- Tamarin links against embedded Maude library code.
- A handwritten C ABI shim exposes the needed operations to Haskell.
- One embedded Maude context is created per loaded theory.
- That context is attached to the Maude-backed signature.
- No subprocess is launched.
- No prompt/stdin/stdout protocol exists.

## Implementation Phases

### 1. Add Native Bridge
Build a minimal C ABI shim over `maude-bindings` that exposes:
- runtime initialization
- context creation from generated Maude theory text
- context destruction
- unification
- matching
- normalization
- variant generation
- version query
- error reporting
- optional stats

Rules:
- no C++ exceptions across the C ABI
- explicit ownership for contexts, results, and error values
- keep the shim narrow and value-oriented

### 2. Replace Process Backend
Replace the current implementation behind the Maude backend layer so it calls the native bridge instead of spawning `maude`.

This phase must remove:
- stdin/stdout transport
- prompt parsing
- subprocess restart logic
- executable path handling in the backend

`MaudeHandle` may remain temporarily, but it must become an embedded-context handle rather than a process handle.

### 3. Attach Embedded Context to Signatures
Update the Maude-backed signature representation so it stores the embedded Maude context for the loaded theory.

Requirements:
- preserve the current idea that Maude operations are relative to a loaded theory
- remove any requirement to store or recover a Maude executable path
- update binary/serialization behavior accordingly

### 4. Remove Delayed AC Execution
Refactor AC/C-backed operations so they execute directly against the embedded context instead of being delayed because Maude was external.

Important:
- keeping a theory-scoped context is acceptable
- delaying AC work due to transport is not

This primarily affects unification and any related normalization/variant paths that currently rely on deferred execution.

### 5. Remove External Binary Assumptions
Update CLI, build, docs, and packaging:
- remove `--with-maude`
- remove executable detection and install checks for `maude`
- replace version reporting with embedded library version reporting
- ship/build `libmaude` with Tamarin

## Expected Code Areas

### Haskell backend and term code
- `lib/term/src/Term/Maude/Process.hs`
- `lib/term/src/Term/Maude/Parser.hs`
- `lib/term/src/Term/Maude/Types.hs`
- `lib/term/src/Term/Unification.hs`
- `lib/term/src/Term/Rewriting/Norm.hs`
- `lib/term/src/Term/Narrowing/Variants/Compute.hs`

### Haskell signature and theory integration
- `lib/theory/src/Theory/Model/Signature.hs`
- theory-closing and preprocessing code that depends on Maude-backed normalization, matching, or variants

### Main/application integration
- `src/Main/Console.hs`
- `src/Main/Environment.hs`
- `src/Main/TheoryLoader.hs`
- any mode/test code assuming an external `maude` executable

### Native integration
Add new native bridge sources and build wiring for:
- C ABI header
- C/C++ shim implementation
- cabal/stack/native linking configuration

## Acceptance Criteria

The migration is complete when:
- Tamarin never launches a `maude` subprocess in normal operation.
- Tamarin never exchanges Maude data via stdin/stdout.
- Tamarin does not require a `maude` executable at runtime.
- One loaded theory corresponds to one stable embedded Maude context.
- AC unification is not delayed because of an external backend.
- Existing Maude-dependent regression tests still pass.
- Theory preprocessing and variant generation still work for DH, BP, XOR, multiset, and mixed signatures.

## Test Plan

### Native bridge tests
- initialize runtime
- create context from generated theory text
- unify representative equations
- match representative equations
- normalize representative terms
- compute variants
- verify repeated use of the same context
- verify cleanup and error handling

### Existing Haskell tests
Preserve and run tests for:
- unification
- matching
- normalization
- narrowing
- variants
- theory preprocessing
- intruder rule generation

### End-to-end regression
Run regression suites covering:
- DH
- BP
- XOR
- multiset
- mixed signatures
- theory loading
- closed theory generation
- proof search paths using normalization and variants

## Constraints

- Do not remove the theory-scoped Maude context in the first implementation.
- Do not consume SWIG-generated bindings directly from Haskell.
- Do not rewrite theory generation and backend transport simultaneously.
- First establish the native bridge seam, then replace the backend under existing abstractions.

## Deferred Follow-Ups

These are out of scope for the first migration:
- deciding whether `WithMaude` should be removed entirely
- renaming `SignatureWithMaude` for clarity
- supporting multiple active theory contexts
- replacing textual module generation with direct native module construction
