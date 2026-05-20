# DeFi Formal Verification Workspace

This repository is organized by protocol, version, and contract/module area.
The goal is to keep protocol-specific abstractions close to the proofs that use
them, while still making shared models easy to reuse inside one protocol.

## Directory Layout

```text
protocols/
  <protocol>/
    <version-or-package>/
      MODEL.md
      common/
        Shared Dafny state, predicates, and helper transitions.
      hooks/
        Hook-specific models and proofs.
      <contract-or-component>/
        Function-level proofs for a Solidity contract/component.
```

Current layout:

```text
protocols/
  uniswap/
    v4-core/
      MODEL.md
      common/
        V4CoreState.dfy
      hooks/
        AfterSwap.dfy
        AfterModifyLiquidity.dfy
      pool-manager/
        Mint.dfy
        Burn.dfy
        Take.dfy
        Settle.dfy
        Clear.dfy
        Donate.dfy
        Swap.dfy
        ModifyLiquidity.dfy
```

## Conventions

- Put protocol-wide types, state maps, invariants, and reusable accounting
  transitions in `common/`.
- Put hook return parsing, hook delta composition, and hook permission logic in
  `hooks/`.
- Put Solidity function-level proofs under the contract/component directory,
  such as `pool-manager/`.
- Keep a `MODEL.md` beside each protocol package to document the abstraction
  boundary between Solidity and Dafny.
- Prefer relative includes from function proofs:

```dafny
include "../common/V4CoreState.dfy"
include "../hooks/AfterSwap.dfy"
```

## Verification

Verify all Dafny files:

```bash
find protocols -name '*.dfy' -print0 | xargs -0 dafny verify
```

Verify one component:

```bash
dafny verify protocols/uniswap/v4-core/pool-manager/Swap.dfy
```

## Adding a New Protocol

Use the same shape:

```text
protocols/<protocol>/<version-or-package>/
  MODEL.md
  common/
  <contract-or-component>/
```

Start with the smallest reusable state model in `common/`, then add one
function-level proof at a time. Each proof should state which Solidity behavior
is modeled, which behavior is abstracted, and which assumptions are represented
as Dafny `requires`.
