# v4-core Dafny Model Notes

This repository contains a hand-written Dafny model for selected accounting
properties of Uniswap v4-core `PoolManager`. The proof is not a Solidity-to-
Dafny translation. It has two parts:

1. A manual abstraction from Solidity code to Dafny state transitions.
2. Dafny proofs over those abstract transitions.

Dafny verifies the second part. The first part must be reviewed against the
Solidity implementation.

## Proof Goal

The main safety property is an accounting conservation property. For a tracked
token, a tracked balance and the corresponding transient balance delta should
move in opposite directions:

```text
trackedBalanceBefore + balanceDeltaBefore
==
trackedBalanceAfter  + balanceDeltaAfter
```

In Dafny this is represented by `Inv` in `common/V4CoreState.dfy`.

For functions over both pool currencies, `CurrencyPairInv` packages the two
single-currency invariants:

```text
CurrencyPairInv(..., currency0, currency1)
==
Inv(..., currency0) && Inv(..., currency1)
```

For `swap`, hook accounting introduces a second delta owner. The model uses
`CurrencyPairBalanceTwoDeltasInv`, which packages:

```text
poolTrackedBalance + callerDelta + hookDelta
```

for both pool currencies.

`CurrencyPairAccountingEffects` packages the repeated postconditions that say:

```text
pool tracked balance changes by a pair of signed deltas
delta owner 0 changes by a pair of signed deltas
delta owner 1 changes by a pair of signed deltas
```

`swap` and `modifyLiquidity` both use this predicate before proving the aggregate
conservation invariant.

`hooks/AfterSwap.dfy` models the hook delta composition inside `Hooks.afterSwap`:

```text
combinedUnspecifiedDelta =
  beforeUnspecifiedDelta
  + (hasAfterSwapFlag && hasAfterSwapReturnsDeltaFlag ? afterSwapReturnDelta : 0)
```

It then maps specified/unspecified deltas into `currency0`/`currency1` using
the same branch as Solidity:

```text
exactIn == zeroForOne
```

`hooks/AfterModifyLiquidity.dfy` models the hook delta composition inside
`Hooks.afterModifyLiquidity`, including the add/remove liquidity branch and
return-delta flags.

The meaning of `trackedBalance` depends on the function being modeled:

- For `mint` and `burn`, it is the ERC6909 claim balance.
- For `settle`, it is the payer's external token/native balance.
- For `take`, it is the receiver's external token/native balance.
- For `donate`, it is the pool-side accounted donation/fee balance.

This distinction is important. The same algebraic invariant is reused, but the
state component being observed is different.

## State Mapping

The shared model is defined in `common/V4CoreState.dfy`.

```text
Address
  Abstract address value.

Currency
  Abstract v4 Currency value. `FromId(id)` models `uint160(id)` truncation.

TokenId
  Abstract ERC6909 token id. `ToId(currency)` models `currency.toId()`.

Balances
  Map from `(Address, TokenId)` to `nat`.
  Depending on the proof, this can represent ERC6909 claim balances or external
  token/native balances.

Deltas
  Map from `(Address, Currency)` to `int`.
  Models `CurrencyDelta` transient storage.
```

## Solidity to Dafny Correspondence

### `PoolManager.mint`

Solidity:

```solidity
Currency currency = CurrencyLibrary.fromId(id);
_accountDelta(currency, -(amount.toInt128()), msg.sender);
_mint(to, currency.toId(), amount);
```

Dafny:

```text
pool-manager/Mint.dfy
  AccountDelta(..., -amount)
  ERC6909Mint(..., amount)
```

Proved effect:

```text
ERC6909 claim balance of `to`:     +amount
Balance delta of `msg.sender`:     -amount
```

Therefore `Inv` holds for `(to, msg.sender, currency)`.

### `PoolManager.burn`

Solidity:

```solidity
Currency currency = CurrencyLibrary.fromId(id);
_accountDelta(currency, amount.toInt128(), msg.sender);
_burnFrom(from, currency.toId(), amount);
```

Dafny:

```text
pool-manager/Burn.dfy
  AccountDelta(..., +amount)
  ERC6909Burn(..., amount)
```

Proved effect:

```text
ERC6909 claim balance of `from`:   -amount
Balance delta of `msg.sender`:     +amount
```

Therefore `Inv` holds for `(from, msg.sender, currency)`.

### `PoolManager.take`

Solidity:

```solidity
_accountDelta(currency, -(amount.toInt128()), msg.sender);
currency.transfer(to, amount);
```

Dafny:

```text
pool-manager/Take.dfy
  AccountDelta(..., -amount)
  ExternalReceive(..., amount)
```

Proved effect:

```text
External balance of `to`:          +amount
Balance delta of `msg.sender`:     -amount
```

Therefore `Inv` holds for `(to, msg.sender, currency)`.

### `PoolManager.donate`

Solidity:

```solidity
delta = pool.donate(amount0, amount1);
_accountPoolBalanceDelta(key, delta, msg.sender);
```

`Pool.donate` returns:

```solidity
toBalanceDelta(-(amount0.toInt128()), -(amount1.toInt128()))
```

and updates pool fee growth for the two currencies.

Dafny:

```text
pool-manager/Donate.dfy
  AccountDelta(currency0, ..., -amount0)
  AccountDelta(currency1, ..., -amount1)
  ExternalReceive(pool, currency0, amount0)
  ExternalReceive(pool, currency1, amount1)
```

The model abstracts the pool fee-growth update as a pool-side accounted balance
increase. It does not model the exact `feeGrowthGlobal{0,1}X128` arithmetic or
liquidity distribution.

Proved effect:

```text
Pool-side accounted balance for currency0:  +amount0
Balance delta of `msg.sender` currency0:    -amount0

Pool-side accounted balance for currency1:  +amount1
Balance delta of `msg.sender` currency1:    -amount1
```

Therefore `CurrencyPairInv` holds for the pool's two currencies.

### `PoolManager.swap`

Solidity:

```solidity
swapDelta = _swap(...);
(swapDelta, hookDelta) = key.hooks.afterSwap(..., swapDelta, ...);
if (hookDelta != ZERO_DELTA) {
  _accountPoolBalanceDelta(key, hookDelta, address(key.hooks));
}
_accountPoolBalanceDelta(key, swapDelta, msg.sender);
```

The hook library adjusts the caller's delta:

```solidity
swapDelta = swapDelta - hookDelta;
```

Dafny:

```text
hooks/AfterSwap.dfy
  combinedUnspecifiedDelta =
    beforeUnspecifiedDelta
    + optional afterSwapReturnDelta

  if exactIn == zeroForOne:
    hookDelta0 = beforeSpecifiedDelta
    hookDelta1 = combinedUnspecifiedDelta
  else:
    hookDelta0 = combinedUnspecifiedDelta
    hookDelta1 = beforeSpecifiedDelta

pool-manager/Swap.dfy
  rawDelta      models the delta returned by `_swap` before hook adjustment.
  hookDelta     is computed by `hooks/AfterSwap.dfy`.
  callerDelta   is defined as `rawDelta - hookDelta`.

  pool-side accounted balance changes by `-rawDelta`.
  hook balance delta changes by `+hookDelta`.
  caller balance delta changes by `+callerDelta`.
```

The proved aggregate relation is:

```text
poolTrackedBalance
+ callerBalanceDelta
+ hookBalanceDelta
```

is conserved for both `currency0` and `currency1`.

This is represented by `CurrencyPairBalanceTwoDeltasInv`.

`hooks/AfterSwap.dfy` also models the self-call early return:

```text
isSelfCall => hookDelta == 0 && adjustedSwapDelta == rawSwapDelta
```

`pool-manager/Swap.dfy` has separate proofs for the two cases:

```text
caller != hook:
  CurrencyPairBalanceTwoDeltasInv
  poolTrackedBalance + callerDelta + hookDelta

caller == hook:
  CurrencyPairInv
  poolTrackedBalance + callerDelta
```

This matches v4-core's self-call behavior: `Hooks.afterSwap` returns zero hook
delta on self-call, so PoolManager does not account hook delta separately.

The model does not prove the AMM swap math, price movement, protocol fee
calculation, or hook callback validity. Those are abstracted into the supplied
`rawDelta`, before-swap deltas, and after-swap return delta.

### `PoolManager.modifyLiquidity`

Solidity:

```solidity
(principalDelta, feesAccrued) = pool.modifyLiquidity(...);
callerDelta = principalDelta + feesAccrued;

(callerDelta, hookDelta) =
  key.hooks.afterModifyLiquidity(key, params, callerDelta, feesAccrued, hookData);

if (hookDelta != ZERO_DELTA) {
  _accountPoolBalanceDelta(key, hookDelta, address(key.hooks));
}

_accountPoolBalanceDelta(key, callerDelta, msg.sender);
```

Dafny:

```text
hooks/AfterModifyLiquidity.dfy
  hookDelta is selected from the add-liquidity or remove-liquidity hook return
  depending on `isAddLiquidity`.

  If the corresponding returns-delta flag is not set, hookDelta is zero.

pool-manager/ModifyLiquidity.dfy
  rawCallerDelta = principalDelta + feesAccrued
  adjustedCallerDelta = rawCallerDelta - hookDelta

  pool-side accounted balance changes by `-rawCallerDelta`.
  hook balance delta changes by `+hookDelta`.
  caller balance delta changes by `+adjustedCallerDelta`.
```

The proved aggregate relation is the same shape as swap:

```text
poolTrackedBalance
+ callerBalanceDelta
+ hookBalanceDelta
```

is conserved for both pool currencies.

This is represented by `CurrencyPairBalanceTwoDeltasInv`.

The model does not prove tick updates, position accounting, liquidity math,
fee-growth calculation, or exact principal/fee formulas. Those are abstracted
into the supplied `principalDelta` and `feesAccrued`.

### `PoolManager.clear`

Solidity:

```solidity
int256 current = currency.getDelta(msg.sender);
int128 amountDelta = amount.toInt128();
if (amountDelta != current) revert;
_accountDelta(currency, -(amountDelta), msg.sender);
```

Dafny:

```text
pool-manager/Clear.dfy
  Clear(...)
  ClearDoesNotSatisfyInv(...)
```

`clear` does not satisfy the current `Inv` for nonzero `amount`.

Reason:

```text
tracked balance: unchanged
delta:           amount -> 0
```

So:

```text
balance + amount != balance + 0
```

when `amount > 0`.

### `sync -> external transfer -> _settle`

Solidity:

```solidity
sync(currency):
  reservesBefore = currency.balanceOfSelf()

external transfer:
  user transfers token/native value to PoolManager

_settle(recipient):
  paid = reservesNow - reservesBefore
  _accountDelta(currency, paid.toInt128(), recipient)
```

Dafny:

```text
pool-manager/Settle.dfy
  One-step abstraction:
    ExternalPay(...)
    AccountDelta(..., +paid)
```

`pool-manager/Settle.dfy` is sufficient for the end-to-end accounting property if `paid` is
accepted as an environment-provided value.

The model does not currently prove how `paid` is derived from `sync` and
PoolManager reserves. That relationship is an environment assumption:

```text
paid = reservesNow - reservesBefore
```

## Preserved Solidity Details

The model intentionally preserves these details:

- `CurrencyLibrary.fromId(id)` truncation through `uint160(id)`.
- `Currency.toId()` mapping back to a token id.
- `amount.toInt128()` bounds through `amount <= INT128_MAX`.
- ERC6909 mint overflow precondition.
- ERC6909 burn underflow precondition.
- The sign direction of `_accountDelta`.
- `take` external receive amount as an explicit environment-provided transfer
  result.
- `donate` balance delta signs for both pool currencies.
- `swap` caller/hook delta split: `callerDelta = rawDelta - hookDelta`.
- `Hooks.afterSwap` specified/unspecified delta composition and mapping to
  `currency0`/`currency1`.
- `modifyLiquidity` caller/hook delta split:
  `adjustedCallerDelta = principalDelta + feesAccrued - hookDelta`.
- `Hooks.afterModifyLiquidity` add/remove branch and return-delta flag handling.
- `clear` exact-current-delta requirement.
- `settle` paid amount as an explicit environment-provided value.

## Abstracted Away Details

The model intentionally omits:

- Events.
- Gas behavior.
- Low-level assembly slot details.
- `NonzeroDeltaCount`.
- Access control beyond the modeled preconditions.
- `onlyWhenUnlocked`.
- Reverts other than those represented as `requires`.
- Hook callbacks and reentrancy behavior.
- ERC20 non-standard behavior and transfer failure modes.
- Native ETH call mechanics.
- Exact pool fee-growth arithmetic and liquidity distribution for `donate`.
- AMM swap math, price movement, protocol fee calculation, and hook callback
  response validity for `swap`.
- Tick updates, position accounting, liquidity math, fee-growth calculation,
  and exact principal/fee formulas for `modifyLiquidity`.
- Full pool math for swap and modify liquidity.

These omissions are acceptable only for the narrow accounting property currently
being proved.

## Preconditions and Their Sources

Some Dafny `requires` clauses correspond to Solidity checks or runtime behavior:

```text
amount <= INT128_MAX
  Models `amount.toInt128()`.

BalanceOf(...) + amount <= UINT256_MAX
  Models ERC6909 mint overflow safety.

BalanceOf(...) >= amount
  Models Solidity 0.8 checked subtraction in `_burn`.

BalanceDeltaOf(...) == amount
  Models `clear` requiring `amountDelta == current`.

currency0 < currency1 < UINT160_MODULUS
  Models the pool-key assumption that the two pool currencies are distinct and
  ordered.

caller != hook
  Used only by the non-self-call helper methods for swap and modify-liquidity
  hook accounting. It is not a Solidity external precondition. The any-caller
  wrappers branch on `caller == hook` and use the self-call proof.
```

Some `requires` clauses are environment assumptions:

```text
ExternalBalance(...) >= amount
  The payer has enough external token/native balance.

ExternalPay
  Represents a real token/native payment that reduced the payer's external
  balance before or during settlement. This is not an internal `_settle`
  operation.

ExternalReceive
  Represents a real token/native transfer from PoolManager to the receiver.
  The model tracks only the receiver's external balance increase, not the
  corresponding decrease in PoolManager's held balance.

paid
  Represents the amount observed by `_settle`, either `msg.value` for native
  settlement or `reservesNow - reservesBefore` for ERC20 settlement.
```

## Current Proof Boundary

The current proofs establish local or fixed-flow properties:

```text
pool-manager/Mint.dfy
  `mint` satisfies `Inv`.

pool-manager/Burn.dfy
  `burn` satisfies `Inv`.

pool-manager/Take.dfy
  `take` satisfies `Inv`.

pool-manager/Donate.dfy
  `donate` satisfies `CurrencyPairInv` under the pool-side accounted balance
  abstraction.

pool-manager/Swap.dfy
  `swap` satisfies `CurrencyPairBalanceTwoDeltasInv` under the abstraction that
  `_swap` returns `rawDelta`; hook delta composition is delegated to
  `hooks/AfterSwap.dfy`. The self-call path satisfies `CurrencyPairInv` because hook
  delta is zero and only caller delta is accounted.

hooks/AfterSwap.dfy
  `Hooks.afterSwap` delta composition and specified/unspecified-to-currency
  mapping are verified.

pool-manager/ModifyLiquidity.dfy
  `modifyLiquidity` satisfies `CurrencyPairBalanceTwoDeltasInv` under the
  abstraction that `pool.modifyLiquidity` returns `principalDelta` and
  `feesAccrued`; hook delta composition is delegated to
  `hooks/AfterModifyLiquidity.dfy`. The self-call path satisfies `CurrencyPairInv`
  because hook delta is zero and only caller delta is accounted.

hooks/AfterModifyLiquidity.dfy
  `Hooks.afterModifyLiquidity` add/remove branch selection and return-delta
  flag handling are verified.

pool-manager/Clear.dfy
  nonzero `clear` does not satisfy `Inv`.

pool-manager/Settle.dfy
  one-step settle abstraction satisfies `Inv`.
```

The current proofs do not establish:

- Bytecode-level correctness.
- Correctness for all v4-core functions.
- Safety for arbitrary legal call traces.
- Liveness, such as "a user who syncs will eventually settle".
- Correct behavior for arbitrary ERC20 implementations.

## Toward Arbitrary Call Sequences

To prove safety for arbitrary legal call sequences, the model should be extended
from fixed-flow postconditions to a transition-system proof:

```text
State
Action
Enabled(state, action)
Step(state, action, nextState)
GlobalInv(state)
```

Then prove:

```text
Init(state) => GlobalInv(state)
GlobalInv(state) && Enabled(state, action) && Step(state, action, nextState)
  => GlobalInv(nextState)
```

For v4-core, `GlobalInv` likely needs to include pending value held by
`PoolManager`, not only user balance and delta. Otherwise intermediate states
such as "external transfer has happened but settle has not yet been called" will
break a two-term invariant.

## Review Checklist

When adding a new modeled function:

1. Identify which Solidity state variables or external balances it changes.
2. Decide whether the tracked balance is ERC6909 claim balance, external user
   balance, PoolManager-held balance, or another component.
3. Preserve the sign direction of `_accountDelta`.
4. Convert Solidity checks and revert paths into Dafny `requires`.
5. Mark environment assumptions explicitly.
6. Decide whether the function preserves `Inv`, violates it, or requires a
   larger `GlobalInv`.
7. Add a correspondence note in this document.
