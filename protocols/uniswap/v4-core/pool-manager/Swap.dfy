include "../common/V4CoreState.dfy"
include "../hooks/AfterSwap.dfy"

module V4CoreSwap {
  import opened V4CoreState
  import V4CoreAfterSwap

  method Swap(
    balancesBefore: Balances,
    deltasBefore: Deltas,
    caller: Address,
    hook: Address,
    pool: Address,
    currency0: Currency,
    currency1: Currency,
    rawDelta0: int,
    rawDelta1: int,
    hookDelta0: int,
    hookDelta1: int
  ) returns (
    balancesAfter: Balances,
    deltasAfter: Deltas,
    callerDelta0: int,
    callerDelta1: int,
    tokenId0: TokenId,
    tokenId1: TokenId
  )
    requires caller != hook
    requires currency0 < currency1 < UINT160_MODULUS
    requires if -rawDelta0 >= 0
      then BalanceOf(balancesBefore, pool, ToId(currency0)) + (-rawDelta0) as nat <= UINT256_MAX
      else BalanceOf(balancesBefore, pool, ToId(currency0)) >= rawDelta0 as nat
    requires if -rawDelta1 >= 0
      then BalanceOf(balancesBefore, pool, ToId(currency1)) + (-rawDelta1) as nat <= UINT256_MAX
      else BalanceOf(balancesBefore, pool, ToId(currency1)) >= rawDelta1 as nat
    ensures tokenId0 == ToId(currency0)
    ensures tokenId1 == ToId(currency1)
    ensures callerDelta0 == rawDelta0 - hookDelta0
    ensures callerDelta1 == rawDelta1 - hookDelta1
    ensures CurrencyPairAccountingEffects(
      balancesBefore, deltasBefore, balancesAfter, deltasAfter,
      pool, hook, caller, currency0, currency1,
      -rawDelta0, -rawDelta1,
      hookDelta0, hookDelta1,
      callerDelta0, callerDelta1
    )
    ensures CurrencyPairBalanceTwoDeltasInv(
      balancesBefore, deltasBefore, balancesAfter, deltasAfter,
      pool, caller, hook, currency0, currency1
    )
  {
    tokenId0 := ToId(currency0);
    tokenId1 := ToId(currency1);

    callerDelta0 := rawDelta0 - hookDelta0;
    callerDelta1 := rawDelta1 - hookDelta1;

    var balancesAfter0 := ApplyBalanceDelta(balancesBefore, pool, tokenId0, -rawDelta0);
    balancesAfter := ApplyBalanceDelta(balancesAfter0, pool, tokenId1, -rawDelta1);

    var deltasAfterHook0 := AccountDelta(deltasBefore, currency0, hook, hookDelta0);
    var deltasAfterHook1 := AccountDelta(deltasAfterHook0, currency1, hook, hookDelta1);
    var deltasAfterCaller0 := AccountDelta(deltasAfterHook1, currency0, caller, callerDelta0);
    deltasAfter := AccountDelta(deltasAfterCaller0, currency1, caller, callerDelta1);
  }

  method SwapWithAfterSwap(
    balancesBefore: Balances,
    deltasBefore: Deltas,
    caller: Address,
    hook: Address,
    pool: Address,
    currency0: Currency,
    currency1: Currency,
    rawDelta0: int,
    rawDelta1: int,
    beforeSpecifiedDelta: int,
    beforeUnspecifiedDelta: int,
    afterSwapReturnDelta: int,
    exactIn: bool,
    zeroForOne: bool,
    hasAfterSwapFlag: bool,
    hasAfterSwapReturnsDeltaFlag: bool
  ) returns (
    balancesAfter: Balances,
    deltasAfter: Deltas,
    adjustedSwapDelta0: int,
    adjustedSwapDelta1: int,
    hookDelta0: int,
    hookDelta1: int,
    tokenId0: TokenId,
    tokenId1: TokenId
  )
    requires caller != hook
    requires hasAfterSwapReturnsDeltaFlag ==> hasAfterSwapFlag
    requires currency0 < currency1 < UINT160_MODULUS
    requires if -rawDelta0 >= 0
      then BalanceOf(balancesBefore, pool, ToId(currency0)) + (-rawDelta0) as nat <= UINT256_MAX
      else BalanceOf(balancesBefore, pool, ToId(currency0)) >= rawDelta0 as nat
    requires if -rawDelta1 >= 0
      then BalanceOf(balancesBefore, pool, ToId(currency1)) + (-rawDelta1) as nat <= UINT256_MAX
      else BalanceOf(balancesBefore, pool, ToId(currency1)) >= rawDelta1 as nat
    ensures tokenId0 == ToId(currency0)
    ensures tokenId1 == ToId(currency1)
    ensures hookDelta0 ==
      V4CoreAfterSwap.HookDelta0(
        exactIn,
        zeroForOne,
        beforeSpecifiedDelta,
        V4CoreAfterSwap.CombinedUnspecifiedDelta(
          beforeUnspecifiedDelta,
          hasAfterSwapFlag,
          hasAfterSwapReturnsDeltaFlag,
          afterSwapReturnDelta
        )
      )
    ensures hookDelta1 ==
      V4CoreAfterSwap.HookDelta1(
        exactIn,
        zeroForOne,
        beforeSpecifiedDelta,
        V4CoreAfterSwap.CombinedUnspecifiedDelta(
          beforeUnspecifiedDelta,
          hasAfterSwapFlag,
          hasAfterSwapReturnsDeltaFlag,
          afterSwapReturnDelta
        )
      )
    ensures adjustedSwapDelta0 == rawDelta0 - hookDelta0
    ensures adjustedSwapDelta1 == rawDelta1 - hookDelta1
    ensures CurrencyPairAccountingEffects(
      balancesBefore, deltasBefore, balancesAfter, deltasAfter,
      pool, hook, caller, currency0, currency1,
      -rawDelta0, -rawDelta1,
      hookDelta0, hookDelta1,
      adjustedSwapDelta0, adjustedSwapDelta1
    )
    ensures CurrencyPairBalanceTwoDeltasInv(
      balancesBefore, deltasBefore, balancesAfter, deltasAfter,
      pool, caller, hook, currency0, currency1
    )
  {
    var combinedUnspecifiedDelta: int;
    adjustedSwapDelta0, adjustedSwapDelta1, hookDelta0, hookDelta1, combinedUnspecifiedDelta :=
      V4CoreAfterSwap.AfterSwap(
        rawDelta0,
        rawDelta1,
        beforeSpecifiedDelta,
        beforeUnspecifiedDelta,
        afterSwapReturnDelta,
        exactIn,
        zeroForOne,
        false,
        hasAfterSwapFlag,
        hasAfterSwapReturnsDeltaFlag
      );

    var callerDelta0: int;
    var callerDelta1: int;
    balancesAfter, deltasAfter, callerDelta0, callerDelta1, tokenId0, tokenId1 :=
      Swap(
        balancesBefore,
        deltasBefore,
        caller,
        hook,
        pool,
        currency0,
        currency1,
        rawDelta0,
        rawDelta1,
        hookDelta0,
        hookDelta1
      );
  }

  method SwapSelfCall(
    balancesBefore: Balances,
    deltasBefore: Deltas,
    caller: Address,
    hook: Address,
    pool: Address,
    currency0: Currency,
    currency1: Currency,
    rawDelta0: int,
    rawDelta1: int
  ) returns (
    balancesAfter: Balances,
    deltasAfter: Deltas,
    tokenId0: TokenId,
    tokenId1: TokenId
  )
    requires caller == hook
    requires currency0 < currency1 < UINT160_MODULUS
    requires if -rawDelta0 >= 0
      then BalanceOf(balancesBefore, pool, ToId(currency0)) + (-rawDelta0) as nat <= UINT256_MAX
      else BalanceOf(balancesBefore, pool, ToId(currency0)) >= rawDelta0 as nat
    requires if -rawDelta1 >= 0
      then BalanceOf(balancesBefore, pool, ToId(currency1)) + (-rawDelta1) as nat <= UINT256_MAX
      else BalanceOf(balancesBefore, pool, ToId(currency1)) >= rawDelta1 as nat
    ensures tokenId0 == ToId(currency0)
    ensures tokenId1 == ToId(currency1)
    ensures CurrencyPairSingleOwnerAccountingEffects(
      balancesBefore, deltasBefore, balancesAfter, deltasAfter,
      pool, caller, currency0, currency1,
      -rawDelta0, -rawDelta1,
      rawDelta0, rawDelta1
    )
    ensures CurrencyPairInv(balancesBefore, deltasBefore, balancesAfter, deltasAfter, pool, caller, currency0, currency1)
  {
    tokenId0 := ToId(currency0);
    tokenId1 := ToId(currency1);

    var balancesAfter0 := ApplyBalanceDelta(balancesBefore, pool, tokenId0, -rawDelta0);
    balancesAfter := ApplyBalanceDelta(balancesAfter0, pool, tokenId1, -rawDelta1);

    var deltasAfter0 := AccountDelta(deltasBefore, currency0, caller, rawDelta0);
    deltasAfter := AccountDelta(deltasAfter0, currency1, caller, rawDelta1);
  }

  method SwapWithAfterSwapAnyCaller(
    balancesBefore: Balances,
    deltasBefore: Deltas,
    caller: Address,
    hook: Address,
    pool: Address,
    currency0: Currency,
    currency1: Currency,
    rawDelta0: int,
    rawDelta1: int,
    beforeSpecifiedDelta: int,
    beforeUnspecifiedDelta: int,
    afterSwapReturnDelta: int,
    exactIn: bool,
    zeroForOne: bool,
    hasAfterSwapFlag: bool,
    hasAfterSwapReturnsDeltaFlag: bool
  ) returns (
    balancesAfter: Balances,
    deltasAfter: Deltas,
    adjustedSwapDelta0: int,
    adjustedSwapDelta1: int,
    hookDelta0: int,
    hookDelta1: int,
    tokenId0: TokenId,
    tokenId1: TokenId
  )
    requires hasAfterSwapReturnsDeltaFlag ==> hasAfterSwapFlag
    requires currency0 < currency1 < UINT160_MODULUS
    requires if -rawDelta0 >= 0
      then BalanceOf(balancesBefore, pool, ToId(currency0)) + (-rawDelta0) as nat <= UINT256_MAX
      else BalanceOf(balancesBefore, pool, ToId(currency0)) >= rawDelta0 as nat
    requires if -rawDelta1 >= 0
      then BalanceOf(balancesBefore, pool, ToId(currency1)) + (-rawDelta1) as nat <= UINT256_MAX
      else BalanceOf(balancesBefore, pool, ToId(currency1)) >= rawDelta1 as nat
    ensures tokenId0 == ToId(currency0)
    ensures tokenId1 == ToId(currency1)
    ensures caller == hook ==> hookDelta0 == 0
    ensures caller == hook ==> hookDelta1 == 0
    ensures caller == hook ==> adjustedSwapDelta0 == rawDelta0
    ensures caller == hook ==> adjustedSwapDelta1 == rawDelta1
    ensures caller == hook ==>
      CurrencyPairInv(balancesBefore, deltasBefore, balancesAfter, deltasAfter, pool, caller, currency0, currency1)
    ensures caller != hook ==>
      CurrencyPairBalanceTwoDeltasInv(
        balancesBefore, deltasBefore, balancesAfter, deltasAfter,
        pool, caller, hook, currency0, currency1
      )
  {
    var combinedUnspecifiedDelta: int;
    adjustedSwapDelta0, adjustedSwapDelta1, hookDelta0, hookDelta1, combinedUnspecifiedDelta :=
      V4CoreAfterSwap.AfterSwap(
        rawDelta0,
        rawDelta1,
        beforeSpecifiedDelta,
        beforeUnspecifiedDelta,
        afterSwapReturnDelta,
        exactIn,
        zeroForOne,
        caller == hook,
        hasAfterSwapFlag,
        hasAfterSwapReturnsDeltaFlag
      );

    if caller == hook {
      balancesAfter, deltasAfter, tokenId0, tokenId1 :=
        SwapSelfCall(
          balancesBefore,
          deltasBefore,
          caller,
          hook,
          pool,
          currency0,
          currency1,
          rawDelta0,
          rawDelta1
        );
    } else {
      var callerDelta0: int;
      var callerDelta1: int;
      balancesAfter, deltasAfter, callerDelta0, callerDelta1, tokenId0, tokenId1 :=
        Swap(
          balancesBefore,
          deltasBefore,
          caller,
          hook,
          pool,
          currency0,
          currency1,
          rawDelta0,
          rawDelta1,
          hookDelta0,
          hookDelta1
        );
    }
  }
}
