include "../common/V4CoreState.dfy"
include "../hooks/AfterModifyLiquidity.dfy"

module V4CoreModifyLiquidity {
  import opened V4CoreState
  import V4CoreAfterModifyLiquidity

  method ModifyLiquidity(
    balancesBefore: Balances,
    deltasBefore: Deltas,
    caller: Address,
    hook: Address,
    pool: Address,
    currency0: Currency,
    currency1: Currency,
    principalDelta0: int,
    principalDelta1: int,
    feesAccrued0: int,
    feesAccrued1: int,
    hookDelta0: int,
    hookDelta1: int
  ) returns (
    balancesAfter: Balances,
    deltasAfter: Deltas,
    rawCallerDelta0: int,
    rawCallerDelta1: int,
    adjustedCallerDelta0: int,
    adjustedCallerDelta1: int,
    tokenId0: TokenId,
    tokenId1: TokenId
  )
    requires caller != hook
    requires currency0 < currency1 < UINT160_MODULUS
    requires if -(principalDelta0 + feesAccrued0) >= 0
      then BalanceOf(balancesBefore, pool, ToId(currency0)) + (-(principalDelta0 + feesAccrued0)) as nat <= UINT256_MAX
      else BalanceOf(balancesBefore, pool, ToId(currency0)) >= (principalDelta0 + feesAccrued0) as nat
    requires if -(principalDelta1 + feesAccrued1) >= 0
      then BalanceOf(balancesBefore, pool, ToId(currency1)) + (-(principalDelta1 + feesAccrued1)) as nat <= UINT256_MAX
      else BalanceOf(balancesBefore, pool, ToId(currency1)) >= (principalDelta1 + feesAccrued1) as nat
    ensures tokenId0 == ToId(currency0)
    ensures tokenId1 == ToId(currency1)
    ensures rawCallerDelta0 == principalDelta0 + feesAccrued0
    ensures rawCallerDelta1 == principalDelta1 + feesAccrued1
    ensures adjustedCallerDelta0 == rawCallerDelta0 - hookDelta0
    ensures adjustedCallerDelta1 == rawCallerDelta1 - hookDelta1
    ensures CurrencyPairAccountingEffects(
      balancesBefore, deltasBefore, balancesAfter, deltasAfter,
      pool, hook, caller, currency0, currency1,
      -rawCallerDelta0, -rawCallerDelta1,
      hookDelta0, hookDelta1,
      adjustedCallerDelta0, adjustedCallerDelta1
    )
    ensures CurrencyPairBalanceTwoDeltasInv(
      balancesBefore, deltasBefore, balancesAfter, deltasAfter,
      pool, caller, hook, currency0, currency1
    )
  {
    tokenId0 := ToId(currency0);
    tokenId1 := ToId(currency1);

    rawCallerDelta0 := principalDelta0 + feesAccrued0;
    rawCallerDelta1 := principalDelta1 + feesAccrued1;
    adjustedCallerDelta0 := rawCallerDelta0 - hookDelta0;
    adjustedCallerDelta1 := rawCallerDelta1 - hookDelta1;

    var balancesAfter0 := ApplyBalanceDelta(balancesBefore, pool, tokenId0, -rawCallerDelta0);
    balancesAfter := ApplyBalanceDelta(balancesAfter0, pool, tokenId1, -rawCallerDelta1);

    var deltasAfterHook0 := AccountDelta(deltasBefore, currency0, hook, hookDelta0);
    var deltasAfterHook1 := AccountDelta(deltasAfterHook0, currency1, hook, hookDelta1);
    var deltasAfterCaller0 := AccountDelta(deltasAfterHook1, currency0, caller, adjustedCallerDelta0);
    deltasAfter := AccountDelta(deltasAfterCaller0, currency1, caller, adjustedCallerDelta1);
  }

  method ModifyLiquidityWithAfterHook(
    balancesBefore: Balances,
    deltasBefore: Deltas,
    caller: Address,
    hook: Address,
    pool: Address,
    currency0: Currency,
    currency1: Currency,
    principalDelta0: int,
    principalDelta1: int,
    feesAccrued0: int,
    feesAccrued1: int,
    addHookReturnDelta0: int,
    addHookReturnDelta1: int,
    removeHookReturnDelta0: int,
    removeHookReturnDelta1: int,
    isAddLiquidity: bool,
    hasAfterAddLiquidityFlag: bool,
    hasAfterAddLiquidityReturnsDeltaFlag: bool,
    hasAfterRemoveLiquidityFlag: bool,
    hasAfterRemoveLiquidityReturnsDeltaFlag: bool
  ) returns (
    balancesAfter: Balances,
    deltasAfter: Deltas,
    rawCallerDelta0: int,
    rawCallerDelta1: int,
    adjustedCallerDelta0: int,
    adjustedCallerDelta1: int,
    hookDelta0: int,
    hookDelta1: int,
    tokenId0: TokenId,
    tokenId1: TokenId
  )
    requires caller != hook
    requires hasAfterAddLiquidityReturnsDeltaFlag ==> hasAfterAddLiquidityFlag
    requires hasAfterRemoveLiquidityReturnsDeltaFlag ==> hasAfterRemoveLiquidityFlag
    requires currency0 < currency1 < UINT160_MODULUS
    requires if -(principalDelta0 + feesAccrued0) >= 0
      then BalanceOf(balancesBefore, pool, ToId(currency0)) + (-(principalDelta0 + feesAccrued0)) as nat <= UINT256_MAX
      else BalanceOf(balancesBefore, pool, ToId(currency0)) >= (principalDelta0 + feesAccrued0) as nat
    requires if -(principalDelta1 + feesAccrued1) >= 0
      then BalanceOf(balancesBefore, pool, ToId(currency1)) + (-(principalDelta1 + feesAccrued1)) as nat <= UINT256_MAX
      else BalanceOf(balancesBefore, pool, ToId(currency1)) >= (principalDelta1 + feesAccrued1) as nat
    ensures tokenId0 == ToId(currency0)
    ensures tokenId1 == ToId(currency1)
    ensures rawCallerDelta0 == principalDelta0 + feesAccrued0
    ensures rawCallerDelta1 == principalDelta1 + feesAccrued1
    ensures adjustedCallerDelta0 == rawCallerDelta0 - hookDelta0
    ensures adjustedCallerDelta1 == rawCallerDelta1 - hookDelta1
    ensures CurrencyPairBalanceTwoDeltasInv(
      balancesBefore, deltasBefore, balancesAfter, deltasAfter,
      pool, caller, hook, currency0, currency1
    )
  {
    rawCallerDelta0 := principalDelta0 + feesAccrued0;
    rawCallerDelta1 := principalDelta1 + feesAccrued1;

    adjustedCallerDelta0, adjustedCallerDelta1, hookDelta0, hookDelta1 :=
      V4CoreAfterModifyLiquidity.AfterModifyLiquidity(
        rawCallerDelta0,
        rawCallerDelta1,
        addHookReturnDelta0,
        addHookReturnDelta1,
        removeHookReturnDelta0,
        removeHookReturnDelta1,
        isAddLiquidity,
        false,
        hasAfterAddLiquidityFlag,
        hasAfterAddLiquidityReturnsDeltaFlag,
        hasAfterRemoveLiquidityFlag,
        hasAfterRemoveLiquidityReturnsDeltaFlag
      );

    var rawCallerDelta0Check: int;
    var rawCallerDelta1Check: int;
    var adjustedCallerDelta0Check: int;
    var adjustedCallerDelta1Check: int;
    balancesAfter, deltasAfter, rawCallerDelta0Check, rawCallerDelta1Check,
      adjustedCallerDelta0Check, adjustedCallerDelta1Check, tokenId0, tokenId1 :=
      ModifyLiquidity(
        balancesBefore,
        deltasBefore,
        caller,
        hook,
        pool,
        currency0,
        currency1,
        principalDelta0,
        principalDelta1,
        feesAccrued0,
        feesAccrued1,
        hookDelta0,
        hookDelta1
      );
  }

  method ModifyLiquiditySelfCall(
    balancesBefore: Balances,
    deltasBefore: Deltas,
    caller: Address,
    hook: Address,
    pool: Address,
    currency0: Currency,
    currency1: Currency,
    principalDelta0: int,
    principalDelta1: int,
    feesAccrued0: int,
    feesAccrued1: int
  ) returns (
    balancesAfter: Balances,
    deltasAfter: Deltas,
    rawCallerDelta0: int,
    rawCallerDelta1: int,
    tokenId0: TokenId,
    tokenId1: TokenId
  )
    requires caller == hook
    requires currency0 < currency1 < UINT160_MODULUS
    requires if -(principalDelta0 + feesAccrued0) >= 0
      then BalanceOf(balancesBefore, pool, ToId(currency0)) + (-(principalDelta0 + feesAccrued0)) as nat <= UINT256_MAX
      else BalanceOf(balancesBefore, pool, ToId(currency0)) >= (principalDelta0 + feesAccrued0) as nat
    requires if -(principalDelta1 + feesAccrued1) >= 0
      then BalanceOf(balancesBefore, pool, ToId(currency1)) + (-(principalDelta1 + feesAccrued1)) as nat <= UINT256_MAX
      else BalanceOf(balancesBefore, pool, ToId(currency1)) >= (principalDelta1 + feesAccrued1) as nat
    ensures tokenId0 == ToId(currency0)
    ensures tokenId1 == ToId(currency1)
    ensures rawCallerDelta0 == principalDelta0 + feesAccrued0
    ensures rawCallerDelta1 == principalDelta1 + feesAccrued1
    ensures CurrencyPairSingleOwnerAccountingEffects(
      balancesBefore, deltasBefore, balancesAfter, deltasAfter,
      pool, caller, currency0, currency1,
      -rawCallerDelta0, -rawCallerDelta1,
      rawCallerDelta0, rawCallerDelta1
    )
    ensures CurrencyPairInv(balancesBefore, deltasBefore, balancesAfter, deltasAfter, pool, caller, currency0, currency1)
  {
    tokenId0 := ToId(currency0);
    tokenId1 := ToId(currency1);

    rawCallerDelta0 := principalDelta0 + feesAccrued0;
    rawCallerDelta1 := principalDelta1 + feesAccrued1;

    var balancesAfter0 := ApplyBalanceDelta(balancesBefore, pool, tokenId0, -rawCallerDelta0);
    balancesAfter := ApplyBalanceDelta(balancesAfter0, pool, tokenId1, -rawCallerDelta1);

    var deltasAfter0 := AccountDelta(deltasBefore, currency0, caller, rawCallerDelta0);
    deltasAfter := AccountDelta(deltasAfter0, currency1, caller, rawCallerDelta1);
  }

  method ModifyLiquidityWithAfterHookAnyCaller(
    balancesBefore: Balances,
    deltasBefore: Deltas,
    caller: Address,
    hook: Address,
    pool: Address,
    currency0: Currency,
    currency1: Currency,
    principalDelta0: int,
    principalDelta1: int,
    feesAccrued0: int,
    feesAccrued1: int,
    addHookReturnDelta0: int,
    addHookReturnDelta1: int,
    removeHookReturnDelta0: int,
    removeHookReturnDelta1: int,
    isAddLiquidity: bool,
    hasAfterAddLiquidityFlag: bool,
    hasAfterAddLiquidityReturnsDeltaFlag: bool,
    hasAfterRemoveLiquidityFlag: bool,
    hasAfterRemoveLiquidityReturnsDeltaFlag: bool
  ) returns (
    balancesAfter: Balances,
    deltasAfter: Deltas,
    rawCallerDelta0: int,
    rawCallerDelta1: int,
    adjustedCallerDelta0: int,
    adjustedCallerDelta1: int,
    hookDelta0: int,
    hookDelta1: int,
    tokenId0: TokenId,
    tokenId1: TokenId
  )
    requires hasAfterAddLiquidityReturnsDeltaFlag ==> hasAfterAddLiquidityFlag
    requires hasAfterRemoveLiquidityReturnsDeltaFlag ==> hasAfterRemoveLiquidityFlag
    requires currency0 < currency1 < UINT160_MODULUS
    requires if -(principalDelta0 + feesAccrued0) >= 0
      then BalanceOf(balancesBefore, pool, ToId(currency0)) + (-(principalDelta0 + feesAccrued0)) as nat <= UINT256_MAX
      else BalanceOf(balancesBefore, pool, ToId(currency0)) >= (principalDelta0 + feesAccrued0) as nat
    requires if -(principalDelta1 + feesAccrued1) >= 0
      then BalanceOf(balancesBefore, pool, ToId(currency1)) + (-(principalDelta1 + feesAccrued1)) as nat <= UINT256_MAX
      else BalanceOf(balancesBefore, pool, ToId(currency1)) >= (principalDelta1 + feesAccrued1) as nat
    ensures tokenId0 == ToId(currency0)
    ensures tokenId1 == ToId(currency1)
    ensures rawCallerDelta0 == principalDelta0 + feesAccrued0
    ensures rawCallerDelta1 == principalDelta1 + feesAccrued1
    ensures caller == hook ==> hookDelta0 == 0
    ensures caller == hook ==> hookDelta1 == 0
    ensures caller == hook ==> adjustedCallerDelta0 == rawCallerDelta0
    ensures caller == hook ==> adjustedCallerDelta1 == rawCallerDelta1
    ensures caller == hook ==>
      CurrencyPairInv(balancesBefore, deltasBefore, balancesAfter, deltasAfter, pool, caller, currency0, currency1)
    ensures caller != hook ==>
      CurrencyPairBalanceTwoDeltasInv(
        balancesBefore, deltasBefore, balancesAfter, deltasAfter,
        pool, caller, hook, currency0, currency1
      )
  {
    rawCallerDelta0 := principalDelta0 + feesAccrued0;
    rawCallerDelta1 := principalDelta1 + feesAccrued1;

    adjustedCallerDelta0, adjustedCallerDelta1, hookDelta0, hookDelta1 :=
      V4CoreAfterModifyLiquidity.AfterModifyLiquidity(
        rawCallerDelta0,
        rawCallerDelta1,
        addHookReturnDelta0,
        addHookReturnDelta1,
        removeHookReturnDelta0,
        removeHookReturnDelta1,
        isAddLiquidity,
        caller == hook,
        hasAfterAddLiquidityFlag,
        hasAfterAddLiquidityReturnsDeltaFlag,
        hasAfterRemoveLiquidityFlag,
        hasAfterRemoveLiquidityReturnsDeltaFlag
      );

    if caller == hook {
      balancesAfter, deltasAfter, rawCallerDelta0, rawCallerDelta1, tokenId0, tokenId1 :=
        ModifyLiquiditySelfCall(
          balancesBefore,
          deltasBefore,
          caller,
          hook,
          pool,
          currency0,
          currency1,
          principalDelta0,
          principalDelta1,
          feesAccrued0,
          feesAccrued1
        );
    } else {
      var rawCallerDelta0Check: int;
      var rawCallerDelta1Check: int;
      var adjustedCallerDelta0Check: int;
      var adjustedCallerDelta1Check: int;
      balancesAfter, deltasAfter, rawCallerDelta0Check, rawCallerDelta1Check,
        adjustedCallerDelta0Check, adjustedCallerDelta1Check, tokenId0, tokenId1 :=
        ModifyLiquidity(
          balancesBefore,
          deltasBefore,
          caller,
          hook,
          pool,
          currency0,
          currency1,
          principalDelta0,
          principalDelta1,
          feesAccrued0,
          feesAccrued1,
          hookDelta0,
          hookDelta1
        );
    }
  }
}
