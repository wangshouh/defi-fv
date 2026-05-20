module V4CoreAfterModifyLiquidity {
  function UsesAddHook(isAddLiquidity: bool): bool
  {
    isAddLiquidity
  }

  function AfterModifyLiquidityReturnDelta(
    isAddLiquidity: bool,
    hasAfterAddLiquidityFlag: bool,
    hasAfterAddLiquidityReturnsDeltaFlag: bool,
    hasAfterRemoveLiquidityFlag: bool,
    hasAfterRemoveLiquidityReturnsDeltaFlag: bool,
    addHookReturnDelta: int,
    removeHookReturnDelta: int
  ): int
  {
    if isAddLiquidity then
      if hasAfterAddLiquidityFlag && hasAfterAddLiquidityReturnsDeltaFlag then addHookReturnDelta else 0
    else
      if hasAfterRemoveLiquidityFlag && hasAfterRemoveLiquidityReturnsDeltaFlag then removeHookReturnDelta else 0
  }

  method AfterModifyLiquidity(
    rawCallerDelta0: int,
    rawCallerDelta1: int,
    addHookReturnDelta0: int,
    addHookReturnDelta1: int,
    removeHookReturnDelta0: int,
    removeHookReturnDelta1: int,
    isAddLiquidity: bool,
    isSelfCall: bool,
    hasAfterAddLiquidityFlag: bool,
    hasAfterAddLiquidityReturnsDeltaFlag: bool,
    hasAfterRemoveLiquidityFlag: bool,
    hasAfterRemoveLiquidityReturnsDeltaFlag: bool
  ) returns (
    adjustedCallerDelta0: int,
    adjustedCallerDelta1: int,
    hookDelta0: int,
    hookDelta1: int
  )
    requires hasAfterAddLiquidityReturnsDeltaFlag ==> hasAfterAddLiquidityFlag
    requires hasAfterRemoveLiquidityReturnsDeltaFlag ==> hasAfterRemoveLiquidityFlag
    ensures isSelfCall ==> hookDelta0 == 0
    ensures isSelfCall ==> hookDelta1 == 0
    ensures isSelfCall ==> adjustedCallerDelta0 == rawCallerDelta0
    ensures isSelfCall ==> adjustedCallerDelta1 == rawCallerDelta1
    ensures !isSelfCall ==> (hookDelta0 ==
      AfterModifyLiquidityReturnDelta(
        isAddLiquidity,
        hasAfterAddLiquidityFlag,
        hasAfterAddLiquidityReturnsDeltaFlag,
        hasAfterRemoveLiquidityFlag,
        hasAfterRemoveLiquidityReturnsDeltaFlag,
        addHookReturnDelta0,
        removeHookReturnDelta0
      ))
    ensures !isSelfCall ==> (hookDelta1 ==
      AfterModifyLiquidityReturnDelta(
        isAddLiquidity,
        hasAfterAddLiquidityFlag,
        hasAfterAddLiquidityReturnsDeltaFlag,
        hasAfterRemoveLiquidityFlag,
        hasAfterRemoveLiquidityReturnsDeltaFlag,
        addHookReturnDelta1,
        removeHookReturnDelta1
      ))
    ensures !isSelfCall ==> adjustedCallerDelta0 == rawCallerDelta0 - hookDelta0
    ensures !isSelfCall ==> adjustedCallerDelta1 == rawCallerDelta1 - hookDelta1
    ensures !isSelfCall && isAddLiquidity && hasAfterAddLiquidityFlag && hasAfterAddLiquidityReturnsDeltaFlag ==>
      hookDelta0 == addHookReturnDelta0
    ensures !isSelfCall && isAddLiquidity && hasAfterAddLiquidityFlag && hasAfterAddLiquidityReturnsDeltaFlag ==>
      hookDelta1 == addHookReturnDelta1
    ensures !isSelfCall && !isAddLiquidity && hasAfterRemoveLiquidityFlag && hasAfterRemoveLiquidityReturnsDeltaFlag ==>
      hookDelta0 == removeHookReturnDelta0
    ensures !isSelfCall && !isAddLiquidity && hasAfterRemoveLiquidityFlag && hasAfterRemoveLiquidityReturnsDeltaFlag ==>
      hookDelta1 == removeHookReturnDelta1
  {
    if isSelfCall {
      hookDelta0 := 0;
      hookDelta1 := 0;
      adjustedCallerDelta0 := rawCallerDelta0;
      adjustedCallerDelta1 := rawCallerDelta1;
    } else {
      hookDelta0 := AfterModifyLiquidityReturnDelta(
        isAddLiquidity,
        hasAfterAddLiquidityFlag,
        hasAfterAddLiquidityReturnsDeltaFlag,
        hasAfterRemoveLiquidityFlag,
        hasAfterRemoveLiquidityReturnsDeltaFlag,
        addHookReturnDelta0,
        removeHookReturnDelta0
      );
      hookDelta1 := AfterModifyLiquidityReturnDelta(
        isAddLiquidity,
        hasAfterAddLiquidityFlag,
        hasAfterAddLiquidityReturnsDeltaFlag,
        hasAfterRemoveLiquidityFlag,
        hasAfterRemoveLiquidityReturnsDeltaFlag,
        addHookReturnDelta1,
        removeHookReturnDelta1
      );
      adjustedCallerDelta0 := rawCallerDelta0 - hookDelta0;
      adjustedCallerDelta1 := rawCallerDelta1 - hookDelta1;
    }
  }
}
