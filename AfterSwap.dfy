module V4CoreAfterSwap {
  function AfterSwapReturnContribution(
    hasAfterSwapFlag: bool,
    hasAfterSwapReturnsDeltaFlag: bool,
    afterSwapReturnDelta: int
  ): int
  {
    if hasAfterSwapFlag && hasAfterSwapReturnsDeltaFlag then afterSwapReturnDelta else 0
  }

  function CombinedUnspecifiedDelta(
    beforeUnspecifiedDelta: int,
    hasAfterSwapFlag: bool,
    hasAfterSwapReturnsDeltaFlag: bool,
    afterSwapReturnDelta: int
  ): int
  {
    beforeUnspecifiedDelta
      + AfterSwapReturnContribution(hasAfterSwapFlag, hasAfterSwapReturnsDeltaFlag, afterSwapReturnDelta)
  }

  function HookDelta0(
    exactIn: bool,
    zeroForOne: bool,
    specifiedDelta: int,
    unspecifiedDelta: int
  ): int
  {
    if exactIn == zeroForOne then specifiedDelta else unspecifiedDelta
  }

  function HookDelta1(
    exactIn: bool,
    zeroForOne: bool,
    specifiedDelta: int,
    unspecifiedDelta: int
  ): int
  {
    if exactIn == zeroForOne then unspecifiedDelta else specifiedDelta
  }

  method AfterSwap(
    rawSwapDelta0: int,
    rawSwapDelta1: int,
    beforeSpecifiedDelta: int,
    beforeUnspecifiedDelta: int,
    afterSwapReturnDelta: int,
    exactIn: bool,
    zeroForOne: bool,
    isSelfCall: bool,
    hasAfterSwapFlag: bool,
    hasAfterSwapReturnsDeltaFlag: bool
  ) returns (
    adjustedSwapDelta0: int,
    adjustedSwapDelta1: int,
    hookDelta0: int,
    hookDelta1: int,
    combinedUnspecifiedDelta: int
  )
    requires hasAfterSwapReturnsDeltaFlag ==> hasAfterSwapFlag
    ensures isSelfCall ==> combinedUnspecifiedDelta == 0
    ensures isSelfCall ==> hookDelta0 == 0
    ensures isSelfCall ==> hookDelta1 == 0
    ensures isSelfCall ==> adjustedSwapDelta0 == rawSwapDelta0
    ensures isSelfCall ==> adjustedSwapDelta1 == rawSwapDelta1
    ensures !isSelfCall ==> (combinedUnspecifiedDelta ==
      CombinedUnspecifiedDelta(
        beforeUnspecifiedDelta,
        hasAfterSwapFlag,
        hasAfterSwapReturnsDeltaFlag,
        afterSwapReturnDelta
      ))
    ensures !isSelfCall ==> (hookDelta0 ==
      HookDelta0(exactIn, zeroForOne, beforeSpecifiedDelta, combinedUnspecifiedDelta)
    )
    ensures !isSelfCall ==> (hookDelta1 ==
      HookDelta1(exactIn, zeroForOne, beforeSpecifiedDelta, combinedUnspecifiedDelta)
    )
    ensures !isSelfCall ==> adjustedSwapDelta0 == rawSwapDelta0 - hookDelta0
    ensures !isSelfCall ==> adjustedSwapDelta1 == rawSwapDelta1 - hookDelta1
    ensures !isSelfCall && exactIn == zeroForOne ==> hookDelta0 == beforeSpecifiedDelta
    ensures !isSelfCall && exactIn == zeroForOne ==> hookDelta1 == combinedUnspecifiedDelta
    ensures !isSelfCall && exactIn != zeroForOne ==> hookDelta0 == combinedUnspecifiedDelta
    ensures !isSelfCall && exactIn != zeroForOne ==> hookDelta1 == beforeSpecifiedDelta
  {
    if isSelfCall {
      combinedUnspecifiedDelta := 0;
      hookDelta0 := 0;
      hookDelta1 := 0;
      adjustedSwapDelta0 := rawSwapDelta0;
      adjustedSwapDelta1 := rawSwapDelta1;
    } else {
      combinedUnspecifiedDelta := CombinedUnspecifiedDelta(
        beforeUnspecifiedDelta,
        hasAfterSwapFlag,
        hasAfterSwapReturnsDeltaFlag,
        afterSwapReturnDelta
      );
      hookDelta0 := HookDelta0(exactIn, zeroForOne, beforeSpecifiedDelta, combinedUnspecifiedDelta);
      hookDelta1 := HookDelta1(exactIn, zeroForOne, beforeSpecifiedDelta, combinedUnspecifiedDelta);
      adjustedSwapDelta0 := rawSwapDelta0 - hookDelta0;
      adjustedSwapDelta1 := rawSwapDelta1 - hookDelta1;
    }
  }
}
