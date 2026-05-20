include "V4CoreState.dfy"

module V4CoreDonate {
  import opened V4CoreState

  method Donate(
    balancesBefore: Balances,
    deltasBefore: Deltas,
    sender: Address,
    pool: Address,
    currency0: Currency,
    currency1: Currency,
    amount0: nat,
    amount1: nat
  ) returns (
    balancesAfter: Balances,
    deltasAfter: Deltas,
    tokenId0: TokenId,
    tokenId1: TokenId
  )
    requires currency0 < currency1 < UINT160_MODULUS
    requires amount0 <= INT128_MAX
    requires amount1 <= INT128_MAX
    requires BalanceOf(balancesBefore, pool, ToId(currency0)) + amount0 <= UINT256_MAX
    requires BalanceOf(balancesBefore, pool, ToId(currency1)) + amount1 <= UINT256_MAX
    ensures tokenId0 == ToId(currency0)
    ensures tokenId1 == ToId(currency1)
    ensures BalanceOf(balancesAfter, pool, tokenId0) ==
      BalanceOf(balancesBefore, pool, tokenId0) + amount0
    ensures BalanceOf(balancesAfter, pool, tokenId1) ==
      BalanceOf(balancesBefore, pool, tokenId1) + amount1
    ensures BalanceDeltaOf(deltasAfter, sender, currency0) ==
      BalanceDeltaOf(deltasBefore, sender, currency0) - amount0 as int
    ensures BalanceDeltaOf(deltasAfter, sender, currency1) ==
      BalanceDeltaOf(deltasBefore, sender, currency1) - amount1 as int
    ensures CurrencyPairInv(balancesBefore, deltasBefore, balancesAfter, deltasAfter, pool, sender, currency0, currency1)
  {
    tokenId0 := ToId(currency0);
    tokenId1 := ToId(currency1);

    var deltasAfter0 := AccountDelta(deltasBefore, currency0, sender, -(amount0 as int));
    deltasAfter := AccountDelta(deltasAfter0, currency1, sender, -(amount1 as int));

    var balancesAfter0 := ExternalReceive(balancesBefore, pool, tokenId0, amount0);
    balancesAfter := ExternalReceive(balancesAfter0, pool, tokenId1, amount1);
  }
}
