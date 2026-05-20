include "V4CoreState.dfy"

module V4CoreTake {
  import opened V4CoreState

  method Take(
    balancesBefore: Balances,
    deltasBefore: Deltas,
    sender: Address,
    to: Address,
    currency: Currency,
    amount: nat
  ) returns (
    balancesAfter: Balances,
    deltasAfter: Deltas,
    tokenId: TokenId
  )
    requires currency < UINT160_MODULUS
    requires amount <= INT128_MAX
    requires BalanceOf(balancesBefore, to, ToId(currency)) + amount <= UINT256_MAX
    ensures tokenId == ToId(currency)
    ensures BalanceOf(balancesAfter, to, tokenId) ==
      BalanceOf(balancesBefore, to, tokenId) + amount
    ensures BalanceDeltaOf(deltasAfter, sender, currency) ==
      BalanceDeltaOf(deltasBefore, sender, currency) - amount as int
    ensures Inv(balancesBefore, deltasBefore, balancesAfter, deltasAfter, to, sender, currency)
  {
    tokenId := ToId(currency);

    deltasAfter := AccountDelta(deltasBefore, currency, sender, -(amount as int));
    balancesAfter := ExternalReceive(balancesBefore, to, tokenId, amount);
  }
}
