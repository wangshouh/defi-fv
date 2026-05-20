include "V4CoreState.dfy"

module V4CoreBurn {
  import opened V4CoreState

  method Burn(
    balancesBefore: Balances,
    deltasBefore: Deltas,
    sender: Address,
    from: Address,
    id: nat,
    amount: nat
  ) returns (
    balancesAfter: Balances,
    deltasAfter: Deltas,
    currency: Currency,
    tokenId: TokenId
  )
    requires id <= UINT256_MAX
    requires amount <= INT128_MAX
    requires BalanceOf(balancesBefore, from, ToId(FromId(id))) >= amount
    ensures currency == FromId(id)
    ensures tokenId == ToId(currency)
    ensures BalanceOf(balancesAfter, from, tokenId) ==
      BalanceOf(balancesBefore, from, tokenId) - amount
    ensures BalanceDeltaOf(deltasAfter, sender, currency) ==
      BalanceDeltaOf(deltasBefore, sender, currency) + amount as int
    ensures Inv(balancesBefore, deltasBefore, balancesAfter, deltasAfter, from, sender, currency)
  {
    currency := FromId(id);
    tokenId := ToId(currency);

    deltasAfter := AccountDelta(deltasBefore, currency, sender, amount as int);
    balancesAfter := ERC6909Burn(balancesBefore, from, tokenId, amount);
  }
}
