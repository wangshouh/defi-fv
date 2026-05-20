include "../common/V4CoreState.dfy"

module V4CoreMint {
  import opened V4CoreState

  method Mint(
    balancesBefore: Balances,
    deltasBefore: Deltas,
    sender: Address,
    to: Address,
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
    requires BalanceOf(balancesBefore, to, ToId(FromId(id))) + amount <= UINT256_MAX
    ensures currency == FromId(id)
    ensures tokenId == ToId(currency)
    ensures BalanceOf(balancesAfter, to, tokenId) ==
      BalanceOf(balancesBefore, to, tokenId) + amount
    ensures BalanceDeltaOf(deltasAfter, sender, currency) ==
      BalanceDeltaOf(deltasBefore, sender, currency) - amount as int
    ensures Inv(balancesBefore, deltasBefore, balancesAfter, deltasAfter, to, sender, currency)
  {
    currency := FromId(id);
    tokenId := ToId(currency);

    deltasAfter := AccountDelta(deltasBefore, currency, sender, -(amount as int));
    balancesAfter := ERC6909Mint(balancesBefore, to, tokenId, amount);
  }
}
