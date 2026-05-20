include "../common/V4CoreState.dfy"

module V4CoreSettle {
  import opened V4CoreState

  method Settle(
    balancesBefore: Balances,
    deltasBefore: Deltas,
    payer: Address,
    recipient: Address,
    currency: Currency,
    paid: nat
  ) returns (
    balancesAfter: Balances,
    deltasAfter: Deltas,
    tokenId: TokenId
  )
    requires currency < UINT160_MODULUS
    requires paid <= INT128_MAX
    requires BalanceOf(balancesBefore, payer, ToId(currency)) >= paid
    ensures tokenId == ToId(currency)
    ensures BalanceOf(balancesAfter, payer, tokenId) ==
      BalanceOf(balancesBefore, payer, tokenId) - paid
    ensures BalanceDeltaOf(deltasAfter, recipient, currency) ==
      BalanceDeltaOf(deltasBefore, recipient, currency) + paid as int
    ensures Inv(balancesBefore, deltasBefore, balancesAfter, deltasAfter, payer, recipient, currency)
  {
    tokenId := ToId(currency);

    balancesAfter := ExternalPay(balancesBefore, payer, tokenId, paid);
    deltasAfter := AccountDelta(deltasBefore, currency, recipient, paid as int);
  }

  method SettleByRecipient(
    balancesBefore: Balances,
    deltasBefore: Deltas,
    recipient: Address,
    currency: Currency,
    paid: nat
  ) returns (
    balancesAfter: Balances,
    deltasAfter: Deltas,
    tokenId: TokenId
  )
    requires currency < UINT160_MODULUS
    requires paid <= INT128_MAX
    requires BalanceOf(balancesBefore, recipient, ToId(currency)) >= paid
    ensures tokenId == ToId(currency)
    ensures Inv(balancesBefore, deltasBefore, balancesAfter, deltasAfter, recipient, recipient, currency)
  {
    balancesAfter, deltasAfter, tokenId :=
      Settle(balancesBefore, deltasBefore, recipient, recipient, currency, paid);
  }
}
