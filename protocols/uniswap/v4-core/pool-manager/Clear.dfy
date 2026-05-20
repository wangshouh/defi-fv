include "../common/V4CoreState.dfy"

module V4CoreClear {
  import opened V4CoreState

  method Clear(
    balancesBefore: Balances,
    deltasBefore: Deltas,
    sender: Address,
    currency: Currency,
    amount: nat
  ) returns (
    balancesAfter: Balances,
    deltasAfter: Deltas
  )
    requires currency < UINT160_MODULUS
    requires amount <= INT128_MAX
    requires BalanceDeltaOf(deltasBefore, sender, currency) == amount as int
    ensures balancesAfter == balancesBefore
    ensures BalanceDeltaOf(deltasAfter, sender, currency) == 0
    ensures deltasAfter == deltasBefore[(sender, currency) := 0]
  {
    balancesAfter := balancesBefore;
    deltasAfter := AccountDelta(deltasBefore, currency, sender, -(amount as int));
  }

  method ClearDoesNotSatisfyInv(
    balancesBefore: Balances,
    deltasBefore: Deltas,
    sender: Address,
    currency: Currency,
    amount: nat
  ) returns (
    balancesAfter: Balances,
    deltasAfter: Deltas
  )
    requires currency < UINT160_MODULUS
    requires amount > 0
    requires amount <= INT128_MAX
    requires BalanceDeltaOf(deltasBefore, sender, currency) == amount as int
    ensures balancesAfter == balancesBefore
    ensures BalanceDeltaOf(deltasAfter, sender, currency) == 0
    ensures !Inv(balancesBefore, deltasBefore, balancesAfter, deltasAfter, sender, sender, currency)
  {
    balancesAfter, deltasAfter := Clear(balancesBefore, deltasBefore, sender, currency, amount);
  }
}
