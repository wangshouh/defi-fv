module V4CoreState {
  const UINT160_MODULUS: nat := 1461501637330902918203684832716283019655932542976
  const UINT256_MAX: nat := 115792089237316195423570985008687907853269984665640564039457584007913129639935
  const INT128_MAX: nat := 170141183460469231731687303715884105727

  type Address = nat
  type Currency = nat
  type TokenId = nat

  type BalanceKey = (Address, TokenId)
  type DeltaKey = (Address, Currency)

  type Balances = map<BalanceKey, nat>
  type Deltas = map<DeltaKey, int>

  function FromId(id: nat): Currency
  {
    id % UINT160_MODULUS
  }

  function ToId(currency: Currency): TokenId
    requires currency < UINT160_MODULUS
  {
    currency
  }

  function BalanceOf(balances: Balances, owner: Address, tokenId: TokenId): nat
  {
    var key := (owner, tokenId);
    if key in balances then balances[key] else 0
  }

  function BalanceDeltaOf(deltas: Deltas, owner: Address, currency: Currency): int
  {
    var key := (owner, currency);
    if key in deltas then deltas[key] else 0
  }

  predicate Inv(
    balancesBefore: Balances,
    deltasBefore: Deltas,
    balancesAfter: Balances,
    deltasAfter: Deltas,
    balanceOwner: Address,
    deltaOwner: Address,
    currency: Currency
  )
    requires currency < UINT160_MODULUS
  {
    BalanceOf(balancesBefore, balanceOwner, ToId(currency)) as int
      + BalanceDeltaOf(deltasBefore, deltaOwner, currency)
    ==
    BalanceOf(balancesAfter, balanceOwner, ToId(currency)) as int
      + BalanceDeltaOf(deltasAfter, deltaOwner, currency)
  }

  predicate CurrencyPairInv(
    balancesBefore: Balances,
    deltasBefore: Deltas,
    balancesAfter: Balances,
    deltasAfter: Deltas,
    balanceOwner: Address,
    deltaOwner: Address,
    currency0: Currency,
    currency1: Currency
  )
    requires currency0 < currency1 < UINT160_MODULUS
  {
    Inv(balancesBefore, deltasBefore, balancesAfter, deltasAfter, balanceOwner, deltaOwner, currency0)
    &&
    Inv(balancesBefore, deltasBefore, balancesAfter, deltasAfter, balanceOwner, deltaOwner, currency1)
  }

  predicate BalanceTwoDeltasInv(
    balancesBefore: Balances,
    deltasBefore: Deltas,
    balancesAfter: Balances,
    deltasAfter: Deltas,
    balanceOwner: Address,
    deltaOwner0: Address,
    deltaOwner1: Address,
    currency: Currency
  )
    requires currency < UINT160_MODULUS
  {
    BalanceOf(balancesBefore, balanceOwner, ToId(currency)) as int
      + BalanceDeltaOf(deltasBefore, deltaOwner0, currency)
      + BalanceDeltaOf(deltasBefore, deltaOwner1, currency)
    ==
    BalanceOf(balancesAfter, balanceOwner, ToId(currency)) as int
      + BalanceDeltaOf(deltasAfter, deltaOwner0, currency)
      + BalanceDeltaOf(deltasAfter, deltaOwner1, currency)
  }

  predicate CurrencyPairBalanceTwoDeltasInv(
    balancesBefore: Balances,
    deltasBefore: Deltas,
    balancesAfter: Balances,
    deltasAfter: Deltas,
    balanceOwner: Address,
    deltaOwner0: Address,
    deltaOwner1: Address,
    currency0: Currency,
    currency1: Currency
  )
    requires currency0 < currency1 < UINT160_MODULUS
  {
    BalanceTwoDeltasInv(
      balancesBefore, deltasBefore, balancesAfter, deltasAfter,
      balanceOwner, deltaOwner0, deltaOwner1, currency0
    )
    &&
    BalanceTwoDeltasInv(
      balancesBefore, deltasBefore, balancesAfter, deltasAfter,
      balanceOwner, deltaOwner0, deltaOwner1, currency1
    )
  }

  predicate CurrencyPairAccountingEffects(
    balancesBefore: Balances,
    deltasBefore: Deltas,
    balancesAfter: Balances,
    deltasAfter: Deltas,
    balanceOwner: Address,
    deltaOwner0: Address,
    deltaOwner1: Address,
    currency0: Currency,
    currency1: Currency,
    balanceDelta0: int,
    balanceDelta1: int,
    owner0Delta0: int,
    owner0Delta1: int,
    owner1Delta0: int,
    owner1Delta1: int
  )
    requires currency0 < currency1 < UINT160_MODULUS
  {
    BalanceOf(balancesAfter, balanceOwner, ToId(currency0)) as int ==
      BalanceOf(balancesBefore, balanceOwner, ToId(currency0)) as int + balanceDelta0
    &&
    BalanceOf(balancesAfter, balanceOwner, ToId(currency1)) as int ==
      BalanceOf(balancesBefore, balanceOwner, ToId(currency1)) as int + balanceDelta1
    &&
    BalanceDeltaOf(deltasAfter, deltaOwner0, currency0) ==
      BalanceDeltaOf(deltasBefore, deltaOwner0, currency0) + owner0Delta0
    &&
    BalanceDeltaOf(deltasAfter, deltaOwner0, currency1) ==
      BalanceDeltaOf(deltasBefore, deltaOwner0, currency1) + owner0Delta1
    &&
    BalanceDeltaOf(deltasAfter, deltaOwner1, currency0) ==
      BalanceDeltaOf(deltasBefore, deltaOwner1, currency0) + owner1Delta0
    &&
    BalanceDeltaOf(deltasAfter, deltaOwner1, currency1) ==
      BalanceDeltaOf(deltasBefore, deltaOwner1, currency1) + owner1Delta1
  }

  predicate CurrencyPairSingleOwnerAccountingEffects(
    balancesBefore: Balances,
    deltasBefore: Deltas,
    balancesAfter: Balances,
    deltasAfter: Deltas,
    balanceOwner: Address,
    deltaOwner: Address,
    currency0: Currency,
    currency1: Currency,
    balanceDelta0: int,
    balanceDelta1: int,
    ownerDelta0: int,
    ownerDelta1: int
  )
    requires currency0 < currency1 < UINT160_MODULUS
  {
    BalanceOf(balancesAfter, balanceOwner, ToId(currency0)) as int ==
      BalanceOf(balancesBefore, balanceOwner, ToId(currency0)) as int + balanceDelta0
    &&
    BalanceOf(balancesAfter, balanceOwner, ToId(currency1)) as int ==
      BalanceOf(balancesBefore, balanceOwner, ToId(currency1)) as int + balanceDelta1
    &&
    BalanceDeltaOf(deltasAfter, deltaOwner, currency0) ==
      BalanceDeltaOf(deltasBefore, deltaOwner, currency0) + ownerDelta0
    &&
    BalanceDeltaOf(deltasAfter, deltaOwner, currency1) ==
      BalanceDeltaOf(deltasBefore, deltaOwner, currency1) + ownerDelta1
  }

  method AccountDelta(
    deltasBefore: Deltas,
    currency: Currency,
    owner: Address,
    delta: int
  ) returns (deltasAfter: Deltas)
    requires currency < UINT160_MODULUS
    ensures BalanceDeltaOf(deltasAfter, owner, currency) ==
      BalanceDeltaOf(deltasBefore, owner, currency) + delta
    ensures deltasAfter == deltasBefore[(owner, currency) :=
      BalanceDeltaOf(deltasBefore, owner, currency) + delta]
  {
    deltasAfter := deltasBefore[(owner, currency) :=
      BalanceDeltaOf(deltasBefore, owner, currency) + delta];
  }

  method ERC6909Mint(
    balancesBefore: Balances,
    owner: Address,
    tokenId: TokenId,
    amount: nat
  ) returns (balancesAfter: Balances)
    requires tokenId < UINT160_MODULUS
    requires amount <= INT128_MAX
    requires BalanceOf(balancesBefore, owner, tokenId) + amount <= UINT256_MAX
    ensures BalanceOf(balancesAfter, owner, tokenId) ==
      BalanceOf(balancesBefore, owner, tokenId) + amount
    ensures balancesAfter == balancesBefore[(owner, tokenId) :=
      BalanceOf(balancesBefore, owner, tokenId) + amount]
  {
    balancesAfter := balancesBefore[(owner, tokenId) :=
      BalanceOf(balancesBefore, owner, tokenId) + amount];
  }

  method ERC6909Burn(
    balancesBefore: Balances,
    owner: Address,
    tokenId: TokenId,
    amount: nat
  ) returns (balancesAfter: Balances)
    requires tokenId < UINT160_MODULUS
    requires amount <= INT128_MAX
    requires BalanceOf(balancesBefore, owner, tokenId) >= amount
    ensures BalanceOf(balancesAfter, owner, tokenId) ==
      BalanceOf(balancesBefore, owner, tokenId) - amount
    ensures balancesAfter == balancesBefore[(owner, tokenId) :=
      BalanceOf(balancesBefore, owner, tokenId) - amount]
  {
    balancesAfter := balancesBefore[(owner, tokenId) :=
      BalanceOf(balancesBefore, owner, tokenId) - amount];
  }

  method ApplyBalanceDelta(
    balancesBefore: Balances,
    owner: Address,
    tokenId: TokenId,
    delta: int
  ) returns (balancesAfter: Balances)
    requires tokenId < UINT160_MODULUS
    requires if delta >= 0
      then BalanceOf(balancesBefore, owner, tokenId) + delta as nat <= UINT256_MAX
      else BalanceOf(balancesBefore, owner, tokenId) >= (-delta) as nat
    ensures BalanceOf(balancesAfter, owner, tokenId) as int ==
      BalanceOf(balancesBefore, owner, tokenId) as int + delta
    ensures if delta >= 0
      then balancesAfter == balancesBefore[(owner, tokenId) :=
        BalanceOf(balancesBefore, owner, tokenId) + delta as nat]
      else balancesAfter == balancesBefore[(owner, tokenId) :=
        BalanceOf(balancesBefore, owner, tokenId) - (-delta) as nat]
  {
    if delta >= 0 {
      balancesAfter := balancesBefore[(owner, tokenId) :=
        BalanceOf(balancesBefore, owner, tokenId) + delta as nat];
    } else {
      balancesAfter := balancesBefore[(owner, tokenId) :=
        BalanceOf(balancesBefore, owner, tokenId) - (-delta) as nat];
    }
  }

  method ExternalPay(
    balancesBefore: Balances,
    payer: Address,
    tokenId: TokenId,
    paid: nat
  ) returns (balancesAfter: Balances)
    requires tokenId < UINT160_MODULUS
    requires paid <= INT128_MAX
    requires BalanceOf(balancesBefore, payer, tokenId) >= paid
    ensures BalanceOf(balancesAfter, payer, tokenId) ==
      BalanceOf(balancesBefore, payer, tokenId) - paid
    ensures balancesAfter == balancesBefore[(payer, tokenId) :=
      BalanceOf(balancesBefore, payer, tokenId) - paid]
  {
    balancesAfter := balancesBefore[(payer, tokenId) :=
      BalanceOf(balancesBefore, payer, tokenId) - paid];
  }

  method ExternalReceive(
    balancesBefore: Balances,
    receiver: Address,
    tokenId: TokenId,
    amount: nat
  ) returns (balancesAfter: Balances)
    requires tokenId < UINT160_MODULUS
    requires amount <= INT128_MAX
    requires BalanceOf(balancesBefore, receiver, tokenId) + amount <= UINT256_MAX
    ensures BalanceOf(balancesAfter, receiver, tokenId) ==
      BalanceOf(balancesBefore, receiver, tokenId) + amount
    ensures balancesAfter == balancesBefore[(receiver, tokenId) :=
      BalanceOf(balancesBefore, receiver, tokenId) + amount]
  {
    balancesAfter := balancesBefore[(receiver, tokenId) :=
      BalanceOf(balancesBefore, receiver, tokenId) + amount];
  }
}
