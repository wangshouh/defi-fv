module ERC4626State {
  type Address = nat

  type Balances = map<Address, nat>

  datatype VaultState = VaultState(
    totalAssets: nat,
    totalSupply: nat,
    virtualShares: nat,
    balances: Balances
  )

  function BalanceOf(balances: Balances, owner: Address): nat
  {
    if owner in balances then balances[owner] else 0
  }

  predicate ValidState(s: VaultState)
  {
    s.virtualShares > 0
  }

  function EffectiveAssets(s: VaultState): nat
  {
    s.totalAssets + 1
  }

  function EffectiveShares(s: VaultState): nat
  {
    s.totalSupply + s.virtualShares
  }

  function FloorMulDiv(x: nat, y: nat, denominator: nat): nat
    requires denominator > 0
  {
    x * y / denominator
  }

  function CeilDiv(x: nat, denominator: nat): nat
    requires denominator > 0
  {
    if x == 0 then 0 else (x - 1) / denominator + 1
  }

  function CeilMulDiv(x: nat, y: nat, denominator: nat): nat
    requires denominator > 0
  {
    CeilDiv(x * y, denominator)
  }

  lemma FloorMulDivBounds(x: nat, y: nat, denominator: nat)
    requires denominator > 0
    ensures FloorMulDiv(x, y, denominator) * denominator <= x * y
    ensures x * y < (FloorMulDiv(x, y, denominator) + 1) * denominator
  {
  }

  lemma CeilDivBounds(x: nat, denominator: nat)
    requires denominator > 0
    ensures x <= CeilDiv(x, denominator) * denominator
    ensures CeilDiv(x, denominator) == 0 || (CeilDiv(x, denominator) - 1) * denominator < x
  {
    if x == 0 {
    } else {
    }
  }

  lemma CeilMulDivBounds(x: nat, y: nat, denominator: nat)
    requires denominator > 0
    ensures x * y <= CeilMulDiv(x, y, denominator) * denominator
    ensures CeilMulDiv(x, y, denominator) == 0 ||
      (CeilMulDiv(x, y, denominator) - 1) * denominator < x * y
  {
    CeilDivBounds(x * y, denominator);
  }

  function ToSharesDown(assets: nat, s: VaultState): nat
    requires ValidState(s)
  {
    FloorMulDiv(assets, EffectiveShares(s), EffectiveAssets(s))
  }

  function ToSharesUp(assets: nat, s: VaultState): nat
    requires ValidState(s)
  {
    CeilMulDiv(assets, EffectiveShares(s), EffectiveAssets(s))
  }

  function ToAssetsDown(shares: nat, s: VaultState): nat
    requires ValidState(s)
  {
    FloorMulDiv(shares, EffectiveAssets(s), EffectiveShares(s))
  }

  function ToAssetsUp(shares: nat, s: VaultState): nat
    requires ValidState(s)
  {
    CeilMulDiv(shares, EffectiveAssets(s), EffectiveShares(s))
  }
}
