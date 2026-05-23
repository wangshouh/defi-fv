include "../common/ERC4626State.dfy"

module ERC4626GhostShareAccounting {
  import opened ERC4626State

  // Proof-only share ledger for the ERC20 shares minted and burned by ERC4626.
  //
  // OpenZeppelin mapping:
  // - ERC4626._deposit calls ERC20._mint(receiver, shares).
  // - ERC4626._withdraw calls ERC20._burn(owner, shares).
  //
  // This file verifies the share-source invariant for those share effects. It
  // deliberately does not prove whether a particular share issuance was fairly
  // priced by assets; that belongs to the price/backing property family.
  datatype ShareLedger = ShareLedger(
    issuedShares: nat,
    burnedShares: nat,
    accountedBalances: Balances
  )

  function AccountedSupply(g: ShareLedger): nat
    requires g.issuedShares >= g.burnedShares
  {
    g.issuedShares - g.burnedShares
  }

  predicate ShareSourceInvariant(s: VaultState, g: ShareLedger)
  {
    && ValidState(s)
    && g.issuedShares >= g.burnedShares
    && s.totalSupply == AccountedSupply(g)
  }

  predicate HolderShareSourceInvariant(s: VaultState, g: ShareLedger, holder: Address)
  {
    BalanceOf(s.balances, holder) == BalanceOf(g.accountedBalances, holder)
  }

  // Models the share effect of OpenZeppelin ERC20._mint as used by
  // ERC4626._deposit: real totalSupply and receiver balance increase, and the
  // ghost ledger records the same issuance.
  method AccountedMint(pre: VaultState, gpre: ShareLedger, recipient: Address, shares: nat)
      returns (post: VaultState, gpost: ShareLedger)
    requires ShareSourceInvariant(pre, gpre)
    requires HolderShareSourceInvariant(pre, gpre, recipient)
    ensures ShareSourceInvariant(post, gpost)
    ensures HolderShareSourceInvariant(post, gpost, recipient)
    ensures post.totalSupply == pre.totalSupply + shares
    ensures BalanceOf(post.balances, recipient) == BalanceOf(pre.balances, recipient) + shares
    ensures gpost.issuedShares == gpre.issuedShares + shares
    ensures gpost.burnedShares == gpre.burnedShares
  {
    post := VaultState(
      pre.totalAssets,
      pre.totalSupply + shares,
      pre.virtualShares,
      pre.balances[recipient := BalanceOf(pre.balances, recipient) + shares]
    );
    gpost := ShareLedger(
      gpre.issuedShares + shares,
      gpre.burnedShares,
      gpre.accountedBalances[recipient := BalanceOf(gpre.accountedBalances, recipient) + shares]
    );
  }

  // Models the share effect of OpenZeppelin ERC20._burn as used by
  // ERC4626._withdraw: real totalSupply and owner balance decrease, and the
  // ghost ledger records the same burn.
  method AccountedBurn(pre: VaultState, gpre: ShareLedger, owner: Address, shares: nat)
      returns (post: VaultState, gpost: ShareLedger)
    requires ShareSourceInvariant(pre, gpre)
    requires HolderShareSourceInvariant(pre, gpre, owner)
    requires shares <= pre.totalSupply
    requires shares <= BalanceOf(pre.balances, owner)
    ensures ShareSourceInvariant(post, gpost)
    ensures HolderShareSourceInvariant(post, gpost, owner)
    ensures post.totalSupply == pre.totalSupply - shares
    ensures BalanceOf(post.balances, owner) == BalanceOf(pre.balances, owner) - shares
    ensures gpost.issuedShares == gpre.issuedShares
    ensures gpost.burnedShares == gpre.burnedShares + shares
  {
    post := VaultState(
      pre.totalAssets,
      pre.totalSupply - shares,
      pre.virtualShares,
      pre.balances[owner := BalanceOf(pre.balances, owner) - shares]
    );
    gpost := ShareLedger(
      gpre.issuedShares,
      gpre.burnedShares + shares,
      gpre.accountedBalances[owner := BalanceOf(gpre.accountedBalances, owner) - shares]
    );
  }
}
