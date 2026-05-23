include "../common/ERC4626State.dfy"

module ERC4626StaticRoundTrip {
  import opened ERC4626State

  lemma MulLeCancelRight(x: nat, y: nat, k: nat)
    requires k > 0
    requires x * k <= y * k
    ensures x <= y
  {
  }

  lemma MulLtSuccCancelRight(x: nat, y: nat, k: nat)
    requires k > 0
    requires x * k < (y + 1) * k
    ensures x <= y
  {
  }

  lemma PredMulLtCancelToLe(x: nat, y: nat, k: nat)
    requires k > 0
    requires x == 0 || (x - 1) * k < y * k
    ensures x <= y
  {
    if x == 0 {
    } else {
      assert (x - 1) * k < y * k;
      MulLtSuccCancelRight(x - 1, y - 1, k);
    }
  }

  lemma DepositRedeemNoProfit(assets: nat, s: VaultState)
    requires ValidState(s)
    ensures ToAssetsDown(ToSharesDown(assets, s), s) <= assets
  {
    var ea := EffectiveAssets(s);
    var es := EffectiveShares(s);
    var shares := ToSharesDown(assets, s);
    var redeemed := ToAssetsDown(shares, s);

    FloorMulDivBounds(assets, es, ea);
    FloorMulDivBounds(shares, ea, es);

    assert shares * ea <= assets * es;
    assert redeemed * es <= shares * ea;
    assert redeemed * es <= assets * es;
    MulLeCancelRight(redeemed, assets, es);
  }

  lemma RedeemDepositNoProfit(shares: nat, s: VaultState)
    requires ValidState(s)
    ensures ToSharesDown(ToAssetsDown(shares, s), s) <= shares
  {
    var ea := EffectiveAssets(s);
    var es := EffectiveShares(s);
    var assets := ToAssetsDown(shares, s);
    var reminted := ToSharesDown(assets, s);

    FloorMulDivBounds(shares, ea, es);
    FloorMulDivBounds(assets, es, ea);

    assert assets * es <= shares * ea;
    assert reminted * ea <= assets * es;
    assert reminted * ea <= shares * ea;
    MulLeCancelRight(reminted, shares, ea);
  }

  lemma WithdrawRedeemEquivalence(assets: nat, shares: nat, s: VaultState)
    requires ValidState(s)
    ensures ToSharesUp(assets, s) <= shares <==> assets <= ToAssetsDown(shares, s)
  {
    var ea := EffectiveAssets(s);
    var es := EffectiveShares(s);
    var neededShares := ToSharesUp(assets, s);
    var redeemableAssets := ToAssetsDown(shares, s);

    CeilMulDivBounds(assets, es, ea);
    FloorMulDivBounds(shares, ea, es);

    if neededShares <= shares {
      assert assets * es <= neededShares * ea;
      assert neededShares * ea <= shares * ea;
      assert assets * es <= shares * ea;
      assert shares * ea < (redeemableAssets + 1) * es;
      assert assets * es < (redeemableAssets + 1) * es;
      MulLtSuccCancelRight(assets, redeemableAssets, es);
    }

    if assets <= redeemableAssets {
      assert redeemableAssets * es <= shares * ea;
      assert assets * es <= redeemableAssets * es;
      assert assets * es <= shares * ea;
      assert neededShares == 0 || (neededShares - 1) * ea < assets * es;
      if neededShares != 0 {
        assert (neededShares - 1) * ea < shares * ea;
        PredMulLtCancelToLe(neededShares, shares, ea);
      }
    }
  }

  lemma MintDepositEquivalence(shares: nat, assets: nat, s: VaultState)
    requires ValidState(s)
    ensures ToAssetsUp(shares, s) <= assets <==> shares <= ToSharesDown(assets, s)
  {
    var ea := EffectiveAssets(s);
    var es := EffectiveShares(s);
    var neededAssets := ToAssetsUp(shares, s);
    var mintableShares := ToSharesDown(assets, s);

    CeilMulDivBounds(shares, ea, es);
    FloorMulDivBounds(assets, es, ea);

    if neededAssets <= assets {
      assert shares * ea <= neededAssets * es;
      assert neededAssets * es <= assets * es;
      assert shares * ea <= assets * es;
      assert assets * es < (mintableShares + 1) * ea;
      assert shares * ea < (mintableShares + 1) * ea;
      MulLtSuccCancelRight(shares, mintableShares, ea);
    }

    if shares <= mintableShares {
      assert mintableShares * ea <= assets * es;
      assert shares * ea <= mintableShares * ea;
      assert shares * ea <= assets * es;
      assert neededAssets == 0 || (neededAssets - 1) * es < shares * ea;
      if neededAssets != 0 {
        assert (neededAssets - 1) * es < assets * es;
        PredMulLtCancelToLe(neededAssets, assets, es);
      }
    }
  }

  lemma WithdrawRedeemCoversAssets(assets: nat, s: VaultState)
    requires ValidState(s)
    ensures assets <= ToAssetsDown(ToSharesUp(assets, s), s)
  {
    WithdrawRedeemEquivalence(assets, ToSharesUp(assets, s), s);
  }

  lemma MintDepositCoversShares(shares: nat, s: VaultState)
    requires ValidState(s)
    ensures shares <= ToSharesDown(ToAssetsUp(shares, s), s)
  {
    MintDepositEquivalence(shares, ToAssetsUp(shares, s), s);
  }
}
