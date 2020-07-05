(******************************************************************************)
(*                                                                            *)
(*                                  PHI                                       *)
(*                                                                            *)
(*   phi n = \sum_(i < n) 2 ^ troot n                                         *)
(*                                                                            *)
(*                                                                            *)
(******************************************************************************)

From mathcomp Require Import all_ssreflect.
From hanoi Require Import triangular.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition phi n := foldr (addn \o (fun i => 2 ^ troot i)) 0 (iota 0 n).

Notation "'ϕ' n" := (phi n) (format "'ϕ' n", at level 0).

Compute zip (iota 0 11) (map phi (iota 0 11)).

Lemma phiE n : phi n = \sum_(i < n) 2 ^ troot i.
Proof.
rewrite -(@big_mkord _ _ _ _ predT (fun i => 2 ^ (troot i))).
rewrite unlock /reducebig /phi.
by rewrite /index_iota subn0.
Qed.

Lemma phiS n : phi n.+1 = phi n + 2 ^ (troot n).
Proof. by rewrite !phiE big_ord_recr. Qed.

Lemma phi_le m n : m <= n -> phi m <= phi n.
Proof.
elim: n m => [[] //|n IH m].
rewrite leq_eqVlt => /orP[/eqP->//|/IH /leq_trans->//].
by rewrite phiS leq_addr.
Qed.

Lemma phi_gt0 n : (0 < phi n) = (0 < n).
Proof. by case: n. Qed.

Lemma phi_deltaD n p :
  p <= n.+1 -> phi (delta n + p) = 1 + (n + p) * 2 ^ n - 2 ^ n.
Proof.
elim: n p => [|n IHn]; first by case => // [] [|p].
elim => [_|p IHp pLn].
  rewrite !addn0 deltaS IHn // -addnBA; last first.
    by rewrite -[X in X <= _]mul1n leq_mul2r addnS orbT.
  rewrite -[X in _ + (_ - X)]mul1n -mulnBl addnS subn1 /=.
  rewrite addnn -muln2 -mulnA -expnS.
  rewrite -{1}[n]subn0 -subSS mulnBl mul1n addnBA //.
  by rewrite -[X in X <= _]mul1n leq_mul2r orbT.
rewrite addnS phiS IHp 1?ltnW //.
rewrite (_ : troot _ = n.+1).
  rewrite subnK.
    by rewrite addnS mulSn [X in _ = _ + X - _]addnC addnA addnK.
  by rewrite [_ + p]addSn mulSn addnC -addnA leq_addr.
by apply/eqP; rewrite trootE leq_addr [delta _.+2]deltaS ltn_add2l.
Qed.

Fact phi_simpl a n p q :
  0 < n -> a + (n + p) * 2 ^ q - 2 ^ q  = a + (n.-1 + p) * 2 ^ q.
Proof.
case: n => // n _.
rewrite -addnBA; last by rewrite addSn mulSn leq_addr.
by rewrite [_ + p]addSn mulSn [2 ^ _ + _]addnC addnK.
Qed.

Fact phi_simpr a n p q :
  0 < p -> a + (n + p) * 2 ^ q - 2 ^ q  = a + (n + p.-1) * 2 ^ q.
Proof. by move=> H; rewrite ![n + _]addnC phi_simpl. Qed.

Lemma phi_modE n : 
  phi n = 1 + (troot n + tmod n) * 2 ^ (troot n) - 2 ^ (troot n).
Proof. by rewrite {1}[n]tmodE phi_deltaD // ltnW // ltnS tmod_le. Qed.

Lemma phi_deltaE n : 
 phi (delta n) = 1 + n * 2 ^ n - 2 ^ n.
Proof. by rewrite phi_modE troot_delta tmod_delta addn0. Qed.

Lemma phi_modSE n : 
 phi n.+1 = 1 + (troot n + tmod n) * 2 ^ (troot n).
Proof.
rewrite phi_modE.
have /orP[/andP[/eqP-> /eqP->]|
          /and3P[/eqP->/eqP->/eqP]->] := troot_mod_case n.
  by rewrite addnS mulSn addnCA [2 ^ _ + _]addnC addnK.
rewrite addn0 mulSn addnCA [2 ^ _ + _]addnC addnK.
by rewrite expnS addnn -mul2n mulnCA mulnA.
Qed.

Lemma phi_odd n : odd (phi n) = (0 < n).
Proof.
case: n => // [] [|n] //.
rewrite phi_modSE oddD odd_mul odd_exp orbF.
case: troot (troot_gt0 (isT : 0 < n.+1)) => // k.
by rewrite andbF.
Qed.

Definition g n m := (phi m).*2 + (2 ^ (n - m)).-1.

Definition gmin n := delta (troot n).-1 + tmod n.

Lemma gmin_gt0 n : 1 < n -> 0 < gmin n.
Proof.
case: n => [|[|[|n _]]] //.
apply: leq_trans (leq_addr _ _).
have /troot_le : 3 <= n.+3 by [].
rewrite -[troot 3]/(2).
case: troot => //= m.
by rewrite ltnS => /delta_le.
Qed.

Lemma gminE n : n = gmin n + troot n.
Proof.
case: n => //= n.
rewrite {1}[n.+1]tmodE /gmin.
case: troot (troot_gt0 (isT : 0 < n.+1)) => //= t _.
by rewrite deltaS addnAC.
Qed.

Lemma gmin_le n : gmin n <= n.
Proof. by rewrite {2}[n]gminE leq_addr. Qed.

Lemma gmin_lt n : 0 < n -> gmin n < n.
Proof.
case: n => // n _.
rewrite {2}[n.+1]gminE -[X in X < _]addn0 ltn_add2l.
by apply: troot_gt0.
Qed.

Lemma gmin_root n : troot (gmin n) = troot n - (tmod n != troot n).
Proof.
have [/eqP mEt|mDt] := boolP (tmod n == troot n).
  rewrite /gmin -mEt subn0.
  by case: tmod => //= t; rewrite -deltaS troot_delta.
have mLt : tmod n < troot n by rewrite ltn_neqAle mDt tmod_le.
rewrite subn1.
apply/eqP; rewrite /gmin trootE.
case: n {mDt}mLt => // [] [|] // n mLt.
case: troot mLt => //= t mLt.
by rewrite leq_addr deltaS ltn_add2l.
Qed.

Lemma gmin_mod n : tmod (gmin n) = (tmod n != troot n) * tmod n.
Proof.
have [/eqP mEt|mDt] := boolP (tmod n == troot n).
  rewrite mul0n /gmin -mEt.
  case: (tmod n) => // t.
  by rewrite -deltaS tmod_delta.
have mLt : tmod n < troot n by rewrite ltn_neqAle mDt tmod_le.
by rewrite mul1n /tmod {1}/gmin gmin_root mDt subn1 addnC addnK.
Qed.

Lemma gmin_root_lt m n : m < gmin n -> troot m < troot n.
Proof.
move=> mLg.
have nP : 0 < n by case: n mLg.
case: leqP => //; rewrite leq_eqVlt => /orP[/eqP tnEtm| /ltn_root]; last first.
  by rewrite ltnNge (leq_trans _ (gmin_le _)) // ltnW.
have /eqP tnEtg : troot n == troot (gmin n).
  by rewrite eqn_leq {1}tnEtm !troot_le // ?gmin_le // ltnW.
have: tmod m < tmod (gmin n) by rewrite ltn_mod // -tnEtg.
suff : tmod (gmin n) = 0 by move->.
rewrite gmin_mod.
have := gmin_root n; case: eqP => //.
rewrite -tnEtg subn1 => _ F.
have := ltnn (troot n).
by rewrite -{2}(prednK (troot_gt0 nP)) -F leqnn.
Qed.
  
Lemma phi_gmin n : phi n = g n (gmin n).
Proof.
case: n => // n.
rewrite {1}phi_modE /g /gmin.
rewrite phi_deltaD; last by rewrite prednK // tmod_le.
set x := troot _; set y := tmod _.
rewrite phi_simpl //.
rewrite doubleB doubleD -!muln2 -!mulnA -!expnSr !prednK //.
have ->: n.+1 = delta x.-1 + x + y.
  by rewrite -{2}[x]prednK // -deltaS prednK // -tmodE.
rewrite [_ + x + y]addnAC [_ + x]addnC addnK.
rewrite {}/x {}/y.
case: n => // [] [|n] //.
rewrite phi_simpl //.
rewrite -[_.-1]prednK // addSn.
case: expn (expn_gt0 2 (troot n.+3)) => // u __.
by rewrite addSn mulSn add0n -addSn addnAC.
Qed.

Lemma gS n m : m.+1 < n -> g n m.+1 + 2 ^ (n - m.+1) = g n m + 2 ^ (troot m).+1.
Proof.
move=> H; rewrite /g !phi_modE.
rewrite phi_simpl; last by rewrite troot_gt0.
rewrite -[n - m]prednK; last first.
  by rewrite subn_gt0 (leq_trans _ H).
rewrite -subnS expnS mul2n -[(2 ^ _).*2]addnn.
have := troot_mod_case m.
case/orP=> [/andP[/eqP H1 /eqP H2]|/and3P[/eqP H1 /eqP H2 /eqP H3]].
  rewrite /g H1 H2 phi_simpl; last by rewrite -H1 troot_gt0.
  rewrite addnS mulSnr !addnA doubleD -!addnA; congr (_ + _).
  rewrite -mul2n -expnS addnC; congr (_ + _).
  by case: (_ ^ _).
rewrite H1 H2 H3 addnn addn0 /=.
set x := troot _; set y := n - _.
rewrite doubleB [in RHS]addnAC -[(2 ^ _).*2]mul2n -expnS subnK; last first.
  rewrite expnS mul2n leq_double.
  by case: x => //= x; rewrite doubleS mulSnr addnA leq_addl.
rewrite -[x.*2]muln2 -mulnA -expnS -addnA; congr (_ +_).
by case: expn (expn_gt0 2 y).
Qed.

Lemma gS_minl n m : m < gmin n -> g n m.+1 <= g n m.
Proof.
case: n => // n mLg.
have mLn : m < n.
   by rewrite -ltnS; apply: leq_trans (gmin_lt _).
suff mtLm : m.+1 + troot m <= n.
  rewrite -(leq_add2r (2 ^ (n.+1 - m.+1))) (gS _) //.
  by rewrite leq_add2l leq_pexp2l // ltn_subRL.
rewrite (leq_trans (_ : _ <= gmin n.+1 + troot m)) //.
  by rewrite leq_add2r.
rewrite -ltnS -addnS.
rewrite /gmin {3}[n.+1]tmodE addnAC leq_add2r.
have : 0 < troot n.+1 by apply troot_gt0.
case E : troot => [|t] _ //=.
rewrite deltaS -E leq_add2l.
by apply: gmin_root_lt.
Qed.

Lemma gS_minr n m : gmin n <= m -> m.+1 < n -> g n m <= g n m.+1.
Proof.
move=> gLm mLn.
suff mtLm : n <= m.+1 + (troot m).+1.
  rewrite -(leq_add2r (2 ^ (n - m.+1))) (gS _) //.
  by rewrite leq_add2l leq_pexp2l // leq_subLR.
rewrite [n]gminE addSnnS leq_add //.
apply: leq_trans (_ : (troot (gmin n)).+2 <= _).
  rewrite gmin_root; case: eqP; first by rewrite subn0 ltnW.
  by rewrite subn1; case: troot.
by rewrite !ltnS troot_le.
Qed.
 
Lemma gmin_min n m : m < n -> g n (gmin n) <= g n m.
Proof.
move=> mLn.
have [gLm|mLg] := leqP (gmin n) m.
  move: mLn; rewrite -(subnK gLm).
  elim: subn => // k IH H1.
  rewrite addSn (leq_trans (IH _) (gS_minr _ _)) ?leq_addl //.
  by apply: leq_trans H1; rewrite ltnS addSnnS leq_add2l.
rewrite -(subKn (ltnW mLg)).
elim: (gmin n - m) (leq_subr m (gmin n)) => [|k IH kLm].
  by rewrite subn0.
apply: leq_trans (IH (ltnW kLm)) _.
rewrite -subSS subSn //.
by rewrite gS_minl // -subSn // subSS leq_subr.
Qed.

(* This is (2.1) *)
Lemma phi_leD a b : phi (a + b) <= (phi a).*2 + (2 ^ b).-1.
Proof.
case: b => [|b]; first by rewrite !addn0 -addnn leq_addr.
rewrite phi_gmin -{3}[b.+1](addnK a _) [b.+1 + a]addnC.
apply: gmin_min.
by rewrite -addSnnS leq_addr.
Qed.
