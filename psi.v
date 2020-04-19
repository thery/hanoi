
(******************************************************************************)
(*                                                                            *)
(*                                    PSI                                     *)
(*     psi n = the psi function                                               *)
(*                                                                            *)
(*                                                                            *)
(*                                                                            *)
(******************************************************************************)

From mathcomp Require Import all_ssreflect all_algebra.
Require Import triangular phi.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section PsiDef.

Variable N : nat.

Implicit Type e : {set 'I_N}.
Import GRing.Theory.
Import Num.Theory.

Definition psi_aux l e : int :=
  ((2 ^ l).-1 + (\sum_(i in e) 2 ^ (minn (troot i) l)))%:R - (l * 2 ^ l)%:R.

Notation "'ψ'' n" := (psi_aux n) (format "'ψ'' n", at level 0).

Lemma psi_aux_0_ge0 e :  (0 <= psi_aux 0 e)%R.
Proof. by rewrite /psi_aux add0n mul0n subr0 (ler_nat _ 0). Qed.

Lemma psi_aux_sub l e1 e2 : e1 \subset e2 -> (psi_aux l e1 <= psi_aux l e2)%R.
Proof.
move=> e1Se2.
apply: ler_sub => //.
rewrite ler_nat.
rewrite leq_add2l //.
rewrite [X in _ <= X](bigID (fun i => i \in e1)) /=.
rewrite (eq_bigl (fun i => (i \in e2) && (i \in e1))) ?leq_addr // => x.
have /subsetP /(_ x) := e1Se2.
do 2 case: (_ \in _)  => //.
by move=> /(_ isT).
Qed.

Lemma psi_auxE_le l e :
  psi_aux l e = 
   (((2 ^ l * #|[set i in e | (l <= troot i)%N]|.+1).-1 
    + (\sum_(i in e | (troot i < l)%N) 2 ^ troot i))%:R - (l * 2 ^ l)%:R)%R.
Proof.
rewrite /psi_aux.
congr (_%:R - _%:R)%R.
rewrite (bigID (fun i : 'I_ _ => l <= troot i)) /=.
rewrite (eq_bigr (fun i : 'I_ _ => 2 ^ l)); last first.
  by move=> i /andP[_ /minn_idPr->].
rewrite sum_nat_const.
rewrite (eq_bigr (fun i : 'I_ _ => 2 ^ (troot i))); last first.
  move=> i /andP[_ H].
  suff /minn_idPl-> : troot i <= l by [].
  by rewrite ltnW // ltnNge.
set c1 := #|_|; set c2 := #|_|.
have <- : c1 = c2.
  by apply: eq_card => i; rewrite -topredE !inE.
rewrite addnA; congr (_ + _).
  rewrite mulnS [_ ^ _ * c1]mulnC.
  by case: (2 ^ l) (expn_gt0 2 l).
by apply: eq_bigl => i; rewrite ltnNge.
Qed.

Lemma psi_auxE_lt l e :
  psi_aux l e =
   (((2 ^ l * #|[set i in e | (l < troot i)%N]|.+1).-1 
    + (\sum_(i in e | (troot i <= l)%N) 2 ^ troot i))%:R - (l * 2 ^ l)%:R)%R.
Proof.
rewrite /psi_aux.
congr (_%:R - _%:R)%R.
rewrite (bigID (fun i : 'I_ _ => l < troot i)) /=.
rewrite (eq_bigr (fun i : 'I_ _ => 2 ^ l)); last first.
  by move=> i /andP[_ /ltnW /minn_idPr->].
rewrite sum_nat_const.
rewrite (eq_bigr (fun i : 'I_ _ => 2 ^ (troot i))); last first.
  move=> i /andP[_ H].
  suff /minn_idPl-> : troot i <= l by [].
  by rewrite leqNgt.
set c1 := #|_|; set c2 := #|_|.
have <- : c1 = c2.
  by apply: eq_card => i; rewrite -topredE !inE.
rewrite addnA; congr (_ + _).
  rewrite mulnS [_ ^ _ * c1]mulnC.
  by case: (2 ^ l) (expn_gt0 2 l).
by apply: eq_bigl => i; rewrite -leqNgt.
Qed.

Definition psi_auxb e := (maxn #|e| (\max_(i in e) troot i)).+1.

Notation "'ψ_b' n" := (psi_auxb n) (format "'ψ_b' n", at level 0).

Lemma psi_aux_psib l e : psi_auxb e <= l -> (psi_aux l e <= 0)%R.
Proof.
rewrite /psi_auxb; case: l => // l.
rewrite ltnS /psi_aux geq_max => /andP[eLl maxLl].
rewrite mulSn -{2}[_ ^ _]prednK ?expn_gt0 // addSnnS.
rewrite !natrD [(_%:R + _)%R]addrC opprD addrA addrK.
rewrite subr_le0 ler_nat.
apply: leq_trans (leqnSn _).
apply: leq_trans (_ : #|e| * 2 ^ l.+1 <= _); last first.
  by rewrite leq_mul2r eLl orbT.
rewrite -sum_nat_const.
apply: leq_sum => i iIe.
apply: leq_pexp2l => //.
by apply geq_minr.
Qed.


Definition rnz (z : int) := `|Num.max 0%R z|.

Lemma rnz_ler0 z : (z <= 0)%R -> rnz z = 0.
Proof. by move=>  zN; rewrite /rnz maxr_l. Qed.

Lemma rnz_ger0 z : (0 <= z)%R -> (z = (rnz z)%:R)%R.
Proof.
by move=>  zP; rewrite /rnz maxr_r // natz gez0_abs.
Qed.

Lemma ler_rnz z : (z <= rnz z)%R.
Proof.
by rewrite /rnz; case: maxrP => // zP; rewrite gtz0_abs.
Qed.

Lemma rnz_ler z1 z2 : (z1 <= z2)%R -> rnz z1 <= rnz z2.
Proof.
(rewrite /rnz; (do 2 case: maxrP => //)) => [z2N z1P z1Lz2|z1P z2P].
  by have := ler_trans z1Lz2 z2N; rewrite lerNgt z1P.
by rewrite -{1}[z1]gtz0_abs // -{1}[z2]gtz0_abs.
Qed.

Definition psi e := \max_(l < psi_auxb e) rnz (psi_aux l e).

Notation "'ψ' n" := (psi n) (format "'ψ' n", at level 0).

Lemma psiE_leq e n :
  psi_auxb e <= n -> psi e = \max_(l < n) rnz (psi_aux l e).
Proof.
move=> pLn.
rewrite /psi.
rewrite (big_ord_widen_cond _ xpredT (fun i => rnz (psi_aux i e)) pLn).
rewrite [RHS](bigID (fun i : 'I_n => i < psi_auxb e)) /=.
rewrite [X in _ = maxn _ X]big1 ?maxn0 // => i.
rewrite -leqNgt => /psi_aux_psib.
exact: rnz_ler0.
Qed.

Lemma psi_max e l : (psi_aux l e <= (psi e)%:R)%R.
Proof.
pose n := maxn (psi_auxb e) l.+1.
have /psiE_leq-> : psi_auxb e <= n by apply: leq_maxl.
have O : l < n by apply: leq_maxr.
have [/ler_trans->//|/ltrW/rnz_ger0->] := lerP (psi_aux l e) 0.
  by rewrite (ler_nat _ 0).
rewrite ler_nat.
by rewrite (bigD1 (Ordinal O)) //= leq_maxl.
Qed.

Lemma psi_ler l e : 
  (((2 ^ l).-1 + \sum_(i in e) 2 ^ (minn (troot i) l))%:R - (l * 2 ^ l)%:R 
      <= ((psi e)%:R : int))%R.
Proof.
have [/psi_aux_psib/ler_trans->//|lLp] := leqP (psi_auxb e) l.
  by rewrite (ler_nat _ 0).
rewrite [X in (_ <= X%:R)%R](bigD1 (Ordinal lLp)) //=.
apply: ler_trans (ler_rnz _) _.
rewrite -natz ler_nat.
apply: leq_maxl.
Qed.

Lemma psiE e :  {l | ((psi e)%:R = psi_aux l e)%R}.
Proof.
have [l] :  {l : 'I_(psi_auxb e) | psi e = rnz (psi_aux l e)}.
  apply: eq_bigmax.
  by rewrite card_ord.
rewrite /rnz.
case: maxrP => [pG pE|pP ->]; last by exists l; rewrite natz gtz0_abs.
by exists 0; apply/eqP; rewrite eqr_le {1}pE psi_aux_0_ge0 psi_max.
Qed.

Lemma psi_sub e1 e2 : e1 \subset e2 -> psi e1 <= psi e2.
Proof.
move=> e1Se2.
rewrite (psiE_leq (leq_maxl (psi_auxb e1) (psi_auxb e2))).
rewrite (psiE_leq (leq_maxl (psi_auxb e2) (psi_auxb e1))).
rewrite maxnC.
elim/big_ind2: _ => // [x1 x2 y1 y2 x2Lx1 y2Ly1 | i _].
  rewrite geq_max (leq_trans x2Lx1 (leq_maxl _ _)).
  by rewrite  (leq_trans y2Ly1 (leq_maxr _ _)).
apply: rnz_ler.
by apply: psi_aux_sub.
Qed.

Lemma psi_aux_le_psi e1 e2 :
  (forall l, (psi_aux l e1 <= psi_aux l e2)%R) -> psi e1 <= psi e2.
Proof.
move=> H.
pose e := maxn (psi_auxb e1) (psi_auxb e2).
rewrite (psiE_leq (leq_maxl _ _ : _ <= e)).
rewrite (psiE_leq (leq_maxr _ _ : _ <= e)).
elim: e => [|e IH]; first by rewrite !big_ord0.
by rewrite !big_ord_recr /= geq_max !leq_max IH /= rnz_ler // orbT.
Qed.

Definition sint a b : {set 'I_N} := [set e : 'I_ _ | a <= e < b].

Lemma sint_minn a b :
   (sint a b) = (sint a (minn b N)).
Proof.
by apply/setP=> i; rewrite !inE leq_min ltn_ord andbT.
Qed.

Lemma sint_sub a b c : a <= c ->
   [set i in  (sint a b) | c <= i] = sint c b.
Proof.
move=> aLc.
apply/setP => i.
rewrite !inE andbC.
by have [/(leq_trans aLc)->|_] := boolP (c <= i).
Qed.

Lemma card_sint a b : b <= N -> #|sint a b| = (b - a).
Proof.
elim: b => // [_|b IH bLN].
  rewrite sub0n.
  by apply: eq_card0 => i; rewrite !inE ltn0 andbF.
have [aLb|bLa] := leqP a b; last first.
  rewrite (_ : _ - _ =  0); last first.
    by apply/eqP; rewrite subn_eq0.
  apply: eq_card0 => i; rewrite !inE.
  case: (leqP a i) => // /(leq_trans bLa).
  by rewrite leqNgt => /negPf->.
rewrite (cardD1 (Ordinal bLN)) !inE /= aLb leqnn /= subSn //.
rewrite add1n -IH; last by rewrite ltnW.
congr (_.+1).
apply: eq_card => i.
by rewrite !inE /= ltnS [i < _]ltn_neqAle andbCA.
Qed.

Notation "`[ n ]" := (sint 0 n) (format "`[ n ]").

Lemma sint0_set0 : `[0] = set0.
Proof. by apply/setP=> i; rewrite inE. Qed.

Lemma psi_auxb_sint n : psi_auxb `[n] = (minn n N).+1.
Proof.
congr (_.+1).
rewrite sint_minn /psi_auxb.
rewrite card_sint ?geq_minr // subn0.
apply/eqP.
rewrite eqn_leq leq_maxl andbT geq_max leqnn andTb.
apply/bigmax_leqP => i.
rewrite inE andTb => iLm.
apply: leq_trans iLm.
by apply: leq_trans (leq_rootnn _) _.
Qed.

Lemma psi_aux_sintE n : 
  n <= N ->
  forall l, psi_aux l `[n] = 
  (((2 ^ l).-1 + \sum_(0 <= i <  n) 2 ^ minn (∇i) l)%:R -
   (l * 2 ^ l)%:R)%R.
Proof.
move=> nLN l.
congr ((_ + _)%:R - _%:R)%R.
rewrite big_mkord.
rewrite (big_ord_widen _ (fun i => 2 ^ minn (∇i) l)  nLN).
by apply: eq_bigl => i; rewrite !inE.
Qed.

Lemma psi_auxb_set0 : psi_auxb set0 = 1.
Proof.
by rewrite /psi_auxb cards0 max0n big1 // => i; rewrite inE.
Qed.

Lemma  psi_set0 : psi set0 = 0.
Proof.
rewrite /psi psi_auxb_set0.
rewrite !big_ord_recr /= big_ord0 /= max0n.
rewrite /psi_aux /= big1 // => i.
by rewrite !inE.
Qed.

Lemma psi_eq0 e : (psi e == 0) = (e == set0).
Proof.
have [->|[x]] := set_0Vmem e; first by rewrite psi_set0 !eqxx.
have [->|_] := e =P set0; first by rewrite inE.
move=> xIe.
suff : psi e > 0 by case: psi.
rewrite -(ltr_nat int_numDomainType).
apply: ltr_le_trans (psi_max _ 0).
by rewrite /psi_aux add0n subr0 ltr_nat (bigD1 x).
Qed.

Lemma  psi_sint0 : psi `[0] = 0.
Proof. by rewrite sint0_set0 psi_set0. Qed.

Lemma  psi_sint1 : 0 < N -> psi `[1] = 1.
Proof.
move=> nLN.
rewrite /psi psi_auxb_sint (minn_idPl nLN).
rewrite -(big_mkord xpredT (fun l => rnz (psi_aux l _))).
pose f l := 
    rnz (((2 ^ l).-1 + \sum_(0 <= i <  1) 2 ^ minn (∇i) l)%:R -
         (l * 2 ^ l)%:R).
rewrite (eq_bigr f) => [|i _]; last by rewrite psi_aux_sintE.
by rewrite /f /= unlock.
Qed.

Lemma  psi_sint2 : 1 < N -> psi `[2] = 2.
Proof.
move=> nLN.
rewrite /psi psi_auxb_sint (minn_idPl nLN).
rewrite -(big_mkord xpredT (fun l => rnz (psi_aux l _))).
pose f l := 
    rnz (((2 ^ l).-1 + \sum_(0 <= i <  2) 2 ^ minn (∇i) l)%:R -
         (l * 2 ^ l)%:R).
rewrite (eq_bigr f) => [|i _]; last by rewrite psi_aux_sintE.
by rewrite /f /= unlock.
Qed.

Lemma  psi_sint3 : 2 < N -> psi `[3] = 4.
Proof.
move=> nLN.
rewrite /psi psi_auxb_sint (minn_idPl nLN).
rewrite -(big_mkord xpredT (fun l => rnz (psi_aux l _))).
pose f l := 
    rnz (((2 ^ l).-1 + \sum_(0 <= i <  3) 2 ^ minn (∇i) l)%:R -
         (l * 2 ^ l)%:R).
rewrite (eq_bigr f) => [|i _]; last by rewrite psi_aux_sintE.
by rewrite /f /= unlock.
Qed.

Lemma psi_aux_incr n l : n <= N ->
  l < (troot n).-1 -> (psi_aux l `[n] <= psi_aux l.+1 `[n])%R.
Proof.
move=> nLN lLr.
have dlLn : delta l.+2 <= n.
  rewrite -root_delta_le -subn_gt0.
  by rewrite -[l.+1]addn1 addnC subnDA subn_gt0 subn1.
rewrite psi_auxE_lt psi_auxE_le.
set s := \sum_(_ in _ | _) _.
have /eq_card-> : [set i in `[n] | l < troot i] =i 
                  [set i in `[n] | delta l.+1 <= i].
  by move=> i; rewrite !inE root_delta_le.
have /(sint_sub n)-> : 0 <= delta l.+1 by apply: delta_le (_ : 0 <= l.+1).
rewrite card_sint //.
set c := n - _.
rewrite expnS mulnAC [2 * _ * _]mulnC.
rewrite mul2n mulnA muln2 -!addnn -[_ + l.+1]addSnnS.
rewrite mulnDl mulnDr prednDr ?(muln_gt0, expn_gt0) //.
set x := 2 ^ _ * _.
rewrite -[_ + _ + s]addnA [x + _]addnC.
rewrite [((_ + _ * _)%:R)%R]natrD opprD addrA ler_sub //.
rewrite ler_subr_addr [((_ + x)%:R)%R]natrD ler_add //.
rewrite ler_nat.
rewrite mulnC leq_mul2l.
rewrite -subSn; last first.
  apply: leq_trans (_ : delta l.+2 <= _); first by by apply: delta_le.
  by apply: leq_trans dlLn _.
by rewrite ltn_subRL -addnS -deltaS (leq_trans dlLn) ?orbT.
Qed.

Lemma psi_aux_decr n l : n <= N ->
  (troot n).-1 <= l -> (psi_aux l.+1 `[n] <= psi_aux l `[n])%R.
Proof.
move=> nLN rLl.
have dlLn : n < delta l.+2.
  rewrite ltnNge -root_delta_le -subn_gt0.
  by rewrite -[l.+1]addn1 addnC subnDA subn_gt0 subn1 -ltnNge.
rewrite psi_auxE_le.
rewrite psi_auxE_lt.
set s := \sum_(_ in _ | _) _.
have /eq_card-> : [set i in `[n] | l < troot i] =i 
                  [set i in `[n] | delta l.+1 <= i].
  by move=> i; rewrite !inE root_delta_le.
have /(sint_sub n)-> : 0 <= delta l.+1 by apply: delta_le (_ : 0 <= l.+1).
rewrite card_sint //.
set c := n - _.
rewrite expnS mulnAC [2 * _ * _]mulnC.
rewrite mul2n mulnA muln2 -!addnn -[_ + l.+1]addSnnS.
rewrite mulnDl mulnDr prednDr ?(muln_gt0, expn_gt0) //.
set x := 2 ^ _ * _. 
rewrite -[_ + s]addnA [x + _]addnC.
rewrite [((_ + _ * _)%:R)%R]natrD opprD addrA ler_sub //.
rewrite ler_subl_addr [((_ + x)%:R)%R]natrD ler_add //.
rewrite ler_nat.
rewrite mulnC leq_mul2l.
rewrite -[l.+2](addnK (delta l.+1)) addnC -deltaS.
rewrite ltn_sub2r ?orbT // [X in _ < X]deltaS //.
by rewrite addnS ltnS leq_addr.
Qed.

Lemma psi_aux_sint n : n <= N  ->
   ((psi `[n])%:R)%R = psi_aux (troot n).-1 `[n].
Proof.
move=> nLN.
apply/eqP.
rewrite eqr_le psi_max andbT.
case: (psiE `[n]) => l ->.
have [E|E] := leqP (troot n).-1 l.
  rewrite -(subnK E).
  elim: (_ - _) => [|k IH] //.
  apply: ler_trans IH.
  rewrite addSn.
  apply: psi_aux_decr => //.
  by rewrite leq_addl.
rewrite -(subKn (ltnW E)).
elim: (_ - l) => [|k IH].
  by rewrite subn0.
apply: ler_trans IH.
rewrite subnS.
have [|E1] := leqP (troot n).-1 k.
  by rewrite -subn_eq0 => /eqP->.
rewrite -{2}[_-_]prednK ?subn_gt0 //.
apply: psi_aux_incr => //.
case: _.-1 E1 => // u _; case: k => // k.
apply: leq_trans (_ : u.+1.-1 < u.+1) => //.
by rewrite ltnS -!subn1 leq_sub2r // leq_subr.
Qed.

(* This is 2.2 *)
Lemma psi_sint_phi n : n <= N -> (psi `[n]).*2 = (phi n.+1).-1.
Proof.
move=> nLN.
have [|nP] := leqP n 0; first by case: (n)=> //; rewrite psi_sint0.
apply/eqP; rewrite -(eqr_nat int_numDomainType).
rewrite -muln2 natrM mulr_natr.
rewrite psi_aux_sint // psi_auxE_lt.
rewrite (_ : [set _ | _] = [set i in `[n] | delta (troot n) <= i]);
   last first.
  apply/setP=> i; rewrite !inE; congr (_ && _).
  by rewrite prednK ?troot_gt0 // root_delta_le.
rewrite sint_sub ?delta_gt0 ?troot_gt0 // card_sint //.
rewrite (_ : \sum_(_ in _ | _) _  = phi (delta (troot n))); last first.
  rewrite phiE big_mkcond.
  pose f i := if (0 <= i < n) && (∇i <= (∇n).-1) then 2 ^ ∇i else 0.
  pose g (i : 'I_N) := f i.
  rewrite (eq_bigr g) => [|i _]; last by rewrite !inE.
  have F : delta (troot n) <= N by apply: leq_trans (delta_root_le _) nLN.
  have -> := (big_ord_widen _ (fun i => 2 ^ (troot i)) F).
  have G : 0 < N by apply: leq_trans nLN.
  rewrite [X in _ = X]big_mkcond.
  apply: eq_bigr => i _.
  congr (if _ then _ else _).
  rewrite -root_delta_lt -{2}(prednK (troot_gt0 nP)) ltnS.
  case: (leqP (troot i) _); rewrite !(andbT, andbF) //.
  rewrite andTb -ltnS prednK ?troot_gt0 // => H.
  apply/idP/(leq_trans _ (delta_root_le _)).
  by rewrite -root_delta_lt.
set m := troot n.
rewrite -[n - _]/(tmod n).
set p := tmod n.
rewrite phi_deltaE.
(* taking care of  m * 2 ^ m - 2 ^ m *)
rewrite -{2}[m]prednK ?troot_gt0 //.
rewrite mulSn addnCA [2 ^ _ + _]addnC addnK add1n.
rewrite addnS -addSn prednK; last first.
  by rewrite muln_gt0 expn_gt0. 
(* taking care of m.-1 * 2 ^ m - m.-1 * 2 ^ m.-1 *)
rewrite -{3}[m]prednK ?troot_gt0 //.
rewrite expnS mul2n -addnn mulnDr addnA natrD addrK.
rewrite mulnC -mulnDl addSnnS prednK ?troot_gt0 //.
rewrite -mulr_natr -natrM muln2 eqr_nat.
rewrite phi_modSE -/m -/p.
rewrite add1n -pred_Sn addnC -{4}[m]prednK ?troot_gt0 //.
by rewrite expnS mulnCA mul2n.
Qed.

Lemma psi_sint_leq a b : a <= b <= N -> psi `[a] <= psi `[b].
Proof.
move=> /andP[aLb bLN].
apply: psi_sub; apply/subsetP=> i.
by rewrite !inE !andTb => /leq_trans /(_ aLb).
Qed.

Lemma psi_sintS n : n < N -> psi `[n.+1] = psi `[n] + 2 ^ (troot n.+1).-1.
Proof.
move=> nLN.
have F : 0 < phi n.+1.
  by apply: phi_le (_ : 1 <= _).
apply: double_inj; rewrite doubleD.
rewrite !psi_sint_phi //; last by apply: ltnW.
rewrite -mul2n -expnS prednK ?troot_gt0 //.
by rewrite phiE big_ord_recr -phiE prednDl.
Qed.

(* This is 2.2 *)
Lemma psi_leD a b : 
  a + b <= N -> psi `[a + b] <= (psi `[a]).*2 + 2 ^ (b.-1).
Proof.
case: b => [abLN|b abLN]; first by rewrite addn0 -addnn -addnA leq_addr.
rewrite -leq_double doubleD [_.+1.-1]/=.
rewrite !psi_sint_phi //; last first.
  by apply: leq_trans abLN; rewrite leq_addr.
rewrite -addSn -ltnS prednK ?phi_gt0 //.
apply: leq_trans (phi_leD _ _) _.
rewrite -{1}[phi (a.+1)]prednK ?phi_gt0 // doubleS.
by rewrite expnS mul2n -prednDr ?double_gt0 ?expn_gt0.
Qed.

(* This is 2.3 *)
Lemma psi_SS_le n :
  n + 2 <= N -> psi `[n + 2] >= 2 ^(troot n).+1.
Proof.
case: n => [|n] n2LN; first by rewrite psi_sint2.
have /psi_sint_leq/(leq_trans _)->// : delta (troot n.+1) + 2 <= n.+1 + 2 <= N.
  by rewrite n2LN andbT leq_add2r -root_delta_le.
set s := troot _.
have thLN : 3 <= N by apply: leq_trans n2LN; rewrite addSnnS leq_addl.
have [|tLs] := leqP s 1.
  case: s => [|[|]] //; first by rewrite psi_sint2 ?(leq_trans _ thLN).
  by rewrite psi_sint3.
rewrite -leq_double psi_sint_phi; last first.
  apply: leq_trans n2LN.
  by rewrite leq_add2r -root_delta_le.
rewrite phi_modSE.
have tE : troot (delta s + 2) = s.
  by apply/eqP; rewrite trootE deltaS leq_addr ltn_add2l.
rewrite tE.
have->: tmod (delta s + 2) = 2 by rewrite /tmod tE addnC addnK.
by rewrite -mul2n expnS mulnA /= leq_mul2r (leq_add2r 2 2) tLs orbT.
Qed.

Lemma psi_aux0_sint n : n <= N -> psi_aux 0 `[n] = n.
Proof.
move=> nLN.
rewrite /psi_aux add0n subr0.
apply/eqP; rewrite -natz eqr_nat; apply/eqP.
rewrite (eq_bigr (fun i : 'I_N => 1)) => [|i _].
  by rewrite sum_nat_const card_sint // subn0 muln1.
by rewrite minn0.
Qed.

(* This is 2.4.1 *)
Lemma psi_sint_min n : n <= N -> n <= psi `[n].
Proof.
move=> nLN.
rewrite -(ler_nat int_numDomainType).
rewrite natz -[X in (X <= _)%R](psi_aux0_sint nLN).
by apply: psi_max.
Qed.

Lemma sum_sint (P : nat -> nat) n : n <= N ->
  \sum_(i in `[n]) P i = \sum_(i < n) P i.
Proof.
move=> nLN.
rewrite (big_ord_widen_cond _ xpredT P nLN).
by apply: eq_big => [i|i] //; rewrite inE.
Qed.

Lemma max_set_nat (e : {set 'I_N}) : 0 < N -> #|e|.-1 <= \max_(i in e) i.
Proof.
move=> NP.
elim: #|_| {1 4}e (eqP (eqxx #|e|)) => [e1 /eqP|[|n] // IH e1 Ce1/=].
  rewrite cards_eq0 => /eqP->.
  by rewrite big1 // => i; rewrite inE.
have /(eq_bigmax_cond (@nat_of_ord N)) [i Hi Hi1] : 
    0 < #|e1| by rewrite Ce1.
pose e2 := e1 :\ i.
have Ce2 : #|e2| = n.+1.
  apply/eqP; move/eqP: Ce1.
  by rewrite (cardsD1 i) Hi.
have /(eq_bigmax_cond (@nat_of_ord N)) [j Hj Hj1] : 
    0 < #|e2| by rewrite Ce2. 
apply: leq_ltn_trans (IH _ Ce2) _.
rewrite Hi1 Hj1.
have : j <= i.
  rewrite -Hj1 -Hi1.
  apply/bigmax_leqP=> j1.
  rewrite inE => /andP[_ jIe1].
  by apply: leq_bigmax_cond.
rewrite leq_eqVlt => /orP[] // /eqP jEi.
move: Hj.
rewrite jEi !inE.
case: eqP => /val_eqP //.
by rewrite /= jEi eqxx.
Qed.

Lemma psi_aux_card_le l e : #|e| <= N -> (psi_aux l `[#|e|] <= psi_aux l e)%R.
Proof.
move=> cLN.
rewrite ler_sub // ler_nat leq_add2l.
rewrite (sum_sint (fun i =>  2 ^ minn (∇i) l)) //.
elim: #|_| {1 9}e (eqP (eqxx #|e|)) cLN => [e1|n IH e1 Ce1 nLN].
  move/eqP; rewrite cards_eq0 => /eqP->.
  by rewrite big_ord0 big1 // => i; rewrite inE.
have /(eq_bigmax_cond (@nat_of_ord N)) [i Hi Hi1] : 
    0 < #|e1| by rewrite Ce1.
rewrite big_ord_recr (bigD1 i) //= addnC.
apply: leq_add.
  rewrite leq_exp2l //.
  rewrite leq_min geq_minr // (leq_trans (geq_minl _ _)) //.
  apply: troot_le.
  rewrite -Hi1 [n]pred_Sn -Ce1.
  apply: max_set_nat.
  by apply: leq_ltn_trans nLN.
pose e2 := e1 :\ i.
have -> : \sum_(i0 in e1 | i0 != i) 2 ^ minn (∇i0) l =
           \sum_(i0 in e2) 2 ^ minn (∇i0) l.
  rewrite big_mkcond /= [RHS]big_mkcond.
  by apply: eq_bigr => k _; rewrite !inE andbC.
apply: IH (ltnW nLN).
apply/eqP; move/eqP: Ce1.
by rewrite (cardsD1 i) Hi.
Qed.


(* This is 2.4.2 *)
Lemma psi_card_le e : #|e| <= N -> psi `[#|e|] <= psi e.
Proof.
move=> cLN.
apply: psi_aux_le_psi => l.
by apply: psi_aux_card_le.
Qed.

(* This is 2.4.3 *)
Lemma psi_exp e : #|e| <= N -> psi e <= (2 ^ #|e|).-1.
Proof.
move=> cLe.
rewrite -(ler_nat int_numDomainType).
have [l ->] := psiE e.
apply: ler_trans (_ : ((2 ^ l).-1 + \sum_(i in e) 2 ^ l)%:R - 
                      (l * 2 ^ l)%:R <= _)%R.
  apply: ler_sub => //.
  rewrite ler_nat leq_add2l.
  apply: leq_sum => i Hi.
  by rewrite leq_exp2l // geq_minr.
rewrite sum_nat_const ler_subl_addr -natrD ler_nat [X in _ <= X]addnC.
rewrite -prednDl ?expn_gt0 // -prednDr ?expn_gt0 //.
rewrite -!subn1 leq_sub2r //.
have [E|E] := leqP #|e| l.
  rewrite -(subnK E).
  set u := _ - _.
  rewrite expnD !mulnDl addnAC leq_add2r.
  case: u => [|u]; first by rewrite mul1n.
  by rewrite mulSn -addnA leq_addr.
rewrite -(subnK (ltnW E)).
set u := _ - _.
rewrite expnD !mulnDl addnA addnC leq_add2l.
by rewrite -mulSn leq_mul2r ltn_expl // orbT.
Qed.

(* This is 2.5 *)
Lemma psi_diff e1 e2 : psi e1 - psi e2 <= \sum_(i in e1 :\: e2) 2 ^ troot i.
Proof.
rewrite leq_subLR -(ler_nat int_numDomainType) natrD addrC -ler_subl_addr.
have [l ->] := psiE e1.
apply: ler_trans (ler_sub (lerr _) (psi_max _ l)) _.
rewrite /psi_aux opprB addrA subrK addnC !natrD opprD addrA addrK.
rewrite ler_subl_addr -natrD ler_nat addnC -leq_subLR.
set s1 := \sum_(_ in _) _; set s2 := \sum_(_ in _) _; set s3 := \sum_(_ in _) _.
pose f (i : 'I_N) := 2 ^ minn (troot i) l.
apply: leq_trans (_ :  \sum_(i in e1 :\: e2) f i <= _); last first.
  by apply: leq_sum => i _; rewrite leq_exp2l // geq_minl.
rewrite leq_subLR.
rewrite [s1](bigID (fun i => i \in e2)) //=.
rewrite -(sum_set_diff f) (sum_set_swap f).
rewrite leq_add2r.
rewrite [s2](bigID (fun i => i \in e1)) //=.
by rewrite leq_addr.
Qed.

(* This is 2.6 *)

Lemma psi_delta e s a : 
  #|e :\: `[delta s]| <= s -> a \in e ->
    psi e - psi (e :\  a) <= 2 ^ s.-1.
Proof.
move=> CLs aIe.
rewrite leq_subLR -(ler_nat int_numDomainType) natrD addrC -ler_subl_addr.
have [l Hl] := psiE e.
have F l1 : s <= l1.+1 -> (psi_aux l1.+1 e <= psi_aux l1 e)%R. 
  move=> sLl1.
  rewrite psi_auxE_le.
  rewrite psi_auxE_lt.
  set s1 := \sum_(_ in _ | _) _.
  have /eq_card-> : [set i in e | l1 < troot i] =i 
                    [set i in e | delta l1.+1 <= i].
    by move=> i; rewrite !inE root_delta_le.
  set c := #|_|.
  have Hc : c <= s.
    apply: leq_trans CLs.
    apply: subset_leq_card.
    apply/subsetP=> i.
    rewrite !inE => /andP[-> H].
    rewrite andbT -leqNgt (leq_trans _ H) //.
    by apply: delta_le.
  rewrite expnS mulnAC [2 * _ * _]mulnC.
  rewrite mul2n mulnA muln2 -!addnn -[_ + l1.+1]addSnnS.
  rewrite mulnDl mulnDr prednDr ?(muln_gt0, expn_gt0) //.
  set x := 2 ^ _ * _.
  rewrite -[_ + s1]addnA [x + _]addnC.
  rewrite [X in (_ - X <= _)%R]natrD opprD addrA ler_add //.
  rewrite ler_sub_addr natrD ler_add // ler_nat.
  by rewrite mulnC leq_mul2l ltnS (leq_trans _ sLl1) ?orbT.
pose l1 := minn l s.-1.
have -> : ((psi e)%:R = psi_aux l1 e)%R.
  have [/minn_idPl U|E] := leqP l s.-1; first by rewrite [l1]U.
  have /ltnW/minn_idPr U := E.
  rewrite [l1]U.
  apply/eqP; rewrite eqr_le psi_max andbT Hl.
  rewrite -(subnK (ltnW E)).
  elim: (_ - _) => [|k IH] //.
  apply: ler_trans IH.
  rewrite addSn.
  apply: F => //.
  case: (s) => // s1.
  by rewrite ltnS /= leq_addl.
apply: ler_trans (ler_sub (lerr _) (psi_max _ l1)) _.
rewrite /psi_aux opprB addrA subrK addnC !natrD opprD addrA addrK.
rewrite ler_subl_addr -natrD ler_nat addnC -leq_subLR.
rewrite (bigD1 a) //=.
set s1 := \sum_(_ in _) _; set s2 := \sum_(_ in _ | _) _.
suff -> : s1 = s2.
  rewrite addnK leq_exp2l //.
  by apply: leq_trans (geq_minr _ _) (geq_minr _ _).
rewrite [s1]big_mkcond [s2]big_mkcond.
apply: eq_bigr => i _.
by rewrite !inE andbC.
Qed.

(* This is 2.7 *)
Lemma psi_add n s e1 e2 : 
  n + s <= N -> e1 \subset `[n] -> n >= delta (s.-1) ->  #|e2| <= s ->
  psi (e1 :|: e2) - psi (e1) <= psi `[n + s] - psi `[n].
Proof.
move=> nsLN e1Sn.
elim: s e2 nsLN => [e2 _ _|s IH e2 nLs dLn Ce2] //.
  rewrite leqn0 cards_eq0 => /eqP->.
  by rewrite setU0 subnn.
have [->|[x xIe2]] := set_0Vmem e2.
  by rewrite setU0 subnn.
have nLs1 : n + s <= N.
  apply: leq_trans _ nLs.
  by rewrite leq_add2l.
have dLn1 : delta (s.-1) <= n.
  apply: leq_trans dLn.
  by apply: delta_le; case: (s) => // s1 /=.
pose e3 := e2 :\ x.
have Ce3 : #|e3| <= s.
  by move: Ce2; rewrite (cardsD1 x) xIe2 ltnS.
apply: leq_trans (leq_sub_add (psi (e1 :|: e3)) _ _) _.
rewrite addnS psi_sintS; last by rewrite -addnS.
rewrite [X in _ <= X - _]addnC -addnBA; last first.
  by apply: psi_sint_leq; rewrite leq_addr.
apply: leq_add; last by apply: IH.
have [xIe1|xNIe1] := boolP (x \in e1).
  have -> : e1 :|: e2 = e1 :|: e3.
    apply/setP=> i; rewrite !inE.
    by case: eqP => // ->; rewrite xIe1.
  by rewrite subnn.
have -> : e1 :|: e3 = (e1 :|: e2) :\ x.
  apply/setP=> i; rewrite !inE.
  case: eqP => // ->.
  by rewrite (negPf xNIe1).
apply: psi_delta; last first.
  by rewrite !inE xIe2 orbT.
rewrite -addnS.
set t := s.+1.
set g := troot (n + t).
apply: leq_trans (_ : #|e2 :|: (e1 :\: `[delta g])| <= _).
  apply: subset_leq_card.
  apply/subsetP=> i.
  rewrite !inE.
  do 2 case: (_ \in _) => //.
apply: leq_trans (_ : #|e2| + #|e1 :\: `[delta g]| <= _).
  by rewrite -cardsUI leq_addr.
apply: leq_trans (_ : t + #|e1 :\: `[delta g]| <= _).
  by rewrite leq_add2r.
apply: leq_trans (_ : t + #|sint (delta g) n| <= _).
  rewrite leq_add2l.
  apply: subset_leq_card.
  apply/subsetP=> i.
  rewrite !inE -leqNgt => /andP[-> /(subsetP e1Sn)].
  by rewrite inE.
rewrite card_sint; last by apply: leq_trans (leq_addr _ _) nLs.
have [|E] := leqP n (delta g); last first.
  rewrite addnBA; last by apply: ltnW.
  rewrite leq_subLR addnC.
  by rewrite -ltnS -!addnS -deltaS addnS -root_delta_lt.
move/eqP->; rewrite addn0.
by rewrite root_delta_le deltaS leq_add2r.
Qed.

(* This is 2.8 *)
Lemma psi_cap_ge e1 e2 :
 #|e1 :|: e2| <= N ->
 phi (#|e1 :|: e2|.+3) <= (psi e1 + psi e2).*2.*2 + 5.
Proof.
move=> cLN.
rewrite -(ler_nat int_numDomainType) natrD.
rewrite -!muln2 !natrM !mulr_natr -mulrnA natrD.
set n := #|_|.
pose m := troot (n.+3).
pose p := tmod (n.+3).
pose l := m.-2.
have mG2 : m >= 2 by rewrite root_delta_le.
have pLm : p <= m.
  by rewrite leq_subLR -ltnS -[X in _ < X]addnS -deltaS -root_delta_lt ltnS.
have nG : n >= delta l.
  rewrite -[n]/(n.+3.-2.-1) [n.+3]tmodE /l -/m.
  case: (m) mG2 => // [] [|] // m1 _.
  by rewrite deltaS deltaS /= !(addSn, addnS, subSS, subn0) -!addnA leq_addr.
apply: ler_trans (_ : ((psi_aux l `[0] + psi_aux l `[n]) *+ 4 + 5%:R <= _))%R; 
     last first.
  rewrite ler_add2r ler_muln2r orFb.
  apply: ler_trans (_ : psi_aux l e1 + psi_aux l e2 <= _)%R; last first.
    by apply: ler_add; apply: psi_max.
  apply: ler_trans (_ : psi_aux l (e1 :&: e2) + psi_aux l (e1 :|: e2) <= _)%R.
    apply: ler_add; last by apply: psi_aux_card_le.
    apply: psi_aux_sub; rewrite sint0_set0.
    by apply/subsetP=> i; rewrite inE.
  rewrite /psi_aux.
  rewrite !natrD !addrA ler_add // -!addrA ler_add //.
  rewrite addrCA [X in (_ <= X)%R]addrCA ler_add //.
  rewrite addrCA [X in (_ <= X)%R]addrCA ler_add //.
  rewrite -!natrD ler_nat.
  rewrite [X in _ <= X + _](bigID (fun i => i \in e2)) /=.
  rewrite -!addnA leq_add //.
    rewrite big_mkcond [X in _ <= X]big_mkcond /=.
    by apply: leq_sum => i _; rewrite !inE; do 2 case: (_ \in _).
  rewrite [X in X <= _](bigID (fun i => i \in e2)) /=.
  rewrite addnC leq_add //.
    rewrite big_mkcond [X in _ <= X]big_mkcond /=.
    by apply: leq_sum => i _; rewrite !inE; do 2 case: (_ \in _).
  rewrite big_mkcond [X in _ <= X]big_mkcond /=.
  apply: leq_sum => i _; rewrite !inE; do 2 case: (_ \in _) => //=.
have pE : phi (n.+3) = ((m + p - 1) * 2 ^ m).+1.
  rewrite phi_modE -/m -/p -{1 4}[m]prednK 1?ltnW //.
  rewrite [_ + p]addSn mulSn [2 ^ _ + _]addnC addnA addnK.
  by rewrite -subn1 -[(_ + _).+1]addn1 addnK.
have pdE : ((phi (delta l))%:R = 1 + (l%:R - 1) * (2 ^ l)%:R :> int)%R.
  rewrite phi_deltaE natrB; last first.
    by case: (l) => // l1; rewrite mulSn addnCA leq_addr.
  by rewrite natrD /= mulrBl mul1r addrA -natrM.
rewrite ler_eqVlt; apply/orP; left; apply/eqP.
(* right part *)
rewrite psi_aux_sintE // psi_auxE_le.
pose f i := 2 ^ minn (∇i) l.
rewrite !(big_mkord _ f) big_ord0 addn0.
have /eq_card-> : [set i in `[n] | l <= troot i] =i 
                  [set i in `[n] | delta l <= i].
  by move=> i; rewrite !inE root_delta_le.
have /(sint_sub n)-> : 0 <= delta l.
  by apply: (@delta_le 0).
rewrite card_sint //.
rewrite (_ : \sum_(_ in _ | _) _  = phi (delta l)); last first.
  rewrite phiE big_mkcond /=.
  have F : delta l <= N by apply: leq_trans cLN.
  have -> := (big_ord_widen _ (fun i => 2 ^ (troot i)) F).
  rewrite [X in _ = X]big_mkcond.
  apply: eq_bigr => i _.
  congr (if _ then _ else _).
  rewrite -root_delta_lt !inE.
  case: (leqP _ l); rewrite ?andbF //.
  by rewrite root_delta_lt => /leq_trans->.
(* right part *)
apply: etrans
 (_ : ((2 ^ l)%:R * (m.-1 + p)%:R - 1%:R) *+4 + 5%:R = _)%R; last first.
 congr (_ *+ _ + _)%R.
rewrite -!subn1 ![in RHS](natrD, natrM, natrB) ?muln_gt0 ?expn_gt0 //.
rewrite pdE !addrA addrK; set u := (2 ^ l)%:R%R.
rewrite [(u - 1)%R]addrC -![in RHS]addrA [RHS]addrC; congr (_ - _)%R.
rewrite -{2}[u]mul1r ![(u * _)%R]mulrC -![(-(_ * u))%R]mulNr -!mulrDl.
congr (_ * _)%R.
rewrite {u}!addrA addrAC addrK.
rewrite -[(_ - _).+1]addn1 [in RHS]natrD !addrA addrK.
rewrite -[n]/(n.+3.-2.-1) [n.+3]tmodE -/m -/p.
rewrite -[in RHS](subnK mG2) ![in RHS](addnS, addn0) !deltaS !(subnS, subn0).
rewrite ![in RHS](addnS, addSn) -!addnA [delta _ + _]addnC addnK -/l.
by rewrite ![in RHS]natrD !addrA subrK /l -(natrD _ 1%nat) -natrD.
(* left part *)
rewrite pE /l.
case: (m) mG2 => // [] [|m1] //= _.
rewrite addSn subn1 /=.
rewrite (_ : 5%:R = 1 *+ 4 + 1)%R // addrA -mulrnDl.
rewrite subrK -addn1 natrD; congr (_ + _)%R.
rewrite -[in RHS]mulr_natr -!natrM [in RHS]mulnAC mulnC.
congr (_ * _)%:R%R.
by rewrite mulnC !expnS !mulnA.
Qed.

Lemma phi_3_5_4_phi n :
   n <= N -> phi (n.+3) = 
    (2^(troot n.+2)) + (2^(troot n.+1)) + (psi `[n]).*2.+1.
Proof.
move=> nLN.
rewrite psi_sint_phi // phiS phiS prednK ?phi_gt0 //.
by rewrite [RHS]addnC !addnA addnAC.
Qed.

Lemma phi_3_5_4_sum n :
   phi (n.+3) = (\sum_(1 <= i < n.+3) 2 ^ troot i).+1.
Proof.
rewrite phiE.
rewrite -(big_mkord xpredT (fun i => 2 ^ troot i)).
rewrite (big_cat_nat _ _ _ (_ : 0 <= 1)) //=.
by rewrite big_nat_recl //= big_mkord big_ord0 addn0 add1n.
Qed.
End PsiDef.

Lemma ltn_diff_ord_max n (i : 'I_n.+2) : i != ord_max -> i < n.+1.
Proof.
move/eqP/val_eqP.
by have := ltn_ord i; rewrite ltnS leq_eqVlt => /orP[->|].
Qed.

Lemma lift_diff_ord_max n (i : 'I_n.+2) :
  i != ord_max -> lift ord_max (inord i) = i.
Proof.
move=> iDm.
apply/val_eqP; rewrite [val (lift _ _)]lift_max /= ?inordK //.
by apply: ltn_diff_ord_max.
Qed.

Lemma set_ord_max_lift n (e : {set 'I_n.+2}) :
  e :\ ord_max = [set lift ord_max x | x in [set i | lift ord_max i \in e]].
Proof.
apply/setP => i; rewrite !inE /=.
apply/andP/imsetP => [[iH iIe]|[j //]].
  exists (inord i).
    by rewrite inE lift_diff_ord_max.
  by rewrite lift_diff_ord_max.
rewrite inE => kH ->; split => //.
apply/eqP/val_eqP.
by rewrite [val (lift _ _)]lift_max /= neq_ltn ltn_ord.
Qed.

Lemma psi_auxb_ord_max (n : nat) (e : {set 'I_n.+1}) : 
  psi_auxb (e :\ ord_max) = psi_auxb [set i | lift ord_max (i : 'I_n) \in e].
Proof.
case: n e => [e|n e].
  rewrite /psi_auxb (_ : #|_| = 0); last first.
    apply/eqP; rewrite cards_eq0.
    by apply/eqP/setP=> [] [[|i] //= H]; rewrite !inE.
  rewrite /psi_auxb (_ : #|_| = 0); last first.
    apply/eqP; rewrite cards_eq0.
    by apply/eqP/setP=> [] [[|i] //= H]; rewrite !inE.
  by rewrite !big1 // => [] [[]] //.
congr (maxn _ _).+1.
  rewrite -[RHS](@card_imset _ _ (lift ord_max) _); last by apply: lift_inj.
  congr (#|pred_of_set _|).
  by apply: set_ord_max_lift.
have F i : i \in e :\ ord_max -> lift ord_max (inord i) = i. 
  by rewrite !inE => /andP[/lift_diff_ord_max].
rewrite (reindex_onto _ _ F).
apply: eq_big => i; last by rewrite lift_max.
rewrite !inE !lift_max (_ : _ != ord_max) 1?(_ : inord _ == i) ?andbT //.
  by apply/eqP/val_eqP; rewrite /= inordK.
apply/eqP/val_eqP; rewrite neq_ltn ltn_diff_ord_max //.
by rewrite eq_sym neq_lift.
Qed.

Lemma psi_ord_max (n : nat) (e : {set 'I_n.+1}) : 
  psi (e :\ ord_max) = psi [set i | lift ord_max (i : 'I_n) \in e].
Proof.
case: n e => [e | n e].
  rewrite (_ : _ :\ _ = set0); last first.
    by apply/setP=> [] [[|] // H]; rewrite !inE.
  rewrite (_ : [set _ | _] = set0); last first.
    by apply/setP=> [] [[|] // H]; rewrite !inE.
  by rewrite !psi_set0.
rewrite /psi -psi_auxb_ord_max.
apply: eq_big => // i _.
congr (rnz ((_ + _)%:R + _)).
have F i1 : i1 \in e :\ ord_max -> lift ord_max (inord i1) = i1. 
  by rewrite !inE => /andP[/lift_diff_ord_max].
rewrite (reindex_onto _ _ F).
apply: eq_big => j; last by rewrite lift_max.
rewrite !inE !lift_max (_ : _ != ord_max) 1?(_ : inord _ == j) ?andbT //.
  by apply/eqP/val_eqP; rewrite /= inordK.
apply/eqP/val_eqP; rewrite neq_ltn ltn_diff_ord_max //.
by rewrite eq_sym neq_lift.
Qed.
