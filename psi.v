
(******************************************************************************)
(*                                                                            *)
(*                                    PSI                                     *)
(*     psi n = the psi function                                               *)
(*                                                                            *)
(*                                                                            *)
(*                                                                            *)
(******************************************************************************)

From mathcomp Require Import all_ssreflect all_algebra finmap.
Require Import extra triangular phi.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Open Scope fset_scope.
Open Scope nat_scope.


Section BigFSetAux.

Variable (R : Type) (idx : R) (op : Monoid.com_law idx).
Variable (I J : choiceType).

Lemma fsum_nat_const (e : {fset I}) a : \sum_(i <- e) a = #|` e| * a.
Proof. by rewrite big_const_seq count_predT iter_addn_0 mulnC. Qed.

Lemma diff_fset0_elem (e : {fset I}) : e != fset0 -> {i : I | i \in e}.
Proof.
by case: e => [] [|i l] iH //=; exists i; rewrite inE eqxx.
Qed.

(* Should be reworked  *)
Lemma eq_fbigmax (e : {fset I}) (F : I -> nat) :
  0 < #|`e| -> {i0 : I | i0 \in e /\ \max_(i <- e) F i = F i0}.
Proof.
have [n cI] := ubnP #|`e|; elim: n => // n IH e cI in e cI *.
rewrite cardfs_gt0 => /diff_fset0_elem[i iH].
have [|H] := leqP #|`(e `\ i)| 0.
  rewrite leqn0 cardfs_eq0 => /eqP eZ.
  exists i; split => //.
  rewrite (big_fsetD1 i) //= eZ big1_fset => [|j]; last by rewrite inE.
  by apply/maxn_idPl.
case: (IH (e `\ i)) => // [|j [jIe jH]].
  by move: cI; rewrite (cardfsD1 i) iH.
have [FiLFj|FjLFi] := leqP (F i) (F j).
  exists j; split => //.
    by move: jIe; rewrite !inE => /andP[].
  rewrite (big_fsetD1 i) //= jH.
  by apply/maxn_idPr.
exists i; split.
  by move: jIe; rewrite !inE => /andP[].
rewrite (big_fsetD1 i) //= jH.
by apply/maxn_idPl/ltnW.
Qed.

Lemma big_fsetD1cond (a : I) (A : {fset I}) (P : pred I) (F : I -> R) : 
   a \in A -> P a ->
  \big[op/idx]_(i <- A | P i) F i = 
     op (F a) (\big[op/idx]_(i <- A `\ a | P i) F i).
Proof.
move=> aA aP; rewrite (big_fsetIDcond _ (mem [fset a])).
congr (op _ _); last first.
  by apply: eq_fbigl_cond => i; rewrite !inE /= [_ && (_ != _)]andbC.
rewrite (_ : [fset _ | _ in _ & _] = [fset a]).
  rewrite big_seq_fsetE /= /index_enum /= -enumT enum_fset1 /=.
  by rewrite unlock /= aP Monoid.Theory.mulm1.
by apply/fsetP=> i; rewrite !inE /= andbC; case: eqP => //->.
Qed.

End BigFSetAux.

Section BigFSetAux.

Variable (R : Type) (idx : R) (op : Monoid.com_law idx).
Variable (I J : choiceType).

Lemma bigfmax_leqP (P : pred I) (m : nat) (e : {fset I}) (F : I -> nat) :
  reflect (forall i : I, i \in e -> P i -> F i <= m) 
          (\max_(i <- e | P i) F i <= m).
Proof.
apply: (iffP idP) => leFm => [i iIe Pi|].
  move: leFm.
  rewrite (big_fsetD1cond _ _ _ Pi) //= => /(leq_trans _)-> //.
  by apply: leq_maxl.
rewrite big_seq_cond.
elim/big_ind: _ => //= [m1 m2 m1Lm m2Ln | i /andP[]].
  by rewrite geq_max m1Lm.
by apply: leFm.
Qed.

Lemma leq_bigfmax (e : {fset I}) (F : I -> nat) i :
   i \in e ->  F i <= \max_(i <- e) F i.
Proof.
move=> iIe.
have : i \in enum_fset e by [].
elim: enum_fset => //= a l IH.
rewrite inE big_cons => /orP[/eqP<-|/IH H]; first by apply: leq_maxl.
by apply: leq_trans H _; apply: leq_maxr.
Qed.

End BigFSetAux.

Section PsiDef.

Implicit Type e : {fset nat}.

Import Order.TTheory GRing.Theory Num.Theory.


Open Scope fset_scope.

Definition psi_aux l e : int :=
  ((2 ^ l).-1 + (\sum_(i <- e) 2 ^ (minn (troot i) l)))%:R - (l * 2 ^ l)%:R.

Notation "'ψ'' n" := (psi_aux n) (format "'ψ'' n", at level 0).

Lemma psi_aux_0_ge0 e :  (0 <= psi_aux 0 e)%R.
Proof. by rewrite /psi_aux add0n mul0n subr0 (ler_nat _ 0). Qed.
Lemma psi_aux_sub l e1 e2 : e1 `<=` e2 -> (psi_aux l e1 <= psi_aux l e2)%R.
Proof.
move=> e1Se2.
apply: ler_sub => //.
rewrite ler_nat.
rewrite leq_add2l //.
rewrite [X in _ <= X](bigID (fun i => i \in e1)) /=.
suff iH : [fset x in e1 | xpredT x] =i [fset i in e2 | i \in e1].
  by rewrite (eq_fbigl_cond _ _ iH) /= leq_addr.
move=> i; rewrite !inE /=.
have /fsubsetP/(_ i) := e1Se2.
by case: (i \in e1) => [->//|]; rewrite andbF.
Qed.

Lemma psi_auxE_le l e :
  psi_aux l e = 
   (((2 ^ l * #|`[fset i in e | (l <= troot i)%nat]|.+1).-1 
    + (\sum_(i <- e | (troot i < l)%nat) 2 ^ troot i))%:R - (l * 2 ^ l)%:R)%R.
Proof.
rewrite /psi_aux.
congr (_%:R - _%:R)%R.
rewrite (big_fsetID _ [pred i | l <= ∇i]) /=.
rewrite (@eq_fbigr _ _ _ _ _ _ _ (fun i => 2 ^ l)) /=; last first.
  by move=> i; rewrite !inE => /andP[_ /minn_idPr->].
rewrite fsum_nat_const.
rewrite (@eq_fbigr _ _ _ _ _ _ _  (fun i => 2 ^ (troot i))) /=; last first.
  move=> i; rewrite !inE => /andP[_ H] _.
  suff /minn_idPl-> : troot i <= l by [].
  by rewrite ltnW // ltnNge.
rewrite addnA; congr (_ + _)%nat.
  rewrite mulnS [_ ^ _ * #|`_|]mulnC.
  by case: (2 ^ l) (expn_gt0 2 l).
by apply: eq_fbigl_cond => i; rewrite !inE ltnNge andbT.
Qed.

Lemma psi_auxE_lt l e :
  psi_aux l e =
   (((2 ^ l * #|`[fset i in e | (l < troot i)%nat]|.+1).-1 
    + (\sum_(i <- e | (troot i <= l)%nat) 2 ^ troot i))%:R - (l * 2 ^ l)%:R)%R.
Proof.
rewrite /psi_aux.
congr (_%:R - _%:R)%R.
rewrite (big_fsetID _ [pred i | l < troot i]) /=.
rewrite (@eq_fbigr _ _ _ _ _ _ _ (fun => 2 ^ l)) /=; last first.
  by move=> i; rewrite !inE => /andP[_ /ltnW/minn_idPr ->].
rewrite fsum_nat_const.
rewrite (@eq_fbigr _ _ _ _ _ _ _ (fun i => 2 ^ troot i)) /=; last first.
  move=> i; rewrite !inE /= => /andP[_ H] _.
  suff /minn_idPl-> : troot i <= l by [].
  by rewrite leqNgt.
rewrite addnA; congr (_ + _)%nat.
  rewrite mulnS [_ ^ _ * #|`_|]mulnC.
  by case: (2 ^ l) (expn_gt0 2 l).
by apply: eq_fbigl_cond => i; rewrite !inE ltnNge andbT negbK.
Qed.

Definition psi_auxb e := (maxn #|`e| (\max_(i <- e) troot i)).+1.

Notation "'ψ_b' n" := (psi_auxb n) (format "'ψ_b' n", at level 0).

Lemma psi_aux_psib l e : psi_auxb e <= l -> (psi_aux l e <= 0)%R.
Proof.
rewrite /psi_auxb; case: l => // l.
rewrite ltnS /psi_aux geq_max => /andP[eLl maxLl].
rewrite mulSn -{2}[_ ^ _]prednK ?expn_gt0 // addSnnS.
rewrite !natrD [(_%:R + _)%R]addrC opprD addrA addrK.
rewrite subr_le0 ler_nat.
apply: leq_trans (leqnSn _).
apply: leq_trans (_ : #|`e| * 2 ^ l.+1 <= _); last first.
  by rewrite leq_mul2r eLl orbT.
rewrite -fsum_nat_const.
apply: leq_sum => i iIe.
apply: leq_pexp2l => //.
by apply geq_minr.
Qed.

Definition rnz (z : int) := `|Num.max 0%R z|.

Lemma rnz_ler0 z : (z <= 0)%R -> rnz z = 0.
Proof. by move=>  zN; rewrite /rnz max_l. Qed.

Lemma rnz_ger0 z : (0 <= z)%R -> (z = (rnz z)%:R)%R.
Proof. by move=>  zP; rewrite /rnz max_r // natz gez0_abs. Qed.

Lemma ler_rnz z : (z <= rnz z)%R.
Proof. by rewrite /rnz; case: ler0P => //= zP; rewrite gtz0_abs. Qed.

Lemma rnz_ler z1 z2 : (z1 <= z2)%R -> rnz z1 <= rnz z2.
Proof.
rewrite /rnz; case: ler0P => // z1_gt0 z1Lz2; case: ler0P => //= [|z2_gt0].
  by rewrite leNgt => /negP[]; apply: lt_le_trans z1Lz2.
by rewrite -lez_nat !gtz0_abs.
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
have [/le_trans->//|/ltW/rnz_ger0->] := lerP (psi_aux l e) 0.
  by rewrite (ler_nat _ 0).
rewrite ler_nat.
by rewrite (bigD1 (Ordinal O)) //= leq_maxl.
Qed.

Lemma psi_ler l e : 
  (((2 ^ l).-1 + \sum_(i <- e) 2 ^ (minn (troot i) l))%:R - (l * 2 ^ l)%:R 
      <= ((psi e)%:R : int))%R.
Proof.
have [/psi_aux_psib/le_trans->//|lLp] := leqP (psi_auxb e) l.
  by rewrite (ler_nat _ 0).
rewrite [X in (_ <= X%:R)%R](bigD1 (Ordinal lLp)) //=.
apply: le_trans (ler_rnz _) _.
rewrite -natz ler_nat.
apply: leq_maxl.
Qed.

Lemma psiE e :  {l | ((psi e)%:R = psi_aux l e)%R}.
Proof.
have [l] :  {l : 'I_(psi_auxb e) | psi e = rnz (psi_aux l e)}.
  apply: eq_bigmax.
  by rewrite card_ord.
rewrite /rnz; case: ler0P => [pG pE|pP ->]; last first.
  by exists l; rewrite natz gtz0_abs.
by exists 0; apply/eqP; rewrite eq_le {1}pE psi_aux_0_ge0 psi_max.
Qed.

Lemma psi_sub e1 e2 : e1 `<=` e2 -> psi e1 <= psi e2.
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

Lemma psi_auxb_sint n : psi_auxb `[n] = n.+1.
Proof.
congr (_.+1).
rewrite /psi_auxb.
rewrite card_sint ?geq_minr // subn0.
apply/eqP.
rewrite eqn_leq leq_maxl andbT geq_max leqnn andTb.
apply/bigfmax_leqP => i; rewrite mem_sint /= => iLn _.
by apply: leq_trans (leq_rootnn _) (ltnW _).
Qed.

Lemma psi_aux_sintE n l :
  psi_aux l `[n] = 
  (((2 ^ l).-1 + \sum_(0 <= i <  n) 2 ^ minn (∇i) l)%:R -
   (l * 2 ^ l)%:R)%R.
Proof.
congr ((_ + _)%:R - _%:R)%R.
elim: n => [|n IH]; first by rewrite sint0_set0 /= big_nil.
rewrite (big_fsetD1 n) /=; last by rewrite mem_sint andTb.
by rewrite sintSr IH !big_mkord big_ord_recr /= addnC.
Qed.

Lemma psi_auxb_set0 : psi_auxb fset0 = 1.
Proof. by rewrite /psi_auxb cardfs0 max0n big_seq_cond big1. Qed.

Lemma  psi_set0 : psi fset0 = 0.
Proof.
rewrite /psi psi_auxb_set0.
rewrite !big_ord_recr /= big_ord0 /= max0n.
by rewrite /psi_aux /= big_seq_cond big1.
Qed.

Lemma psi_eq0 e : (psi e == 0) = (e == fset0).
Proof.
have [->|[x]] := fset_0Vmem e; first by rewrite psi_set0 !eqxx.
have [->|_] := e =P fset0; first by rewrite inE.
move=> xIe.
suff : psi e > 0 by case: psi.
rewrite -(ltr_nat int_numDomainType).
apply: lt_le_trans (psi_max _ 0).
by rewrite /psi_aux add0n subr0 ltr_nat (big_fsetD1 x).
Qed.

Lemma  psi_sint0 : psi `[0] = 0.
Proof. by rewrite sint0_set0 psi_set0. Qed.

Lemma  psi_sint1 : psi `[1] = 1.
Proof.
rewrite /psi psi_auxb_sint.
rewrite -(big_mkord xpredT (fun l => rnz (psi_aux l _))).
pose f l := 
    rnz (((2 ^ l).-1 + \sum_(0 <= i <  1) 2 ^ minn (∇i) l)%:R -
         (l * 2 ^ l)%:R).
rewrite (eq_bigr f) => [|i _]; last by rewrite psi_aux_sintE.
by rewrite /f /= unlock.
Qed.

Lemma  psi_sint2 : psi `[2] = 2.
Proof.
rewrite /psi psi_auxb_sint.
rewrite -(big_mkord xpredT (fun l => rnz (psi_aux l _))).
pose f l := 
    rnz (((2 ^ l).-1 + \sum_(0 <= i <  2) 2 ^ minn (∇i) l)%:R -
         (l * 2 ^ l)%:R).
rewrite (eq_bigr f) => [|i _]; last by rewrite psi_aux_sintE.
by rewrite /f /= unlock.
Qed.

Lemma  psi_sint3 : psi `[3] = 4.
Proof.
rewrite /psi psi_auxb_sint.
rewrite -(big_mkord xpredT (fun l => rnz (psi_aux l _))).
pose f l := 
    rnz (((2 ^ l).-1 + \sum_(0 <= i <  3) 2 ^ minn (∇i) l)%:R -
         (l * 2 ^ l)%:R).
rewrite (eq_bigr f) => [|i _]; last by rewrite psi_aux_sintE.
by rewrite /f /= unlock.
Qed.

Lemma psi_aux_incr n l :
  l < (troot n).-1 -> (psi_aux l `[n] <= psi_aux l.+1 `[n])%R.
Proof.
move=> lLr.
have dlLn : delta l.+2 <= n.
  rewrite -root_delta_le -subn_gt0.
  by rewrite -[l.+1]addn1 addnC subnDA subn_gt0 subn1.
rewrite psi_auxE_lt psi_auxE_le.
set s := \sum_(_ <- _ | _) _.
have -> : [fset i in `[n] | l < troot i] = [fset i in `[n] | delta l.+1 <= i].
   by apply/fsetP => i; rewrite !inE root_delta_le.
have /(sint_sub n)-> : 0 <= delta l.+1 by apply: delta_le (_ : 0 <= l.+1).
rewrite card_sint //.
set c := n - _.
rewrite expnS mulnAC [2 * _ * _]mulnC.
rewrite mul2n mulnA muln2 -!addnn -[(_ + l.+1)%nat]addSnnS.
rewrite mulnDl mulnDr prednDr ?(muln_gt0, expn_gt0) //.
set x := 2 ^ _ * _.
rewrite -[(_ + _ + s)%nat]addnA [(x + _)%nat]addnC.
rewrite [((_ + _ * _)%:R)%R]natrD opprD addrA ler_sub //.
rewrite ler_subr_addr [((_ + x)%:R)%R]natrD ler_add //.
rewrite ler_nat.
rewrite mulnC leq_mul2l.
rewrite -subSn; last first.
  apply: leq_trans (_ : delta l.+2 <= _); first by by apply: delta_le.
  by apply: leq_trans dlLn _.
by rewrite ltn_subRL -addnS -deltaS (leq_trans dlLn) ?orbT.
Qed.

Lemma psi_aux_decr n l :
  (troot n).-1 <= l -> (psi_aux l.+1 `[n] <= psi_aux l `[n])%R.
Proof.
move=> rLl.
have dlLn : n < delta l.+2.
  rewrite ltnNge -root_delta_le -subn_gt0.
  by rewrite -[l.+1]addn1 addnC subnDA subn_gt0 subn1 -ltnNge.
rewrite psi_auxE_le.
rewrite psi_auxE_lt.
set s := \sum_(_ <- _ | _) _.
have -> : [fset i in `[n] | l < troot i] = 
          [fset i in `[n] | delta l.+1 <= i].
  by apply/fsetP => i; rewrite !inE root_delta_le.
have /(sint_sub n)-> : 0 <= delta l.+1 by apply: delta_le (_ : 0 <= l.+1).
rewrite card_sint //.
set c := n - _.
rewrite expnS mulnAC [2 * _ * _]mulnC.
rewrite mul2n mulnA muln2 -!addnn -[(_ + l.+1)%nat]addSnnS.
rewrite mulnDl mulnDr prednDr ?(muln_gt0, expn_gt0) //.
set x := 2 ^ _ * _. 
rewrite -[(_ + s)%nat]addnA [(x + _)%nat]addnC.
rewrite [((_ + _ * _)%:R)%R]natrD opprD addrA ler_sub //.
rewrite ler_subl_addr [((_ + x)%:R)%R]natrD ler_add //.
rewrite ler_nat.
rewrite mulnC leq_mul2l.
rewrite -[l.+2](addnK (delta l.+1)) addnC -deltaS.
rewrite ltn_sub2r ?orbT // [X in _ < X]deltaS //.
by rewrite addnS ltnS leq_addr.
Qed.

Lemma psi_aux_sint n : ((psi `[n])%:R)%R = psi_aux (troot n).-1 `[n].
Proof.
apply/eqP.
rewrite eq_le psi_max andbT.
case: (psiE `[n]) => l ->.
have [E|E] := leqP (troot n).-1 l.
  rewrite -(subnK E).
  elim: (_ - _) => [|k IH] //.
  apply: le_trans IH.
  rewrite addSn.
  apply: psi_aux_decr => //.
  by rewrite leq_addl.
rewrite -(subKn (ltnW E)).
elim: (_ - l) => [|k IH].
  by rewrite subn0.
apply: le_trans IH.
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
Lemma psi_sint_phi n : (psi `[n]).*2 = (phi n.+1).-1.
Proof.
have [|nP] := leqP n 0; first by case: (n)=> //; rewrite psi_sint0.
apply/eqP; rewrite -(eqr_nat int_numDomainType).
rewrite -muln2 natrM mulr_natr.
rewrite psi_aux_sint // psi_auxE_lt.
rewrite (_ : [fset _ in _ | _] = [fset i in `[n] | delta (troot n) <= i]);
   last first.
  apply/fsetP=> i; rewrite !inE; congr (_ && _).
  by rewrite prednK ?troot_gt0 // root_delta_le.
rewrite sint_sub ?delta_gt0 ?troot_gt0 // card_sint //.
rewrite (_ : \sum_(i <- _ | _) _  = phi (delta (troot n))); last first.
  rewrite phiE.
  rewrite [RHS](eq_bigl 
        (fun i : 'I_ _ => (i : nat) \in (enum_fset `[n]))); last first.
    move=> i.
    by rewrite mem_sint leq0n (leq_trans (ltn_ord _)) // delta_root_le.
  elim: enum_fset (fset_uniq `[n]) => /= [_|a l IH /andP[aNIl lU]].
    by rewrite big_nil big1.
  rewrite big_cons /= IH //; case: leqP => aLb; last first.
    rewrite prednK ?troot_gt0 // in aLb.
    apply: eq_bigl => i; rewrite inE eqn_leq [a <= i]leqNgt.
    by rewrite (leq_trans (ltn_ord i)) ?andbF // -root_delta_le.
  have aLn : a < Δ(∇n).
    by rewrite -root_delta_lt -[troot n]prednK // troot_gt0.
  rewrite [RHS](bigD1 (Ordinal aLn)) ?(inE, eqxx) //=.
  congr ((_ + _)%nat).
  apply: eq_bigl => i; rewrite inE -val_eqE /=.
  by case: (_ =P _); rewrite ?andbT // => ->; rewrite (negPf aNIl).
set m := troot n.
rewrite -[n - _]/(tmod n).
set p := tmod n.
rewrite phi_deltaE.
(* taking care of  m * 2 ^ m - 2 ^ m *)
rewrite -{2}[m]prednK ?troot_gt0 //.
rewrite mulSn addnCA [(2 ^ _ + _)%nat]addnC addnK add1n.
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

Lemma psi_sint_leq a b : a <= b -> psi `[a] <= psi `[b].
Proof.
move=> aLb; apply: psi_sub; apply/fsubsetP=> i.
by rewrite !mem_sint /= => iLa; apply: leq_trans aLb.
Qed.

Lemma psi_sintS n : (psi `[n.+1] = psi `[n] + 2 ^ (troot n.+1).-1)%nat.
Proof.
have F : 0 < phi n.+1 by apply: phi_le (_ : 1 <= _).
apply: double_inj; rewrite doubleD.
rewrite !psi_sint_phi //.
rewrite -mul2n -expnS prednK ?troot_gt0 //.
by rewrite phiE big_ord_recr -phiE prednDl.
Qed.

(* This is 2.2 *)
Lemma psi_leD a b : psi `[a + b] <= (psi `[a]).*2 + 2 ^ (b.-1).
Proof.
case: b => [|b]; first by rewrite addn0 -addnn -addnA leq_addr.
rewrite -leq_double doubleD [_.+1.-1]/=.
rewrite !psi_sint_phi -addSn -ltnS prednK ?phi_gt0 //.
apply: leq_trans (phi_leD _ _) _.
rewrite -{1}[phi (a.+1)]prednK ?phi_gt0 // doubleS.
by rewrite expnS mul2n -prednDr ?double_gt0 ?expn_gt0.
Qed.

(* This is 2.3 *)
Lemma psi_SS_le n : psi `[n.+2] >= 2 ^(troot n).+1.
Proof.
case: n => [|n]; first by rewrite psi_sint2.
have /psi_sint_leq/(leq_trans _)->// : (delta (troot n.+1)).+2 <= n.+3.
  by rewrite !ltnS -root_delta_le.
set s := troot _.
have [|tLs] := leqP s 1.
  case: s => [|[|]] //; first by rewrite psi_sint2 ?(leq_trans _ thLN).
  by rewrite psi_sint3.
rewrite -leq_double psi_sint_phi phi_modSE.
have tE : troot (delta s).+2 = s.
  by apply/eqP; rewrite trootE deltaS ltnW //= -addn2 addSnnS leq_add2l.
rewrite tE.
have->: tmod (delta s).+2 = 2 by rewrite /tmod tE -addn2 addnC addnK.
by rewrite -mul2n expnS mulnA /= leq_mul2r (leq_add2r 2 2) tLs orbT.
Qed.

Lemma psi_aux0_sint n : psi_aux 0 `[n] = n.
Proof.
rewrite /psi_aux add0n subr0.
apply/eqP; rewrite -natz eqr_nat; apply/eqP.
rewrite (eq_bigr (fun => 1)) => [|i _].
  by rewrite fsum_nat_const card_sint // subn0 muln1.
by rewrite minn0.
Qed.

(* This is 2.4.1 *)
Lemma psi_sint_min n : n <= psi `[n].
Proof.
rewrite -(ler_nat int_numDomainType).
rewrite natz -[X in (X <= _)%R]psi_aux0_sint.
by apply: psi_max.
Qed.

Lemma sum_sint (F : nat -> nat) n : 
  \sum_(i <- `[n]) F i  = \sum_(i < n) F i.
Proof.
rewrite big_seq_cond.
rewrite [LHS](eq_bigl (fun i => (i < n))); last first.
  by move=> i; rewrite mem_sint andbT.
rewrite [RHS](eq_bigl 
        (fun i : 'I_ _ => ((i : nat) \in (enum_fset `[n])))); last first.
  by move=> i; rewrite mem_sint ltn_ord.
elim: enum_fset (fset_uniq `[n]) => /= [_|a l IH /andP[aNIl lU]].
  by rewrite big_nil big1.
rewrite big_cons /= IH //; case: (boolP (a < n)) => aLn; last first.
  apply: eq_bigl => i; move: (ltn_ord i); rewrite inE; case: eqP => [->| //].
  by rewrite (negPf aLn).
rewrite [RHS](bigD1 (Ordinal aLn)) ?(inE, eqxx) //=.
congr ((_ + _)%nat).
apply: eq_bigl => i; rewrite inE -val_eqE /=.
by case: (_ =P _); rewrite ?andbT // => ->; rewrite (negPf aNIl).
Qed.

Lemma max_set_nat (e : {fset nat}) : #|`e|.-1 <= \max_(i <- e) i.
Proof.
have [n cI] := ubnP #|`e|; elim: n => // [] [|n] IH e cI in e cI *.
  by move: cI; rewrite ltnS leqn0 => /eqP->.
move: cI; rewrite leq_eqVlt => /orP[/eqP eC|]; last first.
  by apply: IH.
have /(eq_fbigmax id)[/= i [iIe iM]] : 0 < #|`e| by rewrite -ltnS eC.
have  eE : #|` e| = #|` e `\ i|.+1 by rewrite (cardfsD1 i) iIe.
have /IH H : #|`e `\ i| < n.+1 by rewrite -eE -ltnS eC.
rewrite eE /=.
case eIE : (#|` e `\ i|) => [//|k].
have /(eq_fbigmax id)[j []] : 0 < #|` e `\ i| by rewrite eIE.
rewrite !inE => /andP[jDi jIe] jM.
move: H; rewrite eIE => H.
apply: leq_ltn_trans H _; rewrite iM jM.
have : j <= i by rewrite -iM; apply: leq_bigfmax.
by rewrite leq_eqVlt (negPf jDi).
Qed.

Lemma psi_aux_card_le l e : (psi_aux l `[#|`e|] <= psi_aux l e)%R.
Proof.
rewrite ler_sub // ler_nat leq_add2l.
rewrite (sum_sint (fun i =>  2 ^ minn (∇i) l)) //.
have [n cI] := ubnP #|`e|; elim: n => // [] [|n] IH e cI in e cI *.
  by move: cI; rewrite ltnS leqn0 => /eqP-> ; rewrite big_ord0.
move: cI; rewrite leq_eqVlt => /orP[/eqP [] eC|]; last first.
  by apply: IH.
have /(eq_fbigmax id)[/= i [iIe iM]] : 0 < #|`e| by rewrite -ltnS eC.
have eE : #|` e| = #|` e `\ i|.+1 by rewrite (cardfsD1 i) iIe.
rewrite eE big_ord_recr /= (big_fsetD1 i) //= addnC.
apply: leq_add; last by apply: IH; rewrite -eC eE.
rewrite leq_exp2l // leq_min geq_minr andbT.
apply: leq_trans (geq_minl _ _) _.
apply: troot_le.
rewrite -{2}iM -ltnS -eE -[#|`_|]prednK; last by rewrite eC.
by apply: max_set_nat.
Qed.

(* This is 2.4.2 *)
Lemma psi_card_le e : psi `[#|`e|] <= psi e.
Proof.
apply: psi_aux_le_psi => l.
by apply: psi_aux_card_le.
Qed.

(* This is 2.4.3 *)
Lemma psi_exp e : psi e <= (2 ^ #|`e|).-1.
Proof.
rewrite -(ler_nat int_numDomainType).
have [l ->] := psiE e.
apply: le_trans (_ : ((2 ^ l).-1 + \sum_(i <- e) 2 ^ l)%:R - 
                      (l * 2 ^ l)%:R <= _)%R.
  apply: ler_sub => //.
  rewrite ler_nat leq_add2l.
  apply: leq_sum => i Hi.
  by rewrite leq_exp2l // geq_minr.
rewrite fsum_nat_const ler_subl_addr -natrD ler_nat [X in _ <= X]addnC.
rewrite -prednDl ?expn_gt0 // -prednDr ?expn_gt0 //.
rewrite -!subn1 leq_sub2r //.
have [E|E] := leqP #|`e| l.
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
Lemma psi_diff e1 e2 : psi e1 - psi e2 <= \sum_(i <- e1 `\` e2) 2 ^ troot i.
Proof.
rewrite leq_subLR -(ler_nat int_numDomainType) natrD addrC -ler_subl_addr.
have [l ->] := psiE e1.
apply: le_trans (ler_sub (lexx _) (psi_max _ l)) _.
rewrite /psi_aux opprB addrA subrK addnC !natrD opprD addrA addrK.
rewrite ler_subl_addr -natrD ler_nat addnC -leq_subLR.
set s1 := \sum_(_ <- _) _; set s2 := \sum_(_ <- _) _; set s3 := \sum_(_ <- _) _.
pose f i := 2 ^ minn (troot i) l.
apply: leq_trans (_ :  \sum_(i <- e1 `\` e2) f i <= _); last first.
  by apply: leq_sum => i _; rewrite leq_exp2l // geq_minl.
rewrite leq_subLR.
rewrite [s1](big_fsetID _ (fun i => i \in e2)) //=.
apply: leq_add.
  rewrite [s2](big_fsetID _ (fun i => i \in e1)) //=.
  apply: leq_trans (leq_addr _ _).
  rewrite leq_eqVlt; apply/orP; left; apply/eqP.
  by apply: eq_fbigl => i; rewrite !inE andbC.
rewrite leq_eqVlt; apply/orP; left; apply/eqP.
by apply: eq_fbigl => i; rewrite !inE andbC.
Qed.

(* This is 2.6 *)

Lemma psi_delta e s a : 
  #|` e `\` `[delta s]| <= s -> a \in e -> psi e - psi (e `\  a) <= 2 ^ s.-1.
Proof.
move=> CLs aIe.
rewrite leq_subLR -(ler_nat int_numDomainType) natrD addrC -ler_subl_addr.
have [l Hl] := psiE e.
have F l1 : s <= l1.+1 -> (psi_aux l1.+1 e <= psi_aux l1 e)%R. 
  move=> sLl1.
  rewrite psi_auxE_le.
  rewrite psi_auxE_lt.
  set s1 := \sum_(_ <- _ | _) _.
  have -> : [fset i in e | l1 < troot i] = [fset i in e | delta l1.+1 <= i].
    by apply/fsetP => i; rewrite !inE root_delta_le.
  set c := #|`_|.
  have Hc : c <= s.
    apply: leq_trans CLs.
    apply: fsubset_leq_card.
    apply/fsubsetP=> i.
    rewrite !inE => /andP[-> H].
    rewrite andbT mem_sint -leqNgt (leq_trans _ H) //.
    by apply: delta_le.
  rewrite expnS mulnAC [2 * _ * _]mulnC.
  rewrite mul2n mulnA muln2 -!addnn -[(_ + l1.+1)%N]addSnnS.
  rewrite mulnDl mulnDr prednDr ?(muln_gt0, expn_gt0) //.
  set x := 2 ^ _ * _.
  rewrite -[(_ + s1)%N]addnA [(x + _)%N]addnC.
  rewrite [X in (_ - X <= _)%R]natrD opprD addrA ler_add //.
  rewrite ler_sub_addr natrD ler_add // ler_nat.
  by rewrite mulnC leq_mul2l ltnS (leq_trans _ sLl1) ?orbT.
pose l1 := minn l s.-1.
have -> : ((psi e)%:R = psi_aux l1 e)%R.
  have [/minn_idPl U|E] := leqP l s.-1; first by rewrite [l1]U.
  have /ltnW/minn_idPr U := E.
  rewrite [l1]U.
  apply/eqP; rewrite eq_le psi_max andbT Hl.
  rewrite -(subnK (ltnW E)).
  elim: (_ - _) => [|k IH] //.
  apply: le_trans IH.
  rewrite addSn.
  apply: F => //.
  case: (s) => // s1.
  by rewrite ltnS /= leq_addl.
apply: le_trans (ler_sub (lexx _) (psi_max _ l1)) _.
rewrite /psi_aux opprB addrA subrK addnC !natrD opprD addrA addrK.
rewrite ler_subl_addr -natrD ler_nat addnC -leq_subLR.
rewrite (big_fsetD1  a) //= addnK leq_exp2l //.
by apply: leq_trans (geq_minr _ _) (geq_minr _ _).
Qed.

(* This is 2.7 *)
Lemma psi_add n s e1 e2 : 
  e1 `<=` `[n] -> n >= delta (s.-1) ->  #|`e2| <= s ->
  psi (e1 `|` e2) - psi (e1) <= psi `[n + s] - psi `[n].
Proof.
move=> e1Sn.
elim: s e2 => [e2 _|s IH e2 dLn Ce2].
  rewrite leqn0 cardfs_eq0 => /eqP->.
  by rewrite fsetU0 subnn.
have [->|[x xIe2]] := fset_0Vmem e2.
  by rewrite fsetU0 subnn.
have dLn1 : delta (s.-1) <= n.
  apply: leq_trans dLn.
  by apply: delta_le; case: (s) => // s1 /=.
pose e3 := e2 `\ x.
have Ce3 : #|` e3| <= s.
  by move: Ce2; rewrite (cardfsD1 x) xIe2 ltnS.
apply: leq_trans (leq_sub_add (psi (e1 `|` e3)) _ _) _.
rewrite addnS psi_sintS.
rewrite [X in _ <= X - _]addnC -addnBA; last first.
  by apply: psi_sint_leq; rewrite leq_addr.
apply: leq_add; last by apply: IH.
have [xIe1|xNIe1] := boolP (x \in e1).
  have -> : e1 `|` e2 = e1 `|` e3.
    apply/fsetP=> i; rewrite !inE.
    by case: eqP => // ->; rewrite xIe1.
  by rewrite subnn.
have -> : e1 `|` e3 = (e1 `|` e2) `\ x.
  apply/fsetP=> i; rewrite !inE.
  case: eqP => // ->.
  by rewrite (negPf xNIe1).
apply: psi_delta; last first.
  by rewrite !inE xIe2 orbT.
rewrite -addnS.
set t := s.+1.
set g := troot (n + t).
apply: leq_trans (_ : #|` e2 `|` (e1 `\` `[delta g])| <= _).
  apply: fsubset_leq_card.
  apply/fsubsetP=> i.
  rewrite !inE.
  by do 2 case: (_ \in _); rewrite ?(orbT, orbF).
apply: leq_trans (_ : #|` e2| + #|` e1 `\` `[delta g]| <= _).
  by rewrite -cardfsUI leq_addr.
apply: leq_trans (_ : t + #|` e1 `\` `[delta g]| <= _).
  by rewrite leq_add2r.
apply: leq_trans (_ : t + #|` sint (delta g) n| <= _).
  rewrite leq_add2l.
  apply: fsubset_leq_card.
  apply/fsubsetP=> i.
  rewrite !(inE, mem_sint) /= -leqNgt => /andP[-> /(fsubsetP e1Sn)].
  by rewrite mem_sint.
rewrite card_sint. 
have [|E] := leqP n (delta g); last first.
  rewrite addnBA; last by apply: ltnW.
  rewrite leq_subLR addnC.
  by rewrite -ltnS -!addnS -deltaS addnS -root_delta_lt.
move/eqP->; rewrite addn0.
by rewrite root_delta_le deltaS leq_add2r.
Qed.

(* This is 2.8 *)
Lemma psi_cap_ge e1 e2 : phi (#|` e1 `|` e2|.+3) <= (psi e1 + psi e2).*2.*2 + 5.
Proof.
rewrite -(ler_nat int_numDomainType) natrD.
rewrite -!muln2 !natrM !mulr_natr -mulrnA natrD.
set n := #|`_|.
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
apply: le_trans (_ : ((psi_aux l `[0] + psi_aux l `[n]) *+ 4 + 5%:R <= _))%R; 
     last first.
  rewrite ler_add2r ler_muln2r orFb.
  apply: le_trans (_ : psi_aux l e1 + psi_aux l e2 <= _)%R; last first.
    by apply: ler_add; apply: psi_max.
  apply: le_trans (_ : psi_aux l (e1 `&` e2) + psi_aux l (e1 `|` e2) <= _)%R.
    apply: ler_add; last by apply: psi_aux_card_le.
    apply: psi_aux_sub; rewrite sint0_set0.
    by apply/fsubsetP=> i; rewrite inE.
  rewrite /psi_aux.
  rewrite !natrD !addrA ler_add // -!addrA ler_add //.
  rewrite addrCA [X in (_ <= X)%R]addrCA ler_add //.
  rewrite addrCA [X in (_ <= X)%R]addrCA ler_add //.
  rewrite -!natrD ler_nat.
  rewrite [X in _ <= X + _](bigID (fun i => i \in e2)) /=.
  rewrite -!addnA leq_add //.
    rewrite leq_eqVlt; apply/orP; left; apply/eqP.
    by apply: eq_fbigl_cond => i; rewrite !inE /= andbT.
  rewrite [X in X <= _](bigID (fun i => i \in e2)) /=.
  rewrite addnC leq_add //.
    rewrite leq_eqVlt; apply/orP; left; apply/eqP.
    apply: eq_fbigl_cond => i; rewrite !inE /=.
    by case: (_ \in e2); rewrite ?(andbT, orbT, andbF, orbF).
  rewrite leq_eqVlt; apply/orP; left; apply/eqP.
  apply: eq_fbigl_cond => i; rewrite !inE /=.
  by case: (_ \in e2); rewrite /= ?(andbT, orbT, andbF, orbF).
have pE : phi (n.+3) = ((m + p - 1) * 2 ^ m).+1.
  rewrite phi_modE -/m -/p -{1 4}[m]prednK 1?ltnW //.
  rewrite [(_ + p)%N]addSn mulSn [(2 ^ _ + _)%nat]addnC addnA addnK.
  by rewrite -subn1 -[(_ + _).+1]addn1 addnK.
have pdE : ((phi (delta l))%:R = 1 + (l%:R - 1) * (2 ^ l)%:R :> int)%R.
  rewrite phi_deltaE natrB; last first.
    by case: (l) => // l1; rewrite mulSn addnCA leq_addr.
  by rewrite natrD /= mulrBl mul1r addrA -natrM.
rewrite le_eqVlt; apply/orP; left; apply/eqP.
(* right part *)
rewrite psi_aux_sintE // psi_auxE_le.
pose f i := 2 ^ minn (∇i) l.
rewrite !(big_mkord _ f) big_ord0 addn0.
have -> : [fset i in `[n] | l <= troot i] = [fset i in `[n] | delta l <= i].
  by apply/fsetP=> i; rewrite !inE root_delta_le.
have /(sint_sub n)-> : 0 <= delta l.
  by apply: (@delta_le 0).
rewrite card_sint //.
rewrite (_ : \sum_(_ <- _ | _) _  = phi (delta l)); last first.
  rewrite phiE.
  rewrite [LHS](eq_bigl (fun i => (i < n) && (∇i < l))); last first.
    move=> i; case: leqP; rewrite ?(andbT, andbF) // root_delta_lt.
    by move/(leq_trans)->.
  rewrite [RHS](eq_bigl 
        (fun i : 'I_ _ => ((i : nat) \in (enum_fset `[n])))); last first.
    by move=> i; rewrite mem_sint (leq_trans (ltn_ord _)).
  elim: enum_fset (fset_uniq `[n]) => /= [_|a l1 IH /andP[aNIl lU]].
    by rewrite big_nil big1.
  rewrite big_cons /= IH //; case: (boolP (a < n)) => aLn /=; last first.
    apply: eq_bigl => i; move: (ltn_ord i); rewrite inE; case: eqP => [->| //].
    by move=> /leq_trans/(_ nG); rewrite (negPf aLn).
  case: leqP => aLl.
    apply: eq_bigl => i; move: (ltn_ord i); rewrite inE; case: eqP => [->| //].
    by rewrite -root_delta_lt ltnNge aLl.
  rewrite root_delta_lt in aLl.
  rewrite [RHS](bigD1 (Ordinal aLl)); apply/eqP; last by rewrite inE eqxx.
  rewrite /= eqn_add2l; apply/eqP.
  apply: eq_bigl => i; rewrite !inE /= -val_eqE /=.
  by case: eqP (ltn_ord i) => [->|]; rewrite?(andbT, negPf aNIl).
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
rewrite ![in RHS](addnS, addSn) -!addnA [(delta _ + _)%nat]addnC addnK -/l.
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

Lemma phi_3_5_4_phi n : phi (n.+3) = (psi `[n.+2]).*2.+1.
Proof. by rewrite psi_sint_phi prednK ?phi_gt0. Qed.

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