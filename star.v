From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma subn_minr : left_distributive subn minn.
Proof.
move=> m n p; rewrite /minn; case: leqP => [nLm|mLn].
  by rewrite ltnNge leq_sub2r.
have [nLp|pLn] := leqP n p; last by rewrite ltn_sub2r.
apply/eqP; move: (nLp); rewrite -subn_eq0 => /eqP->.
by rewrite ltnNge //= subn_eq0 (leq_trans (ltnW mLn)).
Qed.

Lemma subn_maxr : left_distributive subn maxn.
Proof.
move=> m n p; rewrite /maxn; case: leqP => [nLm|mLn].
  by rewrite ltnNge leq_sub2r.
have [nLp|pLn] := leqP n p; last by rewrite ltn_sub2r.
apply/eqP; move: (nLp); rewrite -subn_eq0 => /eqP->.
by rewrite ltnNge //= eq_sym subn_eq0 (leq_trans (ltnW mLn)).
Qed.

Lemma leq_minn2r m n p : m <= n -> minn m p <= minn n p.
Proof.
move=> mLn; rewrite /minn.
case: leqP => pLm; case: leqP => //.
  by rewrite ltnNge (leq_trans pLm).
by move=> _; rewrite ltnW.
Qed.

Lemma leq_minn2l m n p : m <= n -> minn p m <= minn p n.
Proof.
move=> mLn; rewrite /minn.
case: leqP => pLm; case: leqP => //.
by move=> _; rewrite (leq_trans (ltnW pLm)).
Qed.

Section Convex.

Definition increasing (f : nat -> nat) := forall n, f n <= f n.+1.

Definition decreasing (f : nat -> nat) := forall n, f n.+1 <= f n.

Lemma increasing_ext f1 f2 : f1 =1 f2 -> increasing f1 -> increasing f2.
Proof. by move=> fE fI i; rewrite -!fE. Qed.

Lemma increasingE f m n : increasing f -> m <= n -> f m <= f n.
Proof.
move=> fI mLn; rewrite -(subnK mLn).
elim: (_ - _) => //= d fL.
by apply: leq_trans (fI (d + m)).
Qed.

Definition delta (f : nat -> nat) n := f n.+1 - f n.

Lemma delta_ext f1 f2 : f1 =1 f2 -> delta f1 =1 delta f2.
Proof. by move=> fE i; rewrite /delta !fE. Qed.

Definition fnorm (f : nat -> nat) n := f n - f 0.

Lemma increasing_fnorm f : increasing f -> increasing (fnorm f).
Proof. by move=> fI n; rewrite leq_sub2r. Qed.

Lemma delta_fnorm f n : increasing f -> delta (fnorm f) n = delta f n.
Proof.
by move=> fI; rewrite /delta /fnorm -subnDA addnC subnK // increasingE.
Qed.

Lemma sum_delta f n : 
increasing f -> fnorm f n = \sum_(i < n) delta (fnorm f) i.
Proof.
move=> iF.
elim: n => [|n IH]; first by rewrite [LHS]subnn big_ord0.
by rewrite big_ord_recr /= -IH addnC subnK // increasing_fnorm.
Qed.

(* we restrict this to increasing function because of the behavior -*)
Definition convex f :=
  increasing f /\ increasing (delta f).

(* we restrict this to increasing function because of the behavior -*)
Definition concave f :=
  increasing f /\ decreasing (delta f).

Lemma concaveE f : 
  increasing f -> (forall i, f i + f i.+2 <= (f i.+1).*2) -> concave f.
Proof.
move=> fI fH; split => // i.
rewrite /delta.
rewrite -(leq_add2r (f i.+1 + f i)) addnA subnK // addnCA subnK //.
by rewrite addnn addnC.
Qed.

Fixpoint bigmin f n := 
 if n is n1.+1 then minn (f n) (bigmin f n1)
 else f 0.

Notation "\min_ ( i <= n ) F" := (bigmin (fun i => F) n)
 (at level 41, F at level 41, i, n at level 50,
  format "\min_ ( i  <=  n )  F").

Lemma bigmin_constD  f n k :
 \min_(i <= n) (f i + k) =  (\min_(i <= n) f i) + k.
Proof. by elim: n => //=  n ->; rewrite addn_minl. Qed.

Lemma bigmin_constB  f n k :
 \min_(i <= n) (f i - k) =  (\min_(i <= n) f i) - k.
Proof. by elim: n => //=  n ->; rewrite subn_minr. Qed.

Lemma eq_bigmin f n : {i0 : 'I_n.+1 | \min_(i <= n) f i = f i0}.
Proof.
elim: n => /= [|n [i ->]]; first by exists ord0.
rewrite /minn; case: leqP => H.
  by exists (inord i); rewrite inordK // (leq_trans (ltn_ord i)).
by exists ord_max.
Qed.

Lemma bigmin_leqP f n m :
  reflect (forall i, i <= n -> m <= f i) 
          (m <= \min_(i <= n) f i).
Proof.
elim: n => /= [|n IH].
  by apply: (iffP idP) => [mLf0 [|i] //|->].
apply: (iffP idP) => [|H].
  rewrite leq_min => /andP[mLf mLmin] i.
  case: ltngtP => // [iLn _|-> _ //].
  by rewrite ltnS in iLn; move: i iLn; apply/IH.
rewrite leq_min H //=.
by apply/IH => i iLn; rewrite H // (leq_trans iLn).
Qed.

Lemma bigmin_inf f n i0 m :
  i0 <= n -> f i0 <= m -> \min_(i <= n) f i <= m.
Proof.
move=> i0Ln fi0Lm; apply: leq_trans fi0Lm.
elim: n i0Ln => /= [|n IH]; first by case: i0.
by case: ltngtP => // [i0Ln _| -> _]; rewrite geq_min ?leqnn ?IH ?orbT.
Qed.

Lemma bigmin_fnorm f n : \min_(i <= n) fnorm f i = fnorm (bigmin f) n. 
Proof. by elim: n => //= n ->; rewrite -subn_minr. Qed.

Lemma bigmin_ext f1 f2 n : f1 =1 f2 -> \min_(i <= n) f1 i = \min_(i <= n) f2 i.
Proof. by move=> fE; elim: n => //= n ->; rewrite fE. Qed.

Definition conv (f g : nat -> nat) n :=
  \min_(i <= n) (f i + g (n - i)).

Lemma conv0 f g : conv f g 0 = f 0 + g 0.
Proof. by []. Qed.

Lemma conv1 f g : 
  conv f g 1 = minn (f 1 + g 0) (f 0 + g 1).
Proof. by []. Qed.

Lemma conv_fnorm f g : 
  increasing f -> increasing g -> 
  conv (fnorm f) (fnorm g) =1 fnorm (conv f g).
Proof.
move=> fI gI i.
rewrite /fnorm /conv /= -bigmin_constB subnn.
apply: bigmin_ext => j.
by rewrite addnBA ?increasingE // addnBAC ?increasingE // subnDA.
Qed.

Lemma conv_ext f1 g1 f2 g2 : f1 =1 f2 -> g1 =1 g2 -> conv f1 g1 =1 conv f2 g2.
Proof. by move=> fE gE i; apply: bigmin_ext => j; rewrite fE gE. Qed.

Lemma convC f g : conv f g =1 conv g f.
Proof.
move=> n; apply/eqP; rewrite /conv eqn_leq; apply/andP; split.
  apply/bigmin_leqP => i iLn.
  rewrite -{1}(subKn iLn) addnC.
  by apply: bigmin_inf (leq_subr _ _) (leqnn _).
apply/bigmin_leqP => i iLn.
rewrite -{1}(subKn iLn) addnC.
by apply: bigmin_inf (leq_subr _ _) (leqnn _).
Qed.

Lemma increasing_conv f g : 
  increasing f -> increasing g -> increasing (conv f g).
Proof.
move=> fI gI i.
apply/bigmin_leqP => j.
case: ltngtP => // [jLi | ->] _.
  by apply: bigmin_inf (_ : j <= i) _; rewrite // leq_add2l subSn.
rewrite subnn.
by apply: bigmin_inf (leqnn i) _; rewrite subnn leq_add2r.
Qed.


Fixpoint fmerge_aux (f g : nat -> nat) i j n := 
 if n is n1.+1 then
   if f i < g j then fmerge_aux f g i.+1 j n1 
   else fmerge_aux f g i j.+1 n1
 else minn (f i) (g j).

Definition fmerge f g n := fmerge_aux f g 0 0 n.

Lemma fmerge_aux_ext f1 f2 g1 g2 i j : f1 =1 f2 -> g1 =1 g2 -> 
  fmerge_aux f1 g1 i j =1 fmerge_aux f2 g2 i j.
Proof.
move=> fE gE n; elim: n i j => /= [i1 j1|n IH i j]; first by rewrite fE gE.
by rewrite !(fE, gE, IH).
Qed.

Lemma fmerge_ext f1 f2 g1 g2 : f1 =1 f2 -> g1 =1 g2 -> 
  fmerge f1 g1 =1 fmerge f2 g2.
Proof. by move=> fE gE n; apply: fmerge_aux_ext. Qed.

Lemma fmerge_aux_correct f g i j n :
  increasing f -> increasing g -> 
  (forall k, k <= n ->  
     minn (f (i + k)) (g (j + (n - k))) <=  
     fmerge_aux f g i j n).
Proof.
move=> fI gI.
elim: n i j => /= [i j [|] // _|n IH i j k kLn].
  by rewrite !addn0.
case: leqP => [gLf|fLg].
  move: kLn; rewrite leq_eqVlt => /orP[/eqP->|kLn].
    rewrite subnn addn0 (minn_idPr _); last first.
      by rewrite (leq_trans gLf) // increasingE // leq_addr.
    apply: leq_trans (IH _ _ _ (leqnn _)).
    rewrite subnn addn0 leq_min increasingE // andbT (leq_trans gLf) //.
    by rewrite increasingE // leq_addr.
  by rewrite subSn // -addSnnS IH.
case: k kLn => [_ | k kLn].
  rewrite addn0 subn0 (minn_idPl _); last first.
    by rewrite (leq_trans (ltnW fLg)) // increasingE // leq_addr.
  apply: leq_trans (IH i.+1 j 0 isT).
  rewrite addn0 leq_min increasingE //= (leq_trans (ltnW fLg)) //.
  by rewrite increasingE // leq_addr.
by rewrite subSS -addSnnS IH.
Qed.

Lemma fmerge_aux_exist f g i j n :
  exists2 k, k <= n & fmerge_aux f g i j n = minn (f (i + k)) (g (j + (n - k))).
Proof.
elim: n i j => /= [i j | n IH i j]; first by exists 0; rewrite //= !addn0.
case: (leqP (g j) (f i)) => [gLf|fLg]; last first.
  by case: (IH i.+1 j) => k kLn ->; exists k.+1; rewrite // addnS subSS.
case: (IH i j.+1) => [] [|k] kLn ->.
  by exists 0; rewrite // addn0 !subn0 addnS.
by exists k.+1; rewrite ?(leq_trans kLn) // addSnnS -subSn.
Qed.

Lemma fmergeE (f g : nat -> nat) n : 
 increasing f -> increasing g ->
 fmerge f g n = \max_(i < n.+1) minn (f i) (g (n - i)).
Proof.
move=> fI gI.
apply/eqP; rewrite /fmerge eqn_leq; apply/andP; split.
  case: (@fmerge_aux_exist f g 0 0 n) => // i1 i1Ln ->.
  by apply: (@leq_bigmax_cond _ _ _ (Ordinal (i1Ln : i1 < n.+1))).
apply/bigmax_leqP => /= i _.
by apply: fmerge_aux_correct; rewrite -1?ltnS.
Qed.

Lemma increasing_fmerge f g : 
  increasing f -> increasing g -> increasing (fmerge f g).
Proof.
move=> fI gI n; rewrite !fmergeE //.
apply/bigmax_leqP => /= i _.
apply: leq_trans (leq_bigmax_cond _ (isT : xpredT (inord i : 'I_n.+2))).
rewrite inordK ?(leq_trans (ltn_ord _)) //.
rewrite leq_min geq_minl /= (leq_trans (geq_minr _ _)) //.
apply: increasingE gI _.
by rewrite leq_sub2r.
Qed.

Lemma fmerge0 f g : fmerge f g 0 = minn (f 0) (g 0).
Proof. by []. Qed.

Fixpoint sum_fmerge_aux (f g : nat -> nat) i j n := 
 if n is n1.+1 then
   if f i < g j then f i + sum_fmerge_aux f g i.+1 j n1 
   else g j + sum_fmerge_aux f g i j.+1 n1
 else minn (f i) (g j).

Definition sum_fmerge f g n := sum_fmerge_aux f g 0 0 n.

Lemma sum_fmerge_aux_correct f g n i j : 
  sum_fmerge_aux f g i j n = \sum_(k < n.+1) fmerge_aux f g i j k.
Proof.
elim: n i j => //= [i j|n IH i j]; first by rewrite big_ord_recr big_ord0.
by rewrite big_ord_recl /= /minn; case: leqP; rewrite IH.
Qed.

Lemma sum_fmerge_correct f g n : 
  sum_fmerge f g n = \sum_(k < n.+1) fmerge f g k.
Proof. by apply: sum_fmerge_aux_correct. Qed.

Lemma sum_fmerge_aux_conv_correct f g i j n :
  increasing f -> increasing g -> 
  (forall k, k <= n.+1 -> 
    sum_fmerge_aux f g i j n <= 
    \sum_(l < k) f (i + l) + \sum_(l < n.+1 - k) g (j + l)).
Proof.
move=> fI gI.
elim: n i j => /= [i j [_|[_|]]//|n IH i j k kLn].
- by rewrite big_ord_recr !big_ord0 /= !addn0 !add0n geq_minr.
- by rewrite big_ord_recr !big_ord0 /= !addn0 !add0n geq_minl.
case: leqP => [gLf|fLg].
  move: kLn; case: ltngtP => // [kLn _ |-> _]; last first.
    rewrite subnn big_ord0 addn0 big_ord_recl addn0 /=.
    apply: leq_add => //.
    rewrite /bump /=.
    apply: leq_trans (IH _ _ _ (leqnn _)) _.
    rewrite subnn big_ord0 addn0 leq_sum // => l _.
    by apply: increasingE; rewrite // addnCA leq_addl.
  rewrite subSn // big_ord_recl addn0 addnCA leq_add2l.
  apply: leq_trans (IH _ _ _ (kLn : k <= n.+1)) _.
  rewrite leq_add2l leq_sum // => l _.
  by rewrite increasingE //= /bump addnCA add1n.
move: kLn; case: ltngtP => // [kLn _ |-> _]; last first.
  rewrite subnn big_ord0 addn0 big_ord_recl addn0 /= leq_add2l /bump /=.
  apply: leq_trans (IH _ _ _ (leqnn _)) _.
  rewrite subnn big_ord0 addn0 leq_sum // => l _.
  by rewrite increasingE // addnCA add1n.
case: k kLn => [_|k kLn]; last first.
  rewrite subSS.
  apply: leq_trans (leq_add  (leqnn _) (IH i.+1 j k _)) _ .
    by rewrite -ltnS ltnW.
  rewrite addnA leq_add2r big_ord_recl addn0 leq_add2l leq_sum // => l _.
  by rewrite addnCA.
rewrite big_ord0 add0n subn0.
apply: leq_trans (leq_add  (leqnn _) (IH i.+1 j 0 isT)) _ .
rewrite big_ord0 add0n subn0 [X in _ <= X]big_ord_recr addnC leq_add //.
apply: leq_trans (ltnW fLg) _.
by rewrite increasingE // leq_addr.
Qed.

Lemma leq_sum_fmerge_conv f g k n :
  increasing f -> increasing g -> k <= n -> 
  \sum_(i < n) fmerge f g i <= \sum_(i < k) f i + \sum_(i < n - k) g i.
Proof.
move=> fI gI; case: n => [|n kLn].
  by case: k; rewrite // !big_ord0.
rewrite -sum_fmerge_correct.
exact: (sum_fmerge_aux_conv_correct 0 0 fI gI kLn).
Qed.

Lemma sum_fmerge_aux_exist f g i j n :
  exists2 k, k <= n.+1 & 
  sum_fmerge_aux f g i j n =     
  \sum_(l < k) f (i + l) + \sum_(l < n.+1 - k) g (j + l).
Proof.
elim: n i j => /= [i j | n IH i j].
  rewrite /minn; case: leqP => [gLf|fLg].
    by exists 0; rewrite // big_ord_recl !big_ord0 !(add0n, addn0).
  by exists 1; rewrite // subnn big_ord_recl !big_ord0 !(add0n, addn0).
case: (leqP (g j) (f i)) => [gLf|fLg].
  case: (IH i j.+1) => k kLn ->.
  exists k; first by apply: leq_trans kLn _.
  rewrite (subSn kLn) big_ord_recl addn0 addnCA.
  by congr (_ + (_ + _)); apply: eq_bigr => l _; rewrite addnCA.
case: (IH i.+1 j) => k kLn ->; exists k.+1; first by apply: leq_trans kLn _.
rewrite big_ord_recl addn0 subSS -addnA.
by congr (_ + (_ + _)); apply: eq_bigr => l _; rewrite addnCA.
Qed.

Lemma sum_fmerge_exist f g n :
  exists2 k, k <= n & 
  \sum_(i < n) fmerge f g i = \sum_(i < k) f i + \sum_(i < n - k) g i.
Proof.
case: n => [|n]; first by exists 0; rewrite // !big_ord0.
case: (sum_fmerge_aux_exist f g 0 0 n) => k kLn sE.
by exists k; rewrite // -sum_fmerge_correct [LHS]sE.
Qed.

Lemma sum_fmerge_conv f g n : 
  increasing f -> increasing g ->
  \sum_(i < n) (fmerge f g) i  =
     conv (fun n => \sum_(i < n) f i) (fun n => \sum_(i < n) g i) n.
Proof.
move=> fI gI.
apply/eqP; rewrite eqn_leq; apply/andP; split; last first.
  case: (sum_fmerge_exist f g n) => k kLn ->.
  by apply: (bigmin_inf _ (leqnn _)).
apply/bigmin_leqP => k kLn.
by apply: leq_sum_fmerge_conv.
Qed.

(* This is 3.2 *)
Lemma delta_conv f g : 
  convex f -> convex g -> 
  delta (conv f g) =1 fmerge (delta f) (delta g).
Proof.
move=> [fI dfI] [gI dgI] n.
rewrite -delta_fnorm; last by apply: increasing_conv.
rewrite -(delta_ext (conv_fnorm _ _)) //.
have/delta_ext-> : conv (fnorm f) (fnorm g) =1
         conv (fun n => \sum_(i < n) (delta (fnorm f)) i) 
              (fun n => \sum_(i < n) (delta (fnorm g)) i).
  by apply: conv_ext => i; apply: sum_delta.
have/delta_ext-> :
  (conv (fun n : nat => \sum_(i < n) delta (fnorm f) i)
        (fun n : nat => \sum_(i < n) delta (fnorm g) i)) =1
  (fun n => \sum_(i < n) (fmerge (delta (fnorm f)) (delta (fnorm g))) i).
  move=> k; rewrite -sum_fmerge_conv //.
    by apply: increasing_ext dfI => i; rewrite delta_fnorm.
  by apply: increasing_ext dgI => i; rewrite delta_fnorm.
rewrite /delta big_ord_recr /= addnC addnK.
by apply: fmerge_aux_ext => i; apply: delta_fnorm.
Qed.

Lemma convex_conv f g : convex f -> convex g -> convex (conv f g).
Proof.
move=> [fI dfI] [gI dgI]; split; first by apply: increasing_conv.
apply: increasing_ext => [i|]; first by apply/sym_equal/delta_conv.
by apply: increasing_fmerge.
Qed.

End Convex.

Notation "\min_ ( i <= n ) F" := (bigmin (fun i => F) n)
 (at level 41, F at level 41, i, n at level 50,
  format "\min_ ( i  <=  n )  F").

Section Main. 

Variable a b : nat.
Hypothesis aL1 : 1 < a.
Hypothesis aLb : a < b.
Hypothesis aCb : coprime a b.

Let bL1 : 1 < b.
Proof. by apply: ltn_trans aLb. Qed.

Fixpoint alphal (n : nat) :=
 if n isn't n1.+1 then [:: 1; a; b]
 else
 let l := alphal n1 in
   merge leq
   (let c := head 1 l in
    let l1 := if b * c \in l then [::] else [:: b * c] in
    if a * c \in l then l1 else a * c :: l1)
   (behead l).

Definition alpha n := head 1 (alphal n).

Lemma behead_sorted (T: eqType) (r : rel T) (l : seq T) : 
  sorted r l -> sorted r (behead l).
Proof. by case: l => //= a1 [|b1 l /andP[]]. Qed.

Lemma sorted_alphal n : sorted leq (alphal n).
Proof.
elim: n => /= [|n IH]; first by rewrite ltnW //= ltnW.
apply: merge_sorted; first by apply: leq_total.
  by do 2 case: (_ \in _) => //=; rewrite leq_mul2r orbC ltnW.
by apply: behead_sorted.
Qed.

Lemma gt0_alphal n i : i \in alphal n -> 0 < i.
Proof.
elim: n i => /= [i|n].
  by rewrite !inE => /or3P[] /eqP-> //; rewrite ltnW // (ltn_trans aL1).
case: (alphal n) => [/= _ i|/= a1 l IH i]; rewrite !inE.
  by case/orP=> /eqP->; rewrite muln1 ltnW.
have H1 : 0 < a1 by apply: IH; rewrite inE eqxx.
have IH1 i1 : i1 \in l -> 0 < i1.
  by move=> U; apply: IH; rewrite inE orbC U.
rewrite mem_merge.
(do 2 case: (_ || _)); rewrite //= ?inE; first by apply: IH1.
- by case/orP=> [/eqP->|/IH1//]; rewrite muln_gt0 ltnW.
- by case/orP=> [/eqP->|/IH1//]; rewrite muln_gt0 ltnW.
by case/or3P=> [/eqP->|/eqP->|/IH1//]; rewrite muln_gt0 ltnW.
Qed.

Lemma alphal_neq_nil n : alphal n != nil.
Proof.
case: n => //= n.
rewrite -size_eq0 size_merge.
case: (alphal n) (@gt0_alphal n) => //= c l H.
case E : (_ \in _) => //; case : (_ \in _) => //.
case: l H E aL1 => // /(_ c); rewrite !inE eqxx => /(_ is_true_true).
case: c => // c1 _.
by rewrite -{2}[_.+1]mul1n eqn_mul2r /= => /idP/eqP->.
Qed.

Lemma uniq_alphal n : uniq (alphal n).
Proof.
elim: n =>  /=[|n IH].
  by rewrite !inE negb_or !neq_ltn aL1 aLb /= (ltn_trans aL1).
case: (alphal n) (@gt0_alphal n) IH => //= [_ _|c l U /andP[cL uL]].
  by rewrite !inE !muln1 neq_ltn aLb.
(have [H1|H1] := boolP (_ \in _); have [H2|H2] := boolP (_ \in _); 
         rewrite merge_uniq); rewrite /= ?uL ?andbT //=.
- by move: H2; rewrite inE negb_or => /andP[].
- by move: H1; rewrite inE negb_or => /andP[].
move: H1 H2; rewrite !inE !negb_or => /andP[_ ->] /andP[_ ->].
by rewrite eqn_mul2r negb_or !neq_ltn aLb U ?orbT // inE eqxx.
Qed.

Lemma alpha_ltn n : alpha n < alpha n.+1.
Proof.
rewrite /alpha /=.
set h := head _ _.
have hP : 0 < h.
  rewrite /h.
  case: (alphal n) (@gt0_alphal n) => // c l /(_ c)-> //.
  by rewrite inE eqxx.
set l1 := merge _ _ _.
have hIl1 : head 1 l1 \in l1.
  have /= := alphal_neq_nil n.+1.
  by rewrite -/l1; case: l1 => //= c l; rewrite inE eqxx.
suff hLi i :  i \in l1 -> h < i.
  by apply/hLi/hIl1.
rewrite mem_merge mem_cat.
suff hLi1 : (i \in behead (alphal n)) -> h < i => [|H].
  have [H1|H1] := boolP (_ \in alphal _);
    have [H2|H2] := boolP (_ \in alphal _); rewrite /= ?inE -/h //.
  - by case/orP=> [/eqP->|//]; rewrite ltn_Pmull.
  - by case/orP=> [/eqP->|//]; rewrite ltn_Pmull.
  by rewrite -orbA => /or3P[/eqP->|/eqP->|//]; rewrite ltn_Pmull.
have hsSa : subseq [:: h; i] (alphal n).
  rewrite (_ : alphal n =  h :: behead (alphal n)).
    rewrite (@cat_subseq _ [::h] _ [::h]) //.
    by rewrite sub1seq.
  by rewrite /h; case: (alphal n) (alphal_neq_nil n).
rewrite ltn_neqAle.
have /= := subseq_sorted leq_trans hsSa (sorted_alphal n).
rewrite andbT => ->.
have /= := subseq_uniq hsSa (uniq_alphal n).
by rewrite inE.
Qed.

Lemma alpha_mono m n : m < n -> alpha m < alpha n.
Proof.
elim: n => // n IH.
have F := alpha_ltn n.
by rewrite ltnS leq_eqVlt => /orP[/eqP->| /IH /ltn_trans-> //].
Qed.

Lemma alpha_gt0 n : 0 < alpha n.
Proof. by case: n => // n; apply: leq_ltn_trans (alpha_ltn _). Qed.

Lemma alpha_gtn_n n : n < alpha n.
Proof. by elim: n => // n IH; apply: leq_trans (alpha_ltn _). Qed.

Definition isAB i := exists m, i = a ^ m.1 * b ^ m.2.

Lemma isAB_aexp i : isAB (a ^ i).
Proof. by exists (i, 0); rewrite muln1. Qed.

Lemma isAB_bexp i : isAB (b ^ i).
Proof. by exists (0, i); rewrite mul1n. Qed.

Lemma isAB_amul i : isAB i -> isAB (a * i).
Proof.
case=> [] [m1 m2 /= ->]; exists (m1.+1, m2).
by rewrite !mulnA expnS.
Qed.

Lemma isAB_bmul i : isAB  i-> isAB (b * i).
Proof.
case=> [] [m1 m2 /= ->]; exists (m1, m2.+1).
by rewrite mulnCA expnS.
Qed.

Lemma isAB_alphal n i : i \in alphal n -> isAB i.
Proof.
elim: n i => /= [i|n IH i]; rewrite ?mem_merge ?inE.
  case/or3P => /eqP->; first by exists (0, 0).
    by apply: (isAB_aexp 1).
  by apply: (isAB_bexp 1).
have F : i \in behead (alphal n) -> exists m, i = a ^ m.1 * b ^ m.2.
  by move=> U; apply: IH (mem_behead _).
have [[m1 m2 Hm]] : exists m, head 1 (alphal n) = a ^ m.1 * b ^ m.2.
  case: (alphal n) IH => /= [_|c l F1]; first by exists (0, 0).
  by apply: F1; rewrite inE eqxx.
(do 2 case: (_ \in alphal _)); rewrite /= ?inE.
- by apply: F.
rewrite /=.
- case/orP=> [/eqP->|/F//]; exists (m1, m2.+1).
  by rewrite /= Hm mulnCA expnS.
- case/orP=> [/eqP->|/F//]; exists (m1.+1, m2).
  by rewrite Hm expnS !mulnA.
case/or3P=> [/eqP->|/eqP->|//].
  by exists (m1.+1, m2); rewrite Hm expnS !mulnA.
by exists (m1, m2.+1); rewrite /= Hm mulnCA expnS.
Qed.

Lemma isAB_alpha n : isAB (alpha n).
Proof.
rewrite /alpha.
case: (alphal n) (alphal_neq_nil n) 
      (@isAB_alphal n (head 1 (alphal n))) => //= c l _.
by apply; rewrite inE eqxx.
Qed.

Lemma in_alphal n i :
 i \in alphal n -> i != alpha n -> i \in alphal n.+1.
Proof.
have := alpha_gt0 n.
rewrite  /alpha /= mem_merge mem_cat orbC.
case: (alphal n) => //= c l cP.
by rewrite inE => /orP[/eqP->|->//]; rewrite eqxx.
Qed.

Lemma alpha_in_alphal n : alpha n \in alphal n.
Proof.
have /= := alphal_neq_nil n.
rewrite /alpha; case: alphal => //= c l.
by rewrite inE eqxx.
Qed.

Lemma in_alphalS n i :
 i \in alphal n.+1 -> 
 i != a * alpha n ->  i != b * alpha n ->
 i \in alphal n.
Proof.
rewrite /alpha /=.
set h := head _ _.
rewrite mem_merge mem_cat => /orP[]; last first.
  by case: alphal => //= c l; rewrite inE orbC => ->.
by (do 2 case: (_ \in alphal _); rewrite //= ?inE) => 
   [/eqP->|/eqP->|/orP[/eqP->|/eqP->]]; rewrite eqxx.
Qed.

Lemma a_in_alphalS n : a * alpha n \in alphal n.+1.
Proof.
have := alpha_gt0 n.
have := @in_alphal n (a * alpha n).
rewrite /alpha /= mem_merge.
set h := head _ _.
have [H H1 H2|] := boolP (_ \in alphal n).
  apply: H1 => //.
  by rewrite -{2}[h]mul1n eqn_mul2r negb_or !neq_ltn H2 aL1 !orbT.
by rewrite mem_cat inE eqxx.
Qed.

Lemma b_in_alphalS n : b * alpha n \in alphal n.+1.
Proof.
have := alpha_gt0 n.
have := @in_alphal n (b * alpha n).
rewrite /alpha /= mem_merge.
set h := head _ _.
have [H H1 H2|] := boolP (b * _ \in alphal n).
  apply: H1 => //.
  by rewrite -{2}[h]mul1n eqn_mul2r negb_or !neq_ltn H2 bL1 !orbT.
by have [] := boolP (a * _ \in alphal n); rewrite mem_cat !inE eqxx // orbT.
Qed.

Lemma alpha_surjective m n : {k | alpha k = a ^ m * b ^ n}.
Proof.
pose P p := has (fun i => i %| a ^ m * b ^ n) (alphal p).
have F1 : exists n, P n.
  by exists 0; apply/hasP; exists 1.
have F2 : 0 < a ^ m *  b ^ n.
  rewrite muln_gt0 !expn_gt0 ?(ltn_trans _ aLb) (ltn_trans _ aL1) //.
have F3 p : P p -> p <= alpha (a ^ m * b ^ n).
  move=> /hasP[q] qIa.
  suff F : alpha p <= q.
     move=> /(dvdn_leq F2) H.
     rewrite ltnW // (leq_trans (alpha_gtn_n _)) //.
     by rewrite (leq_trans F) // (leq_trans H) // ltnW // alpha_gtn_n.
  have /= := sorted_alphal p; rewrite /alpha.
  case: (alphal _) qIa => //= a1 l.
  by rewrite inE => /orP[/eqP->//|qIl /(order_path_min leq_trans) /allP/(_ _ qIl)].
exists (ex_maxn F1 F3).
case: ex_maxnP => i /hasP[x xIa] Hx Fx.
have : ~~ P i.+1 by apply/negP=> /Fx; rewrite ltnn.
move/hasPn => FF.
have F4 : x = alpha i.
  by apply/eqP; case: eqP=> // /eqP /(in_alphal xIa) /FF/negP[].
case: (isAB_alpha i) => [] [m1 n1 F5].
have Cabe m2 n2 : coprime (a ^ m2) (b ^ n2).
  case: m2 => [|m2]; first by rewrite coprime1n.
  case: n2 => [|n2]; first by rewrite coprimen1.
  by rewrite coprime_pexpl // coprime_pexpr.
move: Hx.
rewrite F4 F5 Gauss_dvd //=.
rewrite Gauss_dvdl // Gauss_dvdr 1?coprime_sym // .
rewrite !dvdn_Pexp2l //.
rewrite leq_eqVlt => /andP[/orP[/eqP mEm1|H1 H2]]; last first.
  case/negP: (FF _ (a_in_alphalS _)).
  rewrite F5 /= mulnA -expnS.
  by apply: dvdn_mul; apply: dvdn_exp2l.
rewrite leq_eqVlt => /orP[/eqP nEn1 //|H1]; first by rewrite mEm1 nEn1.
case/negP: (FF _ (b_in_alphalS _)).
rewrite mulnC F5 mEm1 /= -mulnA -expnSr.
by apply: dvdn_mul; apply: dvdn_exp2l.
Qed.

Lemma isAB_leq_alphaSn i v : isAB v -> alpha i < v -> alpha i.+1 <= v.
Proof.
case=> [] [m1 m2 ->].
case: (alpha_surjective m1 m2) => j <- iLj.
case: (leqP i.+1 j) => [|H].
  by rewrite leq_eqVlt => /orP[/eqP->//|/alpha_mono/ltnW].
move: H iLj; rewrite [alpha _ < _]ltnNge.
rewrite ltnS leq_eqVlt => /orP[/eqP->//|/alpha_mono/ltnW->//].
by rewrite leqnn.
Qed.

Lemma alpha_leq_double i : alpha i.+1 <= a * alpha i.
Proof.
apply: isAB_leq_alphaSn; first by apply/isAB_amul/isAB_alpha.
by rewrite -[X in X < _]mul1n ltn_mul2r alpha_gt0.
Qed.

Lemma isAB_geq_alphaSn i v : isAB v -> v < alpha i.+1 -> v <= alpha i.
Proof.
move => isAB; have := @isAB_leq_alphaSn i _ isAB.
by do 2 case: leqP => // _.
Qed.

Lemma foo : forall u v w n n0 n1 : nat,
u = v + w ->
(v != 0) * alpha n <= a * alpha n0 ->
(w != 0) * alpha n <= b ^ n1 ->
\sum_(n <= i0 < n + u) alpha i0 <=
\sum_(n0 <= i < n0 + v) a * alpha i +
\sum_(n1 <= i0 < n1 + w) b ^ i0.
elim => [[] [] // i j k _ _| 
                     u IH [|v] [|w] // i j k uvw aM1 aM2].
- by rewrite !addn0 big_geq.
- rewrite big_ltn; last by rewrite addnS leq_addr.
  rewrite [X in _ <= _ + X]big_ltn; last by rewrite addnS leq_addr.
  rewrite addnCA.
  apply: leq_add; first by rewrite mul1n in aM2.
  rewrite -!addSnnS.
  apply: IH => //; first by case: uvw.
  case: (w) => // w1 //.
  rewrite !mul1n in aM2 |- *.
  suff /leq_trans-> : alpha i.+1 <= a * alpha i => //.
    by rewrite expnS; apply: leq_mul => //; apply: ltnW.
  by apply: alpha_leq_double.
- rewrite big_ltn; last by rewrite addnS leq_addr.
  rewrite [X in _ <= X + _]big_ltn; last by rewrite addnS leq_addr.
  rewrite -addnA.
  apply: leq_add; first by rewrite mul1n in aM1.
  rewrite -!addSnnS.
  apply: IH => //; first by case: uvw.
  case: (v) => // v1 //.
  rewrite !mul1n in aM1 |- *.
  apply: isAB_leq_alphaSn; first by apply/isAB_amul/isAB_alpha.
  apply: leq_ltn_trans aM1 _.
  by rewrite ltn_mul2l ltnW // alpha_ltn.
have aM3 : alpha i.+1 <= a * alpha j.+1.
  rewrite !mul1n in aM1.
  apply: isAB_leq_alphaSn; first by apply/isAB_amul/isAB_alpha.
  apply: leq_ltn_trans aM1 _.
  by rewrite ltn_mul2l ltnW // alpha_ltn.
case: (leqP (a * alpha j) (b ^ k)) => [|bLaa].
- rewrite leq_eqVlt => /orP[/eqP aaEb |aaLb].
  have : a %| b ^ k by rewrite -aaEb dvdn_mulr.
  move/gcdn_idPl.
  have /eqP->:= @coprime_expr k _ _ aCb.
  by case: a aL1 => // [] [].
- rewrite big_ltn; last by rewrite addnS leq_addr.
  rewrite [X in _ <= X + _]big_ltn; last by rewrite addnS leq_addr.
  rewrite -addnA.
  apply: leq_add; first by rewrite mul1n in aM1.
  rewrite -2!addSnnS.
  apply: IH => //; first by case: uvw.
    case: (v) => // v1 //.
    by rewrite !mul1n.
  rewrite !mul1n in aM1, aM2 |- *.
  apply: isAB_leq_alphaSn (isAB_bexp _) _.
  by apply: leq_ltn_trans aaLb.
rewrite big_ltn; last by rewrite addnS leq_addr.
rewrite [X in _ <= _ + X]big_ltn; last by rewrite addnS leq_addr.
rewrite addnCA.
apply: leq_add; first by rewrite mul1n in aM2.
rewrite -addSnnS -(addSnnS k).
apply: IH => //; first by move: uvw; rewrite addnS => [[]].
  rewrite !mul1n in aM1, aM2 |- *.
  apply: isAB_leq_alphaSn.
    by apply: isAB_amul; apply: isAB_alpha.
  by apply: leq_ltn_trans bLaa.
case: (w) => // w1.
rewrite !mul1n in aM1, aM2 |- *.
apply: isAB_leq_alphaSn (isAB_bexp _) _.
apply: leq_ltn_trans aM2 _.
by rewrite ltn_exp2l.
Qed.

Lemma sum_alpha_leq n i : 
  i <= n ->
 \sum_(j < n) alpha j <= (a * \sum_(j < (n - i)) alpha j) + \sum_(j < i) b ^ j.
Proof.
move=> iLn.
rewrite -!(big_mkord xpredT) big_distrr /=.
suff aux : forall u v w n n0 n1 : nat,
           u = v + w ->
          (v != 0) * alpha n <= a * alpha n0 ->
          (w != 0) * alpha n <= b ^ n1 ->
          \sum_(n <= i0 < n + u) alpha i0 <=
          \sum_(n0 <= i < n0 + v) a * alpha i +
          \sum_(n1 <= i0 < n1 + w) b ^ i0.
  rewrite -{1}[n]add0n -{1}[n - i]add0n -{2}[i]add0n.
  apply: aux => //.
  - by rewrite subnK.
  - by rewrite !muln1; apply: leq_trans aL1; case: eqP.
  by rewrite muln1; case: eqP.
elim => {i iLn}[[] [] // i j k _ _| 
                     u IH [|v] [|w] // i j k uvw aM1 aM2].
- by rewrite !addn0 big_geq.
- rewrite big_ltn; last by rewrite addnS leq_addr.
  rewrite [X in _ <= _ + X]big_ltn; last by rewrite addnS leq_addr.
  rewrite addnCA.
  apply: leq_add; first by rewrite mul1n in aM2.
  rewrite -!addSnnS.
  apply: IH => //; first by case: uvw.
  case: (w) => // w1 //.
  rewrite !mul1n in aM2 |- *.
  suff /leq_trans-> : alpha i.+1 <= a * alpha i => //.
    by rewrite expnS; apply: leq_mul => //; apply: ltnW.
  by apply: alpha_leq_double.
- rewrite big_ltn; last by rewrite addnS leq_addr.
  rewrite [X in _ <= X + _]big_ltn; last by rewrite addnS leq_addr.
  rewrite -addnA.
  apply: leq_add; first by rewrite mul1n in aM1.
  rewrite -!addSnnS.
  apply: IH => //; first by case: uvw.
  case: (v) => // v1 //.
  rewrite !mul1n in aM1 |- *.
  apply: isAB_leq_alphaSn; first by apply/isAB_amul/isAB_alpha.
  apply: leq_ltn_trans aM1 _.
  by rewrite ltn_mul2l ltnW // alpha_ltn.
have aM3 : alpha i.+1 <= a * alpha j.+1.
  rewrite !mul1n in aM1.
  apply: isAB_leq_alphaSn; first by apply/isAB_amul/isAB_alpha.
  apply: leq_ltn_trans aM1 _.
  by rewrite ltn_mul2l ltnW // alpha_ltn.
case: (leqP (a * alpha j) (b ^ k)) => [|bLaa].
- rewrite leq_eqVlt => /orP[/eqP aaEb |aaLb].
  have : a %| b ^ k by rewrite -aaEb dvdn_mulr.
  move/gcdn_idPl.
  have /eqP->:= @coprime_expr k _ _ aCb.
  by case: a aL1 => // [] [].
- rewrite big_ltn; last by rewrite addnS leq_addr.
  rewrite [X in _ <= X + _]big_ltn; last by rewrite addnS leq_addr.
  rewrite -addnA.
  apply: leq_add; first by rewrite mul1n in aM1.
  rewrite -2!addSnnS.
  apply: IH => //; first by case: uvw.
    case: (v) => // v1 //.
    by rewrite !mul1n.
  rewrite !mul1n in aM1, aM2 |- *.
  apply: isAB_leq_alphaSn (isAB_bexp _) _.
  by apply: leq_ltn_trans aaLb.
rewrite big_ltn; last by rewrite addnS leq_addr.
rewrite [X in _ <= _ + X]big_ltn; last by rewrite addnS leq_addr.
rewrite addnCA.
apply: leq_add; first by rewrite mul1n in aM2.
rewrite -addSnnS -(addSnnS k).
apply: IH => //; first by move: uvw; rewrite addnS => [[]].
  rewrite !mul1n in aM1, aM2 |- *.
  apply: isAB_leq_alphaSn.
    by apply: isAB_amul; apply: isAB_alpha.
  by apply: leq_ltn_trans bLaa.
case: (w) => // w1.
rewrite !mul1n in aM1, aM2 |- *.
apply: isAB_leq_alphaSn (isAB_bexp _) _.
apply: leq_ltn_trans aM2 _.
by rewrite ltn_exp2l.
Qed.

Lemma alpha0 : alpha 0 = 1.
Proof. by []. Qed.

Lemma alpha1 : alpha 1 = a.
Proof. 
by rewrite /alpha /= !ifT //= muln1 !inE eqxx ?orbT.
Qed.

Lemma b_exp_leq k n : b ^ k <= alpha n -> k <= n.
Proof.
elim: n k => [k|n IH [|k Hk]//].
  by rewrite -[alpha 0]/(b ^ 0) leq_exp2l.
apply/IH/(isAB_geq_alphaSn (isAB_bexp _)).
by apply: leq_trans Hk; rewrite ltn_exp2l.
Qed.

Lemma alpha_exp_bound n : alpha n < b ^ n.+1.
Proof. by rewrite ltnNge; apply/negP => /b_exp_leq; rewrite ltnn. Qed.

Lemma b_exp_ltn k n : b ^ k < alpha n -> k < n.
Proof.
case: n => [|n H]; first by rewrite ltnNge expn_gt0 (leq_trans _ bL1).
by rewrite ltnS; apply/b_exp_leq/(isAB_geq_alphaSn (isAB_bexp _)).
Qed.

Lemma alpha_b_eq n i : 
   b ^ i < alpha n.+1 < b ^ i.+1 -> alpha n.+1 = a * alpha (n - i).
Proof.
move=> /andP[beLa aLbe].
have iLm : i <= n.
  apply/b_exp_leq/isAB_geq_alphaSn => //.
  by exists (0, i); rewrite mul1n.
have [[[|x] y] Hxy] : isAB (alpha n.+1) by apply: isAB_alpha.
  move: beLa aLbe; rewrite Hxy.
  rewrite mul1n !(ltn_exp2l _ _ bL1) ltnS.
  by case: leqP.
case: (alpha_surjective x y) => k Hk.
pose la := [seq alpha (j : 'I_n.+2) | j <- enum 'I_n.+2].
pose lb := [seq b ^ (j : 'I_ i.+1) | j <- enum 'I_i.+1].
pose lc := [seq a * alpha (j : 'I_(n - i)) | j <- enum 'I_(n- i)].
have Ula : uniq la.
  rewrite map_inj_uniq; first by apply: enum_uniq.
  move=> k1 k2 H.
  case: (leqP k1 k2)=> [|/alpha_mono]; last by rewrite H ltnn.
  by rewrite leq_eqVlt => /orP[/val_eqP//|/alpha_mono]; rewrite H ltnn.
have Sla : size la = n.+2 by rewrite size_map size_enum_ord.
pose la1:= [seq x <- la | a %| x].
pose la2 := [seq x <- la | ~~ (a %| x)].
pose lk := [seq a * alpha (j : 'I_k.+1) | j <- enum 'I_k.+1].
have Slk : size lk = k.+1 by rewrite size_map size_enum_ord.
have lkEla1 : lk =i la1.
  move=> u; rewrite mem_filter.
  apply/mapP/idP.
    case => z Hz ->; rewrite dvdn_mulr //=.
    have [[x1 y1] Hx1y1] : isAB (alpha z) by apply: isAB_alpha.
    case: (alpha_surjective x1.+1 y1) => t Ht.
    suff H1t : t < n.+2.
      apply/mapP; exists (Ordinal H1t); first by rewrite mem_enum.
      by rewrite Ht expnS -mulnA -Hx1y1.
    case: leqP => // /alpha_mono.
    rewrite ltnNge Hxy Ht /= !expnS -!mulnA -Hx1y1 -Hk.
    rewrite  (leq_pmul2l (ltnW aL1)).
    have : z < k.+1 by [].
    by rewrite ltnS leq_eqVlt => /orP[/eqP->|/alpha_mono/ltnW->]; rewrite // leqnn.
  rewrite andbC => /andP[/mapP[v Hv ->] Ha].
  have [[[|x1] y1] Hx1y1] : isAB (alpha v) by apply: isAB_alpha.
    move: Ha; rewrite Hx1y1 mul1n /= => /gcdn_idPl.
    have /eqP-> : coprime a (b ^ y1) by rewrite coprime_expr.
    by move=> H; move: aL1; rewrite H ltnn.
  case: (alpha_surjective x1 y1) => j1 Hj1.
  suff H1j1 : j1 < k.+1.
    exists (Ordinal H1j1); first by rewrite mem_enum.
    by rewrite Hx1y1 expnS -mulnA Hj1.
  case: leqP => // /alpha_mono.
  rewrite  -(ltn_pmul2l (ltnW aL1)) Hk Hj1 !mulnA -!expnS -Hxy -Hx1y1.
  rewrite ltnNge isAB_geq_alphaSn //; first by apply: isAB_alpha.
  by apply: alpha_mono.
have lbEla2 : lb =i la2.
  move=> u; apply/idP/idP; last first.
    rewrite mem_filter andbC => /andP[/mapP[v Hx ->]].
    have /alpha_mono : v < n.+2 by [].
      case: (isAB_alpha v) => [] [[|u1] v1]->/=; last first.
      by rewrite expnS -mulnA dvdn_mulr.
    rewrite mul1n => H _.
    have /(ltn_pexp2l (ltnW bL1)) v1Li : b ^ v1 < b ^ i.+1.
      apply: leq_ltn_trans aLbe.
      by apply: isAB_geq_alphaSn (isAB_bexp _) _.
    by apply/mapP; exists (Ordinal v1Li); rewrite // mem_enum.
  move=> /mapP[u1 _ ->].
  rewrite mem_filter; apply/andP; split.
    apply/negP=> /gcdn_idPl.
    have /eqP-> : coprime a (b ^ u1) by rewrite coprime_expr.
    by move=> H; move: aL1; rewrite H ltnn.
   case: (alpha_surjective 0 u1) => j1; rewrite mul1n => Hj1.
  suff j1Ln : j1 < n.+2.
    by apply/mapP; exists (Ordinal j1Ln); rewrite ?mem_enum.
  case: leqP => // /alpha_mono; rewrite ltnNge => /negP[].
  apply: leq_trans (ltnW beLa).
  by rewrite Hj1 leq_exp2l // -ltnS.
rewrite Hxy expnS -mulnA -Hk.
congr (_ * alpha _).
rewrite -subSS -subSS -Sla (_ : size la = size la1 + size la2); last first.
  by rewrite !size_filter count_predC.
have : uniq la1.
  apply: filter_uniq.
  rewrite map_inj_uniq; first by apply: enum_uniq.
  move=> k1 k2 H.
  case: (leqP k1 k2)=> [|/alpha_mono]; last by rewrite H ltnn.
  by rewrite leq_eqVlt => /orP[/val_eqP//|/alpha_mono]; rewrite H ltnn.
rewrite (uniq_size_uniq _ lkEla1) => [/eqP->|]; last first.
  rewrite map_inj_uniq; first by apply: enum_uniq.
  move=> k1 k2 H.
  case: (leqP k1 k2)=> [|/alpha_mono]; last first.
    by rewrite -(ltn_pmul2l (ltnW aL1)) H ltnn.
  rewrite leq_eqVlt => /orP[/val_eqP//|/alpha_mono].
  by rewrite -(ltn_pmul2l (ltnW aL1)) H ltnn.
rewrite Slk.
have : uniq la2.
  apply: filter_uniq.
  rewrite map_inj_uniq; first by apply: enum_uniq.
  move=> k1 k2 H.
  case: (leqP k1 k2)=> [|/alpha_mono]; last by rewrite H ltnn.
  by rewrite leq_eqVlt => /orP[/val_eqP//|/alpha_mono]; rewrite H ltnn.
rewrite (uniq_size_uniq _ lbEla2) => [/eqP->|]; last first.
  rewrite map_inj_uniq; first by apply: enum_uniq.
  by move=> k1 k2 /eqP; rewrite eqn_exp2l => // /val_eqP.
rewrite size_map size_enum_ord.
by rewrite subSS addnK.
Qed.

Lemma sum_alpha_eq n i : 
 b ^ i <= alpha n < b ^ i.+1 ->
 \sum_(i0 < n.+1) alpha i0 =
  (a * \sum_(i0 < (n - i)) alpha i0) + \sum_(i0 < i.+1) b ^ i0.
Proof.
elim: n i => [i|n IH i].
  case: i => [_|i]; last by rewrite leqNgt alpha0 (ltn_exp2l 0).
  by rewrite !big_ord_recr !big_ord0 muln0.
rewrite leq_eqVlt => /andP[/orP[/eqP Ha Hb| Ha Hb]].
  case: i Ha Hb => [H|i Ha Hb].
    have : alpha 0 < alpha n.+1 by apply: alpha_mono.
    by rewrite [alpha 0]H ltnn.
  rewrite big_ord_recr [X in _ = _ + X]big_ord_recr /= Ha.
  rewrite addnA; congr (_ + _).
  rewrite subSS.
  apply: IH => //.
  rewrite Ha alpha_ltn andbT.
  apply: isAB_geq_alphaSn (isAB_bexp _) _.
  by rewrite -Ha ltn_exp2l.
rewrite subSn; last exact: b_exp_ltn Ha.
rewrite big_ord_recr [X in _ = _  * X + _]big_ord_recr.
rewrite mulnDr addnAC.
congr (_ + _); last first.
  by apply: alpha_b_eq; rewrite ?Ha.
apply: IH.
rewrite (isAB_geq_alphaSn (isAB_bexp _)) //.
apply: leq_trans Hb.
by rewrite ltnS ltnW // alpha_ltn.
Qed.

End Main.

Section S23.

Local Notation a := (alpha 2 3).

(* First 60 element of the list *)
Compute map a (iota 0 60).

Definition dsum_alpha n := \sum_(i < n) a i.

Local Notation S1 := dsum_alpha.

Lemma dsum_alpha_0 : S1 0 = 0.
Proof. by rewrite /S1 big_ord0 // =>  [] []. Qed.

Lemma dsum_alpha_1 : S1 1 = 1.
Proof. by rewrite /S1 big_ord_recr /= big_ord0. Qed.

Lemma div2K n : ~~ odd n -> n./2.*2 = n.
Proof. by move=> nO; rewrite -{2}(odd_double_half n) (negPf nO). Qed.

Lemma S1_leq n i : i <= n -> S1 n <= (S1 (n - i)).*2 + (3 ^ i).-1./2.
Proof.
move=> iLn.
rewrite -leq_double doubleD div2K; last first.
  by rewrite -subn1 odd_sub ?expn_gt0 //= odd_exp orbT.
rewrite -!mul2n predn_exp.
rewrite -mulnDr leq_mul2l /=.
by apply: sum_alpha_leq.
Qed.

Lemma log3_proof n : exists i, n  < 3 ^ i.
Proof. by exists n; apply: ltn_expl. Qed.

Definition log3 k := (ex_minn (log3_proof k)).-1.

Lemma log30 : log3 0 = 0.
Proof.
by rewrite /log3; case: ex_minnP => [] [|m] //= _ /(_ 0 isT); case: m.
Qed.

Lemma log31 : log3 1 = 0.
Proof.
by rewrite /log3; case: ex_minnP => [] [|m] //= _  /(_ 1 isT); case: m.
Qed. 

Lemma gtn_log3 n : n < 3 ^ (log3 n).+1.
Proof.
rewrite /log3; case: ex_minnP => [] [|m] //= nLm H.
by apply: leq_trans nLm _.
Qed.

Lemma leq_log3 n : 0 < n -> 3 ^ (log3 n) <= n.
Proof.
rewrite /log3; case: ex_minnP => [] [|m] //= nLm H nL.
by rewrite leqNgt; apply/negP => /H; rewrite ltnn.
Qed.

Lemma leq_log3_alpha n : log3 (a n) < n.+1.
Proof.
rewrite -(ltn_exp2l _ _ (_ : 1 < 3)) //.
apply: leq_ltn_trans (leq_log3 _) _; first by apply: alpha_gt0.
by apply: alpha_exp_bound.
Qed.

Lemma S1_eq n : 0 < n -> 
  S1 n = (S1 (n - (log3 (a n.-1)).+1)).*2 + (3 ^ (log3 (a n.-1)).+1).-1./2.
Proof.
case: n => // n _.
apply: double_inj.
rewrite doubleD div2K; last first.
  by rewrite -subn1 odd_sub ?expn_gt0 //= odd_exp orbT.
rewrite -!mul2n predn_exp -mulnDr; congr (2 * _).
have iLn : 3 ^ (log3 (a n)) <= a n < 3 ^ (log3 (a n)).+1.
  rewrite gtn_log3  leq_log3 //.
  by apply: alpha_gt0.
by apply: sum_alpha_eq.
Qed.

Lemma S1_bigmin n : 
  S1 n.+1 = \min_(i <= n) ((S1 i).*2 + (3 ^ (n.+1 - i)).-1./2).
Proof.
apply/eqP; rewrite eqn_leq; apply/andP; split; last first.
  rewrite S1_eq // -{2}(subKn (leq_log3_alpha n)).
  apply: bigmin_inf (leqnn _) => //.
  by rewrite leq_subLR addSnnS leq_addl.
apply/bigmin_leqP => i iLn.
rewrite -{1}(subKn (_ : i <= n.+1)); last by apply: ltnW.
by apply/S1_leq/leq_subr.
Qed.

Lemma delta_S1 n : delta S1 n = a n.
Proof. by rewrite /S1 /delta big_ord_recr /= addnC addnK. Qed. 

Definition dsum_alphaL l :=
 conv (fun i => (S1 i).*2) (fun i => l * (3 ^ i).-1./2).

Notation " 'S_[' l ']' " := (dsum_alphaL l) 
 (format "S_[ l ]").

Definition alphaL l n := delta S_[l] n.

Notation " 'a_[' l ']' " := (alphaL l) 
 (format "a_[ l ]").

Lemma leq_bigmin f g n :
 (forall i, i <= n -> f i <= g i) ->
 \min_(i <= n) f i <= \min_(i <= n) g i.
Proof.
elim: n => /= [->//|n IH H].
rewrite leq_min !geq_min H //= orbC IH // => i iLn.
by rewrite H // (leq_trans iLn).
Qed.

Lemma increasing_dsum_alphaL_l n : increasing (fun l => S_[l] n).
Proof.
move=> l; rewrite /increasing /dsum_alphaL /conv.
apply: leq_bigmin => i _.
by rewrite leq_add2l leq_mul2r leqnSn orbT.
Qed.

Lemma concave_dsum_alphaL_l n : concave (fun l => S_[l] n).
Proof.
apply: concaveE (increasing_dsum_alphaL_l _) _ => i.
rewrite {3}/dsum_alphaL /conv.
pose f i x := (S1 x).*2 + i * ((3 ^ (n - x)).-1)./2.
case: (eq_bigmin (f i.+1) n) => j ->.
have -> : (f i.+1 j).*2 = f i j + f (i.+2) j.
  rewrite /f; set x := (S1 _).*2; set y := _./2.
  rewrite addnCA 2![in RHS]addnA addnn -[in RHS]addnA -mulnDl.
  by rewrite -addSnnS addnn -doubleMl -doubleD.
apply: leq_add.
  by apply: bigmin_inf (leqnn _); rewrite -ltnS.
by apply: bigmin_inf (leqnn _); rewrite -ltnS.
Qed.

Lemma lim_dsum_alphaL_l l n : (S1 n).*2 <= l -> S_[l] n = (S1 n).*2.
Proof.
move=> S1Ll; apply/eqP.
rewrite /dsum_alphaL /conv eqn_leq; apply/andP; split.
  apply: bigmin_inf (_ : _ n <= _) => //.
  by rewrite subnn muln0 addn0.
apply/bigmin_leqP => i.
case: ltngtP => // [iLn _|-> _]; last apply: leq_addr.
apply: leq_trans S1Ll _.
apply: leq_trans (leq_addl _ _).
rewrite -{1}[l]muln1 leq_mul2l (half_leq (_ : 2 <= _)) ?orbT //.
by rewrite -ltnS prednK ?expn_gt0 // (@leq_exp2l _ 1) // subn_gt0.
Qed.

Lemma leq_pred m n : m <= n -> m.-1 <= n.-1.
Proof. by case: m; case: n => //=. Qed.

Lemma even_halfB m n : 
  ~~ odd m -> ~~ odd n -> (m - n)./2 = m./2 - n./2.
Proof.
move=> mE nE.
have := odd_double_half m; rewrite (negPf mE) add0n => {1}<-.
have := odd_double_half n; rewrite (negPf nE) add0n => {1}<-.
by rewrite -doubleB doubleK.
Qed.

Lemma delta_2S1 i : delta (fun i : nat => (S1 i).*2) i = (a i).*2.
Proof. by rewrite /delta -doubleB [_ - _]delta_S1. Qed.

Lemma convex_2S1 : convex (fun i : nat => (S1 i).*2).
Proof.
split => [] i.
  by rewrite leq_double /dsum_alpha [X in _ <= X]big_ord_recr leq_addr.
by rewrite !delta_2S1 leq_double; apply/ltnW/alpha_ltn.
Qed.

Lemma delta_3l l i : delta (fun i : nat => l * ((3 ^ i).-1)./2) i = l * 3 ^ i.
Proof.
rewrite /delta -mulnBr -even_halfB //;
  try by rewrite -subn1 odd_sub ?expn_gt0 //= odd_exp orbT.
rewrite -predn_sub -subnS prednK ?expn_gt0 //.
by rewrite expnS -[X in _ * ((_ - X))./2]mul1n -mulnBl mul2n doubleK.
Qed.

Lemma convex_3l l : convex (fun i : nat => l * ((3 ^ i).-1)./2).
Proof.
split => [] i.
  rewrite leq_mul2l half_leq ?orbT //.
  by apply: leq_pred; rewrite leq_exp2l.
by rewrite !delta_3l leq_mul2l leq_exp2l // leqnSn orbT.
Qed.

Lemma convex_dsum_alphaL l : convex (S_[l]).
Proof.
apply: convex_conv; first by apply: convex_2S1.
by apply: convex_3l.
Qed.

Lemma alphaLE l n : 
  a_[l] n = fmerge (fun i : nat => (a i).*2) (fun i : nat => l * 3 ^ i) n.
Proof.
rewrite [LHS]delta_conv; last by apply: convex_3l.
  apply: fmerge_ext => i; first by rewrite delta_2S1.
  by rewrite delta_3l.
by apply: convex_2S1.
Qed.

End S23.
