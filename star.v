From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma subn_minr : left_distributive subn minn.
Proof.
move=> m n p; rewrite /minn; case: leqP => nLm.
  by rewrite ltnNge leq_sub2r.
case: (leqP n p) => nLp.
  apply/eqP; move: (nLp); rewrite -subn_eq0 => /eqP->.
  by rewrite ltnNge //= subn_eq0 (leq_trans (ltnW nLm)).
by rewrite ltn_sub2r.
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

Lemma increasingE f m n : increasing f -> m <= n -> f m <= f n.
Proof.
move=> fI mLn; rewrite -(subnK mLn).
elim: (_ - _) => //= d fL.
by apply: leq_trans (fI (d + m)).
Qed.

Definition delta (f : nat -> nat) n := f n.+1 - f n.

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

Fixpoint bigmin f n := 
 if n is n1.+1 then minn (f n) (bigmin f n1)
 else f 0.

Notation "\min_ ( i <= n ) F" := (bigmin (fun i => F) n)
 (at level 41, F at level 41, i, n at level 50,
  format " \min_ ( i  <=  n )  F ").

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

Definition conv (f g : nat -> nat) n :=
  \min_(i <= n) (f i + g (n - i)).

Lemma conv0 f g : conv f g 0 = f 0 + g 0.
Proof. by []. Qed.

Lemma conv1 f g : 
  conv f g 1 = minn (f 1 + g 0) (f 0 + g 1).
Proof. by []. Qed.

Fixpoint fmerge_aux (f g : nat -> nat) i j n := 
 if n is n1.+1 then
   if f i < g j then fmerge_aux f g i.+1 j n1 
   else fmerge_aux f g i j.+1 n1
 else minn (f i) (g j).

Definition fmerge f g n := fmerge_aux f g 0 0 n.

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

Definition alpha n := if n isn't n1.+1 then 0 else head 1 (alphal n1).

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
rewrite /alpha /=; case: n => //= n.
set h := head _ _.
have hP : 0 < h.
  rewrite /h.
  case: (alphal n) (@gt0_alphal n) => // c l /(_ c)-> //.
  by rewrite inE eqxx.
set l1 := merge _ _ _.
have hIl1 : head 1 l1 \in l1.
  have /= := alphal_neq_nil n.+1.
  rewrite -/l1; case: l1 => //= c l; first by rewrite inE eqxx.
suff hLi i :  i \in l1 -> h < i.
  apply: hLi.
  have /= := alphal_neq_nil n.+1; rewrite -/l1.
  by case: (l1) => //= c l _; rewrite inE eqxx.
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

Lemma alpha_gt0 n : 0 < alpha n.+1.
Proof. by apply: leq_ltn_trans (alpha_ltn _). Qed.

Lemma alpha_gtn_n n : n < alpha n.+1.
Proof.
by elim: n => // n IH; apply: leq_trans (alpha_ltn _).
Qed.

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

Lemma isAB_alpha n : isAB (alpha n.+1).
Proof.
rewrite /=.
case: (alphal n) (alphal_neq_nil n) 
      (@isAB_alphal n (head 1 (alphal n))) => //= c l _.
by apply; rewrite inE eqxx.
Qed.

Lemma in_alphal n i :
 i \in alphal n -> i != alpha n.+1 -> i \in alphal n.+1.
Proof.
have := alpha_gt0 n.
rewrite /= mem_merge mem_cat orbC.
case: (alphal n) => //= c l cP.
by rewrite inE => /orP[/eqP->|->//]; rewrite eqxx.
Qed.

Lemma alpha_in_alphal n : alpha n.+1 \in alphal n.
Proof.
have /= := alphal_neq_nil n.
case: alphal => //= c l.
by rewrite inE eqxx.
Qed.

Lemma in_alphalS n i :
 i \in alphal n.+1 -> 
 i != a * alpha n.+1 ->  i != b * alpha n.+1 ->
 i \in alphal n.
Proof.
rewrite /=.
set h := head _ _.
rewrite mem_merge mem_cat => /orP[]; last first.
  by case: alphal => //= c l; rewrite inE orbC => ->.
by (do 2 case: (_ \in alphal _); rewrite //= ?inE) => 
   [/eqP->|/eqP->|/orP[/eqP->|/eqP->]]; rewrite eqxx.
Qed.

Lemma a_in_alphalS n : a * alpha n.+1 \in alphal n.+1.
Proof.
have := alpha_gt0 n.
have := @in_alphal n (a * alpha n.+1).
rewrite /= mem_merge.
set h := head _ _.
have [H H1 H2|] := boolP (_ \in alphal n).
  apply: H1 => //.
  by rewrite -{2}[h]mul1n eqn_mul2r negb_or !neq_ltn H2 aL1 !orbT.
by rewrite mem_cat inE eqxx.
Qed.

Lemma b_in_alphalS n : b * alpha n.+1 \in alphal n.+1.
Proof.
have := alpha_gt0 n.
have := @in_alphal n (b * alpha n.+1).
rewrite /= mem_merge.
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
  suff F : alpha p.+1 <= q.
     move=> /(dvdn_leq F2) H.
     rewrite ltnW // (leq_trans (alpha_gtn_n _)) //.
     by rewrite (leq_trans F) // (leq_trans H) // -(prednK F2) alpha_gtn_n.
  have /= := sorted_alphal p.
  case: (alphal _) qIa => //= a1 l.
  by rewrite inE => /orP[/eqP->//|qIl /(order_path_min leq_trans) /allP/(_ _ qIl)].
exists (ex_maxn F1 F3).+1.
case: ex_maxnP => i /hasP[x xIa] Hx Fx.
have : ~~ P i.+1 by apply/negP=> /Fx; rewrite ltnn.
move/hasPn => FF.
have F4 : x = alpha i.+1.
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

Lemma alpha_leq_double i : alpha i.+2 <= a * alpha i.+1.
Proof.
apply: isAB_leq_alphaSn; first by apply/isAB_amul/isAB_alpha.
by rewrite -[X in X < _]mul1n ltn_mul2r alpha_gt0.
Qed.

Lemma isAB_geq_alphaSn i v : isAB v -> v < alpha i.+1 -> v <= alpha i.
Proof.
move => isAB; have := @isAB_leq_alphaSn i _ isAB.
by do 2 case: leqP => // _.
Qed.

Lemma sum_alpha_leq n i : 
  i <= n ->
 \sum_(1 <= i0 < n.+1) alpha i0 <=
       (a * \sum_(1 <= i0 < (n - i).+1) alpha i0) +
       \sum_(0 <= i0 < i) b ^ i0.
Proof.
move=> iLn.
rewrite big_distrr /=.
set v := n - i; set w := i; set u := n.
have {iLn}uvw : u = v + w by rewrite subnK.
rewrite -(add1n u) -(add1n v) -(add0n w).
have : (w != 0) * alpha 1 <= b ^ 0.
  by rewrite expn0; case: (w) => //= w1; rewrite ltnW.
have : (v != 0) * alpha 1 <= a * alpha 1.
  by rewrite !muln1; case: (v) => // v1; rewrite ltnW.
have : 0 < 1 by [].
have : 0 < 1 by [].
elim: {n i}u v w {-1 3}1 {4 6 10 11}1 {10 18 19}0 uvw
  => [[] [] // i j k _ iP jP _| 
                     u IH [|v] [|w] // i j k uvw iP jP aM1 aM2].
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
  case: (i) iP => // i1 _.
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
    by apply: isAB_amul; case: (j) jP => // j1 _; apply: isAB_alpha.
  by apply: leq_ltn_trans bLaa.
case: (w) => // w1.
rewrite !mul1n in aM1, aM2 |- *.
apply: isAB_leq_alphaSn (isAB_bexp _) _.
apply: leq_ltn_trans aM2 _.
by rewrite ltn_exp2l.
Qed.

Lemma b_exp_leq k n : b ^ k <= alpha n -> k < n.
Proof.
elim: n k => [k|n IH [|k Hk]//]; first by rewrite leqNgt expn_gt0 ltnW.
apply/IH/(isAB_geq_alphaSn (isAB_bexp _)).
by apply: leq_trans Hk; rewrite ltn_exp2l.
Qed.

Lemma b_exp_ltn k n : b ^ k < alpha n -> k.+1 < n.
Proof.
case: n => // n H.
rewrite ltnS.
apply: b_exp_leq.
by apply: isAB_geq_alphaSn (isAB_bexp _) _.
Qed.

Lemma alpha_b_eq n i : 
   b ^ i < alpha n.+1 < b ^ i.+1 -> alpha n.+1 = a * alpha (n - i).
Proof.
move=> /andP[beLa aLbe].
have iLm : i < n.
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
    case => [] [[|z] Hz] _ ->; rewrite dvdn_mulr //.
      by rewrite muln0; apply/mapP; exists ord0; rewrite ?mem_enum.
    set v := Ordinal _.
    have [[x1 y1] Hx1y1] : isAB (alpha v) by apply: isAB_alpha.
    case: (alpha_surjective x1.+1 y1) => t Ht.
    suff H1t : t < n.+2.
      apply/mapP; exists (Ordinal H1t); first by rewrite mem_enum.
      by rewrite Ht expnS -mulnA -Hx1y1.
    case: leqP => // /alpha_mono.
    rewrite ltnNge Hxy Ht /= !expnS -!mulnA -Hx1y1 -Hk.
    rewrite  (leq_pmul2l (ltnW aL1)).
    have : v < k.+1 by [].
    by rewrite ltnS leq_eqVlt => /orP[/eqP->|/alpha_mono/ltnW->]; rewrite // leqnn.
  rewrite andbC => /andP[/mapP[[[|u1] Hu1] _ ->] Ha].
    by exists ord0; rewrite ?mem_enum ?muln0.
  set v := Ordinal _.
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
    rewrite mem_filter andbC => /andP[/mapP[[[|j1] Hj1] _ ->] ].
      by rewrite dvdn0.
    have /alpha_mono : j1.+1 < n.+2 by [].
      case: (isAB_alpha j1) => [] [[|u1] v1]->; last first.
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
elim: n i => [i|n IH i]; first by rewrite leqNgt expn_gt0 ltnW.
rewrite leq_eqVlt => /andP[/orP[/eqP Ha Hb| Ha Hb]].
  case: i Ha Hb => [|i Ha Hb].
    case: (n) => [|n1 HH]; first by rewrite !big_ord_recr /= !big_ord0 muln0.
    have : alpha 1 < alpha n1.+2 by apply: alpha_mono.
    by rewrite -HH ltnn. 
  rewrite big_ord_recr [X in _ = _ + X]big_ord_recr Ha.
  rewrite addnA; congr (_ + _).
  rewrite subSS.
  apply: IH => //.
  rewrite Ha alpha_ltn andbT.
  apply: isAB_geq_alphaSn (isAB_bexp _) _.
  by rewrite -Ha ltn_exp2l.
rewrite subSn; last by apply/ltnW/(b_exp_ltn Ha).
rewrite big_ord_recr [X in _ = _  * X + _]big_ord_recr.
rewrite mulnDr addnAC.
congr (_ + _); last first.
  by apply: alpha_b_eq; rewrite ?Ha.
apply: IH.
rewrite (isAB_geq_alphaSn (isAB_bexp _)) //.
apply: leq_trans Hb.
by rewrite ltnS ltnW // alpha_ltn.
Qed.

Lemma sum1_alpha_eq n i : 
 b ^ i <= alpha n < b ^ i.+1 ->
\sum_(1 <= i0 < n.+1) alpha i0 =
(a * \sum_(1 <= i0 < (n - i)) alpha i0) +
 \sum_(0 <= i0 < i.+1) b ^ i0.
Proof.
move=> H.
have: \sum_(0 <= i0 < n.+1) alpha i0 =
      (a * \sum_(0 <= i0 < (n - i)) alpha i0) +
       \sum_(0 <= i0 < i.+1) b ^ i0.
  rewrite !big_mkord.
  by apply: sum_alpha_eq.
rewrite big_ltn // add0n.
rewrite (big_ltn (_ : 0 < n - i)) ?addn0 //.
rewrite subn_gt0.
by apply: b_exp_leq; case/andP: H.
Qed.

End Main.

Section S23.

Local Notation a := (alpha 2 3).

(* First 60 element of the list *)
Compute map a (iota 0 60).

Definition dsum_alpha n := 2 * \sum_(1 <= i < n.+1) a i.

Local Notation S := dsum_alpha.

Lemma dsum_alpha_0 : S 0 = 0.
Proof. by rewrite /S big_nat big1 // =>  [] []. Qed.

Lemma S_leq n i : 
i <= n -> S n <= 2 * S (n - i) + 3 ^ i - 1.
Proof.
move=> iLn.
rewrite -addnBA ?expn_gt0; last by rewrite ltnW.
rewrite subn1 predn_exp.
have <- := @big_mkord _ 0 addn i xpredT (expn 3).
rewrite mulnCA -mulnDr leq_mul2l /=.
by apply:  sum_alpha_leq.
Qed.

Lemma S_eq n i : 
 3 ^ i <= a n < 3 ^ i.+1 ->
 S n = 2 * S (n - i.+1) + 3 ^ i.+1 - 1.
Proof.
move=> iLn.
rewrite -addnBA ?expn_gt0; last by rewrite ltnW.
rewrite subn1 predn_exp.
have <- := @big_mkord _ 0 addn i.+1 xpredT (expn 3).
apply/eqP.
rewrite mulnCA -mulnDr eqn_mul2l /=.
rewrite -subSn ?subSS.
by apply/eqP/sum1_alpha_eq.
case/andP: iLn => H1 _.
by apply: b_exp_leq H1.
Qed.

End S23.
