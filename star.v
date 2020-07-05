From mathcomp Require Import all_ssreflect finmap.
From hanoi Require Import extra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

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

Lemma alpha_inj : injective alpha.
Proof.
move=> m n amEan; apply/eqP.
by case: ltngtP => // /alpha_mono; rewrite amEan ltnn.
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

Local Notation α := (alpha 2 3).

(* First 60 element of the list *)
Compute map α (iota 0 60).

Definition dsum_alpha n := \sum_(i < n) α i.

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
  by rewrite -subn1 oddB ?expn_gt0 //= odd_exp orbT.
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

Lemma leq_log3_alpha n : log3 (α n) < n.+1.
Proof.
rewrite -(ltn_exp2l _ _ (_ : 1 < 3)) //.
apply: leq_ltn_trans (leq_log3 _) _; first by apply: alpha_gt0.
by apply: alpha_exp_bound.
Qed.

Lemma S1_eq n : 0 < n -> 
  S1 n = (S1 (n - (log3 (α n.-1)).+1)).*2 + (3 ^ (log3 (α n.-1)).+1).-1./2.
Proof.
case: n => // n _.
apply: double_inj.
rewrite doubleD div2K; last first.
  by rewrite -subn1 oddB ?expn_gt0 //= odd_exp orbT.
rewrite -!mul2n predn_exp -mulnDr; congr (2 * _).
have iLn : 3 ^ (log3 (α n)) <= α n < 3 ^ (log3 (α n)).+1.
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

Lemma delta_S1 n : delta S1 n = α n.
Proof. by rewrite /S1 /delta big_ord_recr /= addnC addnK. Qed. 

Definition dsum_alphaL l :=
 conv (fun i => (S1 i).*2) (fun i => l * (3 ^ i).-1./2).

Notation " 'S_[' l ']' " := (dsum_alphaL l) 
 (format "S_[ l ]").

Definition alphaL l n := delta S_[l] n.

Notation " 'α_[' l ']' " := (alphaL l) 
 (format "α_[ l ]").

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

Lemma delta_2S1 i : delta (fun i : nat => (S1 i).*2) i = (α i).*2.
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
  try by rewrite -subn1 oddB ?expn_gt0 //= odd_exp orbT.
rewrite -predn_sub -subnS prednK ?expn_gt0 //.
by rewrite expnS -[X in _ * ((_ - X))./2]mul1n -mulnBl mul2n doubleK.
Qed.

Lemma convex_3l l : convex (fun i : nat => l * ((3 ^ i).-1)./2).
Proof.
split => [] i.
  rewrite leq_mul2l half_leq ?orbT //.
  by apply: leq_pred2; rewrite leq_exp2l.
by rewrite !delta_3l leq_mul2l leq_exp2l // leqnSn orbT.
Qed.

Lemma convex_dsum_alphaL l : convex (S_[l]).
Proof.
apply: convex_conv; first by apply: convex_2S1.
by apply: convex_3l.
Qed.

Lemma alphaLE l n : 
  α_[l] n = fmerge (fun i : nat => (α i).*2) (fun i : nat => l * 3 ^ i) n.
Proof.
rewrite [LHS]delta_conv; last by apply: convex_3l.
  apply: fmerge_ext => i; first by rewrite delta_2S1.
  by rewrite delta_3l.
by apply: convex_2S1.
Qed.

Lemma increasing_alphaL l : increasing α_[l].
Proof.
apply: increasing_ext; first by move=> i; apply/sym_equal/alphaLE.
apply: increasing_fmerge.
  by move=> n; rewrite leq_double; apply/ltnW/alpha_mono.
by move=> n; rewrite leq_mul2l leq_exp2l ?leqnSn ?orbT.
Qed.

Lemma increasing_alphaL_l n : increasing (fun l => α_[l] n).
Proof.
move=> l; rewrite !alphaLE !fmergeE //; last 4 first.
- by move=> k; rewrite leq_double; apply/ltnW/alpha_mono.
- by move=> k; rewrite leq_mul2l leq_exp2l ?leqnSn ?orbT.
- by move=> k; rewrite leq_double; apply/ltnW/alpha_mono.
- by move=> k; rewrite leq_mul2l leq_exp2l ?leqnSn ?orbT.
apply/bigmax_leqP => i _.
apply: leq_trans (_ : minn (α i).*2 (l.+1 * 3 ^ (n - i)) <= _).
  by rewrite leq_min !geq_min leqnn /= leq_mul2r leqnSn !orbT.
by apply: leq_bigmax.
Qed.

Lemma submodular_dsum_alphaL l n :
  S_[l] n.+1 + S_[l.+1] n <= S_[l] n + S_[l.+1] n.+1.
Proof.
rewrite -leq_subLR -addnBAC; last first.
  by have [daI _] := convex_dsum_alphaL l.
rewrite -[_ - _]/(α_[l] _) addnC -leq_subRL; last first.
  by have [daI _] := convex_dsum_alphaL l.+1.
 rewrite -[_ - _]/(α_[l.+1] _).
by apply: increasing_alphaL_l.
Qed.

Lemma alphaL_0 l : α_[l] 0 = minn 2 l.
Proof.
rewrite /alphaL /delta /dsum_alphaL /conv /= dsum_alpha_1 dsum_alpha_0.
by rewrite muln0 addn0 add0n subn0 muln1.
Qed.

Lemma S0E n : S_[0] n = 0.
Proof.
rewrite /dsum_alphaL /conv.
elim: n => /= [|n ->]; first by rewrite dsum_alpha_0.
by rewrite minn0.
Qed.

Lemma S1E : S_[1] =1 S1.
Proof.
case => [|i].
  by rewrite /dsum_alphaL /conv /= dsum_alpha_0.
rewrite S1_bigmin /dsum_alphaL /conv /= subnn addn0 -S1_bigmin.
rewrite (_ : \min_(_ <= _) _ = S1 i.+1).
  by rewrite (minn_idPr _) // -addnn leq_addr.
by rewrite S1_bigmin; apply: bigmin_ext => i1 i1H; rewrite mul1n.
Qed.



Lemma bound_dsum_alphaL l n : S_[l] n <= (S_[1] n).*2.
Proof.
rewrite S1E.
have [SLl|lLS] := leqP (S1 n).*2 l; first by rewrite lim_dsum_alphaL_l.
rewrite -(lim_dsum_alphaL_l (leqnn _)).
have [/increasingE H _] := concave_dsum_alphaL_l n.
by apply/H/ltnW.
Qed.

Lemma alphaL1E k : α_[1] k = α k.
Proof. by rewrite /alphaL /delta !S1E -delta_S1. Qed.


Lemma bound_alphaL l n : α_[l] n <= (α_[1] n).*2.
Proof.
rewrite alphaL1E.
have [SLl|lLS] := leqP (S1 n.+1).*2 l.
 rewrite /alphaL /delta !lim_dsum_alphaL_l //.
   by rewrite -delta_S1 doubleB.
 by apply: leq_trans SLl; case: convex_2S1.
rewrite -delta_S1 /delta doubleB.
rewrite -(lim_dsum_alphaL_l (leqnn _)).
rewrite -[(S1 n).*2](@lim_dsum_alphaL_l (S1 n.+1).*2).
  rewrite -[_ - _]/(α_[_] _).
  by apply: increasingE (increasing_alphaL_l n) _; apply: ltnW.
by case: convex_2S1.
Qed.

Lemma iotaS m n : iota m n.+1 = m :: iota m.+1 n.
Proof. by []. Qed.

Lemma count_cons (T : Type) a b (l : seq T) : count a (b :: l) = a b + count a l.
Proof. by []. Qed.


Lemma increasing_alpha : increasing α.
Proof. by move=> n; apply/ltnW/alpha_mono. Qed.

(* THis is 3.3 *)
Lemma alpha_min_exp3 m k : α m + minn (3 ^ k) (α m) <= α (m + k.+1).
Proof.
case: (leqP (α m).*2 (α (m + k.+1))) => [/(leq_trans _)-> //|amkLam].
  by rewrite -addnn leq_add2l geq_minr.
apply: leq_trans (leq_add (leqnn _) (geq_minl _ _)) _.
move: m amkLam => n; rewrite [_ + 3 ^ _]addnC.  
set m := n + k.+1.
have : k + n < m by rewrite /m addnS addnC.
move: m => m.
elim: k m n => [m n | k IH m n nkLm aL2a].
  by rewrite add0n add1n => nLm _; apply: alpha_mono.
pose l := [seq (α i) | i <- iota n (m - n).+1 & 3 %| (α i)].
have Il i : i \in l -> exists j, i = 3 * α j.
  case/mapP => j; rewrite mem_filter => /andP[ajD3 _] ->.
  have [[i1 [|j1]] /= ajE]: isAB 2 3 (α j) by apply: isAB_alpha.
    by move: ajD3; rewrite ajE muln1 Euclid_dvdX //.
  have [k1 ak1E] : {k : nat | α k = 2 ^ i1 * 3 ^ j1} by apply: alpha_surjective.
  by exists k1; rewrite ak1E ajE expnS mulnCA.
have nLm : n <= m by rewrite (leq_trans _ nkLm) // -addSn leq_addl.
have iS : k.+3 <= size (iota n (m - n).+1).
  by rewrite size_iota ltnS leq_subRL // addnC addSn.
have kLsl : k.+2 <= size l.
  rewrite size_map size_filter -ltnS -[X in _ < X]add1n.
  move: iS; rewrite -(count_predC (fun i => 3 %| (α i))) -/l => iS.
  apply: leq_trans iS _; rewrite addnC leq_add2r.
  move: aL2a; rewrite -{1}(subnK nLm) addnC.
  move: (m - n) => u.
  elim: u {k IH Il l nLm nkLm}n => [n _ /=|k IH n H]; first by case: negb.
  have /IH : α (n.+1 + k) < (α n.+1).*2.
    by rewrite addSnnS (leq_trans H) // leq_double ltnW // alpha_mono.
  rewrite (iotaS _ _.+1) count_cons.
  case: ltngtP => // [|H1 _].
    by case: count => //=; case: (~~ _).
  have /hasP[i iH1 iH2] : has (predC (fun i => 3 %| α i)) (iota n.+1 k.+1).
    by rewrite has_count H1.
  move: iH1; rewrite mem_iota => /andP[nLi iLn].
  rewrite H1; case: (boolP (predC _ _)) => //= iH3.
  have [[i1 [|j1]] /= aiE] : isAB 2 3 (α i) by apply: isAB_alpha.
    have [[i2 [|j2]] /= anE] : isAB 2 3 (α n) by apply: isAB_alpha.
      rewrite !muln1 in aiE anE.
      have : α n < α i by apply: alpha_mono.
      rewrite aiE anE ltn_exp2l // => i2Li1.
      have : (α i) < (α n).*2.
        apply: leq_trans H; rewrite ltnS -addSnnS //.
        move: iLn;rewrite addnS ltnS; case: ltngtP => // [iLS _|<-//].
        by apply/ltnW/alpha_mono.
      by rewrite aiE anE -mul2n -expnS ltn_exp2l // ltnS leqNgt i2Li1.
    by case/negP : iH3; rewrite anE expnS mulnCA dvdn_mulr.
  by case/negP : iH2; rewrite aiE expnS mulnCA dvdn_mulr.
pose n1 := head 0 l.
pose m1 := last 0 l.
have lS : sorted ltn l.
  rewrite sorted_map.
  apply: sorted_filter.
    by move=> a b c H1 H2; apply: ltn_trans H2.
  move: (_ - _).+1 => u; elim: u (n) => //= k1 IH1 n0.
  by case: (k1) (IH1 n0.+1) => //= k2 -; rewrite alpha_mono.
have uS : uniq l by move: lS; rewrite ltn_sorted_uniq_leq; case/andP.
have n1Il : n1 \in l.
  by rewrite /n1; case: (l) kLsl => [|a l1]; rewrite /= ?inE ?eqxx.
case: (Il _ n1Il) => n2 n2E.
have m1Il : m1 \in l.
  by rewrite /m1; case: (l) kLsl => [|a l1]; rewrite //= mem_last.
case: (Il _ m1Il) => m2 m2E.
have n1Lm1 : n1 < m1.
  rewrite /n1 /m1; case: (l) kLsl lS => [|a [|b l1 _]] //= /andP[].
  elim: l1 a b => //= c l1 IH1 a b aLb /andP[bLc pH].
  by apply: ltn_trans aLb (IH1 _ _ _ _).
have n2Lm2 : n2 < m2.
  move: n1Lm1; rewrite n2E m2E ltn_mul2l /=.
  case: (ltngtP n2 m2) => // [m2Ln2|->]; last by rewrite ltnn.
  by rewrite ltnNge ltnW // alpha_mono.
pose l1 := [seq 3 * α i | i <- iota n2 (m2 - n2).+1].
have l1size : size l1 = (m2 - n2).+1 by rewrite size_map size_iota.
have H : {subset l <= l1}.
  move=> i iIl; case: (Il _ iIl) => j jE.
  apply/mapP; exists j; rewrite // mem_iota addnS addnC subnK //; last first.
    by rewrite ltnW.
  rewrite ltnS; apply/andP; split.
    have: n1 <= i.
      rewrite /n1; case: (l) kLsl iIl lS => //= a l2 _.
      rewrite inE => /orP[/eqP->//|].
      elim: l2 a => //= b l2 IH1 a.
      rewrite inE => /orP[/eqP->//|bIl2] /andP[aLb pH]; first by apply: ltnW.
      apply: leq_trans (ltnW aLb) _.
      by apply: IH1.
    rewrite n2E jE leq_mul2l /=; case: (ltngtP n2 j) => // jLn2.
    by rewrite leqNgt alpha_mono.
  have: i <= m1.
    rewrite /m1; case: (l) kLsl iIl lS => //= a l2 _.
    elim: l2 a (i) => /= [a i1|b l2 IH1 a i1]; first by rewrite inE => /eqP->.
    rewrite inE => /orP[/eqP->//|bIl2] /andP[aLb pH].
      apply: leq_trans (ltnW aLb) (IH1 _ _ _ _) => //.
      by rewrite inE eqxx.
    by apply: IH1.
  rewrite m2E jE leq_mul2l /=; case: (ltngtP m2 j) => // jLn2.
  by rewrite leqNgt alpha_mono.
have kn2Lm2 : k + n2 < m2.
  rewrite -addSn addnC -leq_subRL; last by apply: ltnW.
  by rewrite -ltnS -l1size (leq_trans kLsl) // uniq_leq_size.
have anLan2 : α n <= 3 * α n2.
  rewrite -n2E.
  case/mapP : n1Il => i1.
  rewrite mem_filter mem_iota => /andP[_ /andP[nLi1 _] ->].
  by apply: (increasingE increasing_alpha).
have am2Lam : 3 * α m2 <= α m.
  rewrite -m2E.
  case/mapP : m1Il => i1.
  rewrite mem_filter mem_iota => /andP[_ /andP[_ i1Lm] ->].
  rewrite addnS ltnS addnC subnK // in i1Lm.
  by apply: (increasingE increasing_alpha).
have am2Lan2 : α m2 < (α n2).*2.
  rewrite -[_ < _]andTb -(ltn_mul2l 3) -doubleMr.
  apply: leq_ltn_trans am2Lam _.
  apply: leq_trans aL2a _.
  by rewrite leq_double.
apply: leq_trans am2Lam.
apply: leq_trans (leq_add (leqnn _) anLan2) _.
rewrite expnS -mulnDr leq_mul2l /=.
by apply: IH kn2Lm2 am2Lan2.
Qed.

Lemma alpha_min_exp3_cor m k : 3 ^k <= α m -> α m + 3 ^ k <= α (m + k.+1).
Proof.
move=> kLam.
have := alpha_min_exp3 m k.
by rewrite (minn_idPl _).
Qed.

Lemma eq_dsum_alphaL l n :
  {i : 'I_n.+1 | S_[l] n = (S1 i).*2 + l * ((3 ^ (n - i)).-1)./2}.
Proof. by apply: eq_bigmin. Qed.

Lemma increasing_dsum_alpha : increasing S1.
Proof.
by move=> n; rewrite -leq_double; case: convex_2S1.
Qed.

Lemma even_expn3_pred n : ~~ odd (3 ^ n).-1.
Proof.
by rewrite -subn1 oddB ?expn_gt0 // odd_exp orbT.
Qed.

(* This is 3.4 *)
Lemma dsum_alphaL_alpha l n : 1 < l -> S_[l.+1] n.+1 <= S_[l] n + (α_[1] n).*2.
Proof.
rewrite alphaL1E => l_gt1.
case: (eq_dsum_alphaL l n) => [] [/= m mLn] mH.
rewrite mH; rewrite ltnS in mLn.
apply: leq_trans (_ : (S1 m.+1).*2 + l.+1 * ((3 ^ (n - m)).-1)./2 <= _).
  by rewrite -subSS; apply: bigmin_inf (leqnn _).
rewrite addnAC mulSn addnA leq_add2r.
rewrite -leq_subLR -addnBAC ?leq_double ?increasing_dsum_alpha //.
rewrite [_ - _]delta_2S1.
case: ltngtP mLn => // [mLn _ |-> _]; last by rewrite subnn addn0.
apply: leq_trans (_ : (α m).*2 + (3 ^ (n - m).-1).*2 <= _).
  rewrite leq_add2l -leq_double.
  apply: leq_trans (_ : (3 ^ (n - m)).-1 <= _).
    by rewrite -[X in _ <= X]odd_double_half leq_addl.
  apply: leq_trans (ssrnat.leq_pred _) _.
  by rewrite -[n -m]prednK ?subn_gt0 // expnSr -!muln2 -mulnA leq_mul.
rewrite -doubleD leq_double.
have := @alpha_min_exp3_cor m (n - m).-1.
rewrite prednK ?subn_gt0 // [_ + (_ - _)]addnC subnK; last by apply: ltnW.
apply.
have : S_[l] n <= (S1 m.+1).*2 + l * (3 ^ (n - m.+1)).-1./2.
  by apply: bigmin_inf mLn (leqnn _).
rewrite mH (_ : S1 m.+1 = S1 m + α m); last first.
  by rewrite addnC -delta_S1 subnK // increasing_dsum_alpha.
rewrite doubleD -!addnA leq_add2l.
rewrite addnC -leq_subLR -mulnBr -[_ <= α m]leq_double.
rewrite -even_halfB ?even_expn3_pred //.
have ->: (3 ^ (n - m)).-1 - (3 ^ (n - m.+1)).-1 = (3 ^ (n - m).-1).*2.
  rewrite subnS -{1}predn_sub -subnS prednK ?expn_gt0 //.
  rewrite -{1}[(n - m)]prednK ?subn_gt0 // expnS.
  by rewrite -mul2n -{4}[2]/(3 - 1) mulnBl mul1n.
by move=> /(leq_trans _)-> //; rewrite doubleK -mul2n leq_mul2r l_gt1 orbT.
Qed.

Lemma dsum_alphal_min_3  l n :
  S_[l] n.+1 = minn (S1 n.+1).*2 (S_[3 * l] n + l).
Proof.
rewrite {1}/dsum_alphaL /conv /= subnn muln0 addn0.
congr (minn _ _).
rewrite /dsum_alphaL /conv -bigmin_constD.
apply: bigmin_ext => i iH; rewrite -addnA; congr (_ + _).
rewrite -mulnAC -{3}[l]mul1n -mulnDl mulnC; congr (_ * _).
rewrite -even_halfMl ?even_expn3_pred // -{4}[1]/(2./2).
rewrite -even_halfD ?odd_mul ?even_expn3_pred //; congr (_./2).
rewrite subSn // expnS -!subn1 mulnBr muln1 addn2 -!subSn ?subSS //.
  by rewrite ltnS -expnS (ltn_exp2l 0).
by rewrite -expnS (leq_exp2l 1).
Qed.


(* This is first part of 3.5 *)
Lemma dsum_alpha3_S n : S_[1] n.+1 = (S_[3] n).+1.
Proof.
rewrite S1E.
have := dsum_alphal_min_3 1 n.
rewrite S1E addn1 /minn; case: leqP => // _ /eqP.
rewrite -addnn -{1}[S1 _]add0n eqn_add2r.
suff : 0 < S1 n.+1 by case: S1.
rewrite -dsum_alpha_1 increasingE //.
by apply: increasing_dsum_alpha.
Qed.

Lemma alphaL_3E n : α_[3] n = α_[1] n.+1.
Proof.
by rewrite /alphaL /delta -subSS -!dsum_alpha3_S.
Qed.

(* This is second part of 3.5 *)
Lemma dsum_alpha3l l n : S_[l] n.+1 <= S_[3 * l] n + l.
Proof.
rewrite dsum_alphal_min_3.
by apply: geq_minr.
Qed.

Lemma leq_dsum_alpha_2l_l l n : S_[l] n + S_[l] n.+1 <= (S_[l.*2] n).*2 + l.
Proof.
have H := concaveEk (concave_dsum_alphaL_l n) (leq_addr l l).
rewrite addnK addnn -{1}mul2n -{3}[l]mul1n -mulnDl in H.
apply: leq_trans (leq_add H (leqnn _)).
by rewrite -addnA leq_add2l dsum_alpha3l.
Qed.

Lemma leq_dsum_alpha_2l_1 n : S_[1] n + S_[1] n.+1 <= (S_[2] n).*2.+1.
Proof. by have := leq_dsum_alpha_2l_l 1 n; rewrite addn1. Qed.


(* This is 3.7 *)
Lemma alpha_4_3 n : 3 < n -> 3 * α_[1] n.+1 <= 4 * α_[1] n.
Proof.
rewrite !alphaL1E.
move=> n_gt_3.
have an_gt_5 : 5 < α n by apply: increasingE (increasing_alpha) n_gt_3.
have [[i [|j]] /= anE] : isAB 2 3 (α n) by apply: isAB_alpha.
  rewrite muln1 in anE.
  case: i anE an_gt_5 => [|[|[|i anE an_gt_5]]]; try by move=> ->.
  suff H1 : 8 * α n.+1 <= 9 * α n.
    rewrite -3!leq_double -!mul2n !mulnA -[_ * 3]/(3 * 8).
    apply: leq_trans (_ : (3 * 9) * α n <= _).
      by rewrite -!mulnA leq_mul2l //.
    by rewrite leq_mul2r orbT.
  pose m := 2 ^ i * 3 ^ 2.
  case: (alpha_surjective (isT : 1 < 2) (isT : 2 < 3) (isT : coprime 2 3) i 2)
    => m1 m1H.
  have H2 : α n < α m1.
    by rewrite anE m1H !expnSr -!mulnA ltn_mul2l ?expn_gt0.
  have H3 : α n.+1 <= α m1.
    case: (leqP m1 n) => /(increasingE increasing_alpha) //.
    by rewrite leqNgt H2.
  rewrite anE !expnS [X in _ <= X]mulnC !mulnA -[2 * 2 * 2]/8 -mulnA leq_mul2l.
  by rewrite  -m1H.
pose m := 2 ^ i.+2 * 3 ^ j.
case: (alpha_surjective (isT : 1 < 2) (isT : 2 < 3) (isT : coprime 2 3) i.+2 j)
    => m1 m1H.
have H2 : α n < α m1.
  rewrite anE m1H !expnSr -!mulnA ltn_mul2l ?expn_gt0 //=.
  by rewrite mulnC !mulnA ltn_mul2r ?expn_gt0.
have H3 : α n.+1 <= α m1.
  case: (leqP m1 n) => /(increasingE increasing_alpha) //.
  by rewrite leqNgt H2.
by rewrite anE !expnSr -[4]/(2 ^ 2) !mulnA -expnD add2n -m1H mulnC leq_mul2r.
Qed.

Lemma alphaL_1_2 n : α_[1] (n.+1) <= (α_[1] n).*2.
Proof. 
rewrite !alphaL1E.
case: n => // [] [|[|[|]]] // k.
rewrite -(leq_pmul2l (_ : 0 < 3)) //.
rewrite -!alphaL1E.
apply: leq_trans (alpha_4_3 _) _ => //.
by rewrite -mul2n mulnA leq_mul2r orbT.
Qed.

Lemma alphaL_4_5 n : α_[1] (n.+2) <= (α_[1] n).*2.+1.
Proof. 
rewrite !alphaL1E.
case: n => // [] [|[|[|]]] // k.
rewrite -!alphaL1E.
apply: leq_trans (leqnSn _).
rewrite -(leq_pmul2l (_ : 0 < 3)) //.
apply: leq_trans (alpha_4_3 _) _ => //.
rewrite -(leq_pmul2l (_ : 0 < 3)) //.
rewrite mulnCA (leq_trans (_ : _ <= 4 * (4 *  α_[1] k.+4))) //.
  by rewrite leq_mul2l /= alpha_4_3.
by rewrite -mul2n !mulnA leq_mul2r orbT.
Qed.

Lemma dsum_alphaL_S l n : S_[l] n.+1 = S_[l] n + α_[l] n.
Proof. by rewrite addnC subnK //; case: (convex_dsum_alphaL l). Qed.

Lemma dsum_alphaLE l n : S_[l] n = \sum_(i < n) α_[l] i.
Proof.
elim: n => [|n IH].
  by rewrite /dsum_alphaL /conv /= dsum_alpha_0 muln0 big_ord0.
by rewrite dsum_alphaL_S IH big_ord_recr.
Qed.


(* Table *)

Lemma S1_small : 
  ((S_[1] 0 = 0) * (S_[1] 1 = 1) * (S_[1] 2 = 3) * (S_[1] 3 = 6) * 
  (S_[1] 4 = 10) * (S_[1] 5 = 16) * (S_[1] 6 = 24))%type.
Proof.
by rewrite /dsum_alphaL /conv /= /dsum_alpha
              -!(big_mkord xpredT) unlock /=; compute.
Qed.

Lemma S2_small : 
  ((S_[2] 0 = 0 ) * (S_[2] 1 = 2) * (S_[2] 2 = 4) * (S_[2] 3 = 8) * (
  S_[2] 4 = 14) * (S_[2] 5 = 20) * (S_[2] 6 = 28))%type.
Proof.
by rewrite /dsum_alphaL /conv /= /dsum_alpha
              -!(big_mkord xpredT) unlock /=; compute.
Qed.

Lemma S3_small : 
  ((S_[3] 0 = 0) * (S_[3] 1 = 2) * (S_[3] 2 = 5) * (S_[3] 3 = 9) * (
  S_[3] 4 = 15) * (S_[3] 5 = 23) * (S_[3] 6 = 32))%type.
Proof.
by rewrite /dsum_alphaL /conv /= /dsum_alpha
              -!(big_mkord xpredT) unlock /=; compute.
Qed.

Lemma S4_small : 
  ((S_[4] 0 = 0) * (S_[4] 1 = 2) * (S_[4] 2 = 6) * (S_[4] 3 = 10) * (
  S_[4] 4 = 16) * (S_[4] 5 = 24) * (S_[4] 6 = 36))%type.
Proof.
by rewrite /dsum_alphaL /conv /= /dsum_alpha
              -!(big_mkord xpredT) unlock /=; compute.
Qed.

Lemma S5_small : 
  ((S_[5] 0 = 0) * (S_[5] 1 = 2) * (S_[5] 2 = 6) * (S_[5] 3 = 11) * (
  S_[5] 4 = 17) * (S_[5] 5 = 25) * (S_[5] 6 = 37))%type.
Proof.
by rewrite /dsum_alphaL /conv /= /dsum_alpha
              -!(big_mkord xpredT) unlock /=; compute.
Qed.

Lemma alpha1_small : 
  ((α_[1] 0 = 1) * (α_[1] 1 = 2) * (α_[1] 2 = 3) * (α_[1] 3 = 4) * 
  (α_[1] 4 = 6) * (α_[1] 5 = 8))%type.
Proof.
by rewrite /alphaL /delta !S1_small; compute.
Qed.

Lemma alpha2_small : 
  ((α_[2] 0 = 2) * (α_[2] 1 = 2) * (α_[2] 2 = 4) * (α_[2] 3 = 6) * (
  α_[2] 4 = 6) * (α_[2] 5 = 8))%type.
Proof.
by rewrite /alphaL /delta !S2_small; compute.
Qed.

Lemma alpha3_small : 
  ((α_[3] 0 = 2) * (α_[3] 1 = 3) * (α_[3] 2 = 4) * (α_[3] 3 = 6) * (
  α_[3] 4 = 8) * (α_[3] 5 = 9))%type.
Proof.
by rewrite /alphaL /delta !S3_small; compute.
Qed.

Lemma alpha4_small : 
  ((α_[4] 0 = 2) * (α_[4] 1 = 4) * (α_[4] 2 = 4) * (α_[4] 3 = 6) * (
  α_[4] 4 = 8) * (α_[4] 5 = 12))%type.
Proof.
by rewrite /alphaL /delta !S4_small; compute.
Qed.

Lemma alpha5_small : 
  ((α_[5] 0 = 2) * (α_[5] 1 = 4) * (α_[5] 2 = 5) * (α_[5] 3 = 6) * (
  α_[5] 4 = 8) * (α_[5] 5 = 12))%type.
Proof.
by rewrite /alphaL /delta !S5_small; compute.
Qed.

Definition alphaS_small :=
   (S1_small, S2_small, S3_small, S4_small, S5_small).

Definition alpha_small :=
   (alpha1_small, alpha2_small, alpha3_small, alpha4_small, alpha5_small).

End S23.

Notation α := (alpha 2 3).

Notation "\min_ ( i <= n ) F" := (bigmin (fun i => F) n)
 (at level 41, F at level 41, i, n at level 50,
  format "\min_ ( i  <=  n )  F").

Notation " 'S_[' l ']' " := (dsum_alphaL l) 
 (format "S_[ l ]").

Notation " 'α_[' l ']' " := (alphaL l) 
 (format "α_[ l ]").

Notation S1 := dsum_alpha.
