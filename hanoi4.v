From mathcomp Require Import all_ssreflect.
Require Import tsplit gdist ghanoi triangular phi hanoi3 psi.

Set Implicit Arguments.
Unset Strict Implicit.

Section Hanoi4.

(*****************************************************************************)
(*  The pegs are the three elements of 'I_4                                  *)
(*****************************************************************************)

Implicit Type p : peg 4.

Let peg0 : peg 4 := ord0.
Let peg1 : peg 4 := inord 1.
Let peg2 : peg 4 := inord 2.
Let peg3 : peg 4 := inord 3.


Lemma peg4E p : [\/ p = peg0, p = peg1, p = peg2 | p = peg3].
Proof.
by case: p => [] [|[|[|[|]]]] // H; 
   [apply: Or41|apply: Or42|apply: Or43|apply: Or44];
   apply/val_eqP; rewrite //= inordK.
Qed.

Ltac comp2_tac peg2 peg3 :=
 let p := fresh "p" in
 exists peg2; exists peg3; repeat split; 
      try (by apply/eqP/val_eqP; rewrite /= !inordK);
    move=> p; case: (peg4E p)=>->;
    ((by apply/Or41/val_eqP; rewrite /= ?inordK) ||
     (by apply/Or42/val_eqP; rewrite /= ?inordK) ||
     (by apply/Or43/val_eqP; rewrite /= ?inordK) ||
     (by apply/Or44/val_eqP; rewrite /= ?inordK)).
     

Lemma peg4comp2 p1 p2 :
  p1 != p2 -> exists p3, exists p4,
    [/\ [/\ p4 != p3, p4 != p2 & p4 != p1],
        [/\ p3 != p2 & p3 != p1] & 
        (forall p, [\/ p = p1, p = p2, p = p3 | p = p4])].
Proof.
case: (peg4E p1)=>->; case: (peg4E p2)=>->; rewrite ?eqxx // => _.
comp2_tac peg2 peg3. 
comp2_tac peg1 peg3.
comp2_tac peg1 peg2.
comp2_tac peg2 peg3.
comp2_tac peg0 peg3.
comp2_tac peg0 peg2.
comp2_tac peg1 peg3.
comp2_tac peg0 peg3.
comp2_tac peg0 peg1.
comp2_tac peg1 peg2.
comp2_tac peg0 peg2.
comp2_tac peg0 peg1.
Qed.

Ltac comp3_tac peg0 :=
let p := fresh "p" in
exists peg0; (repeat split) => [|||p];
     try (apply/eqP/val_eqP; rewrite /= ?inordK //);
case: (peg4E p)=>->;
    ((by apply/Or41/val_eqP; rewrite /= ?inordK) ||
     (by apply/Or42/val_eqP; rewrite /= ?inordK) ||
     (by apply/Or43/val_eqP; rewrite /= ?inordK) ||
     (by apply/Or44/val_eqP; rewrite /= ?inordK)).

Lemma peg4comp3 p1 p2 p3 :
  p1 != p2 -> p1 != p3 -> p2 != p3 -> 
  exists p4, [/\ p4 != p3, p4 != p2 & p4 != p1] /\
        (forall p, [\/ p = p1, p = p2, p = p3 | p = p4]).
Proof.
case: (peg4E p1)=>->; case: (peg4E p2)=>->; 
case: (peg4E p3)=>->; rewrite ?eqxx // => _ _ _;
(comp3_tac peg0 || comp3_tac peg1 || comp3_tac peg2 || comp3_tac peg3).
Qed.

Let hrel : rel (peg 4) := @drel 4.
Let hirr : irreflexive hrel := @dirr 4.
Let hsym : symmetric hrel := @dsym 4.

Let hmove {n} := @move 4 hrel n.
Let hmove_sym n (c1 c2 : configuration 4 n) : hmove c1 c2 = hmove c2 c1
  := move_sym hsym c1 c2.
Let hconnect n := connect (@hmove n).

Local Notation "c1 `--> c2" := (hmove c1 c2)
    (format "c1  `-->  c2", at level 60).
Local Notation "c1 `-->* c2" := (hconnect c1 c2) 
    (format "c1  `-->*  c2", at level 60).
Local Notation "`c[ p ] " := (perfect p )
    (format "`c[ p ]", at level 60).

Definition p3top4 (k : 'I_4) : peg 3 -> peg 4 := lift k.

Lemma p3to4_inj k : injective (p3top4 k).
Proof. exact: lift_inj. Qed.

Lemma gdist_leq (n : nat) (p1 p2 : peg 4) : 
 `d[`c[p1] : configuration 4 n, `c[p2]]_hmove  <= ϕ(n).
Proof.
have [/eqP->|p1Dp2] := boolP (p1 == p2); first by rewrite gdist0.
elim: {n}_.+1 {-2}n (ltnSn n) p1 p2 p1Dp2 => // n IH [_ |[_|m mLn]] p1 p2 p1Dp2.
- rewrite (_ : perfect p1 = perfect p2) ?gdist0 //.
  by apply/ffunP => [] [].
- rewrite -[phi 1]/(size [:: (@perfect 4 1 p2)]).
  apply: gdist_path_le => //=.
  rewrite andbT; apply/moveP; exists ldisk; split => //=.
  - by rewrite !ffunE.
  - by move=> [[|]].
  - by apply/on_topP => [] [].
  by apply/on_topP => [] [].
pose p3 := `p[p1, p2].
set k := gmin m.+2.
set k1 := k.-1.+1.
have kP : 0 < k by apply: gmin_gt0.
have k1Lm : k1 < m.+2 by rewrite [k1]prednK //; apply: gmin_lt.
have k1L1m : k1 <= m.+2 by apply: ltnW.
rewrite -[in X in X <= _](subnK k1L1m); set k2 := _ - _.
rewrite -perfect_liftrn; set c1 := cliftrn _ _ _.
rewrite -perfect_liftrn; set c4 := cliftrn _ _ _.
pose c2 : _ _ (k2 + k1) := cliftrn k2 p1 (perfect p3).
pose c3 : _ _ (k2 + k1) := cliftrn k2 p2 (perfect p3).
apply: leq_trans (_ : _ <= gdist hmove c1 c2 + _) _.
  by apply: gdist_triangular.
rewrite phi_gmin /g -/k -/k1 -addnn -addnA.
have kLn : k1 < n.
  by rewrite -ltnS; apply: leq_trans mLn.
apply: leq_add.
  apply: leq_trans.
    apply: gdist_merger => //.
    by apply: connect_move.
  rewrite -(prednK kP).
  apply: IH => //.
  by rewrite eq_sym opegDl.
apply: leq_trans (_ : _ <= gdist hmove c2 c3 + _) _.
  by apply: gdist_triangular.
rewrite addnC.
apply: leq_add.
  apply: leq_trans.
    apply: gdist_merger => //.
    by apply: connect_move.
  rewrite -(prednK kP).
  apply: IH => //.
  by rewrite opegDr.
rewrite /c2 /c3; move: p1Dp2.
have [p2' -> p2'E] := unlift_some (opegDr p1 p2).
rewrite -/p3.
have [p1' -> p1'E] := unlift_some (opegDl p1 p2).
move => p1Dp2.
have p1'Dp2' : p1' != p2' by apply: contra p1Dp2 => /eqP->.
rewrite -[X in _ <= X]muln1 {10}(_ : 1 = (p1' != p2')); last first.
  by rewrite (negPf p1'Dp2').
rewrite -gdist_perfect -/p3 -!crliftn_perfect -!plift_perfect.
rewrite -(prednK kP).
apply: gdist_liftln => // [i j|].
  by (apply/idP/idP; apply: contra => /eqP) => [/lift_inj->|->].
by apply: move_connect.
Qed.

Lemma trshift_lift n (i : 'I_ n) : trshift 1 i = lift ord_max i.
Proof.
apply/val_eqP=> /=.
by rewrite /bump leqNgt ltn_ord.
Qed.

Lemma split_first (A : eqType) (a : A) (l : seq A) (P : pred A) :
  P a -> ~~ all P l -> exists b, exists l1, exists l2,
    [/\ all P l1, ~~ P b &  l = l1 ++ b :: l2].
Proof.
elim: l a => //= b l IH a aP.
rewrite negb_and; case: (boolP (P b)) => /= bP lNP; last first.
  by exists b; exists nil; exists l; split.
case: (IH _ aP lNP) => c [l1 [l2 [H1 H2 ->]]].
by exists c; exists (b :: l1); exists l2; split; rewrite /= ?bP.
Qed.

Lemma split_last (A : eqType) (a : A) (l : seq A) (P : pred A) :
  P a -> ~~ all P l -> exists b, exists l1, exists l2, exists l3,
    [/\ all (fun i => ~~ P i) (b :: l2), all P l3, P (last a l1) &  
        l = l1 ++ b :: (l2 ++ l3)].
Proof.
move=> aP.
elim/last_ind : l => //= l b IH.
rewrite all_rcons negb_and orbC; case: (boolP (all P l)) => /= [lP bP|lP _].
  exists b; exists l; exists [::]; exists [::]; split; rewrite /= ?bP //.
    elim: (l) (a) aP lP => //= c l1 IH1 d dP /andP[H1 H2].
    by apply: IH1.
  by rewrite cats1.
case: (IH lP) => c [l1 [l2 [l3 [/andP[H1 H2] H3 H4 ->]]]].
case: (boolP (P b)) => /= bP; last first.
  case: l3 H3 => [|d l3] H3.
    exists c; exists l1; exists (rcons l2 b); exists [::]; split => //=.
      by rewrite H1 all_rcons H2 bP.
    by rewrite -!cats1 !cats0 -catA /=.
  exists b; exists (l1 ++ c :: l2 ++ d :: l3); exists [::]; exists [::].
  split=> //=.
  - by rewrite bP.
  - rewrite last_cat /= last_cat /=.
    apply: (allP H3).
    by apply: mem_last.
  by rewrite -!cats1 /= -catA.
exists c; exists l1; exists l2; exists (rcons l3 b); split => //.
- by rewrite H1.
- by rewrite all_rcons bP.
by rewrite -!cats1 /= -catA /= -catA.
Qed.

(* initial section of an ordinal *)
Definition isO n t := [set i | (i : 'I_n) < t].

Lemma isOE n t : isO n t = sint n 0 t.
Proof. by apply/setP => i; rewrite !inE. Qed.

Lemma mem_isO n t i : (i \in isO n t) = (i < t).
Proof. by rewrite inE. Qed.

Lemma isOE_ge n t : n <= t -> isO n t = setT.
Proof.
by move=> nLt; apply/setP => í; rewrite !inE (leq_trans _ nLt).
Qed.

Lemma isOE_le n t : t < n.+1 -> isO n.+1 t = [set inord i | i : 'I_t].
Proof.
move=> tLn; apply/setP=> i; rewrite !inE.
apply/idP/imsetP => [iLt| [j _ ->]].
  by exists (Ordinal iLt); rewrite //=; apply/val_eqP; rewrite /= inordK.
by rewrite inordK // (leq_trans _ tLn) // ltnS // ltnW.
Qed.

Lemma card_isO n t : #|isO n t| = minn n t.
Proof.
apply/sym_equal.
case: (leqP n t) => [nLt|tLn].
  rewrite isOE_ge //= cardsT card_ord.
  by apply/minn_idPl.
case: n tLn => // n tLn.
rewrite isOE_le // card_imset // => [|i j /val_eqP/eqP /=].
  by rewrite card_ord; apply/minn_idPr/ltnW.
by rewrite !inordK ?(leq_trans _ tLn) ?ltnS 1?ltnW // => /eqP/val_eqP.
Qed.

(* This is theorem 2.9 *)
Lemma phi_2_9 n (u v : configuration 4 n) (p0 p2 p3 : peg 4)
  (E := [set i | u i == p0]) : 
  [/\ p3 != p2, p3 != p0 & p2 != p0] ->
  (codom v) \subset [:: p2 ; p3] -> psi E  <= `d[u, v]_hmove.
Proof.
move=> pH.
suff H k :
 let E := [set i in isO n k | u i == p0] in 
    v @: (isO n k) \subset [:: p2 ; p3] -> psi E  <= `d[u, v]_hmove.
  have ->: E = [set i in isO n n | u i == p0].
    by apply/setP => i; rewrite !inE ltn_ord.
  suff -> : (codom v \subset [:: p2; p3]) = 
            (v @: (isO n n) \subset [:: p2; p3]) by apply: H.
  apply/subsetP/subsetP => sH i; 
      have := sH i; rewrite !inE => Hs  Hi; apply: Hs.
    by case/imsetP: Hi => j _ ->; apply: codom_f.
  case/codomP: Hi => j ->; apply/imsetP; exists j => //.
  by rewrite !inE.
elim: n u v k {E}p0 p2 p3 pH =>
    [u v k p0 p2 p3 [p3Dp2 p3Dp0 p2Dp0] E cH |
     n IH u v k p0 p2 p3 [p3Dp2 p3Dp0 p2Dp0] E cH]; first 2 last.
  suff ->: E = set0 by rewrite psi_set0.
  by apply/setP=> [] [].
have [nLk|kLn] := (leqP n.+1 k); last first.
  apply: leq_trans (gdist_cunlift (connect_move _ _)).
  pose N : disk n.+1 := ord_max.
  have->: E = E :\ N.
    apply/setP=> i; rewrite !inE.
    case: leqP=> [kLi|iLk] /=; first by rewrite andbF.
    by rewrite neq_ltn (leq_trans iLk).
  rewrite psi_ord_max.
  have -> : [set i | lift ord_max i \in E] =
            [set i in isO n k | ↓[u] i == p0].
    apply/setP => i; rewrite !inE /= !ffunE // trshift_lift.
    by rewrite /bump [n <= i]leqNgt ltn_ord.
  apply: IH.
    by split; [exact: p3Dp2 | exact: p3Dp0 | exact p2Dp0].
  apply: subset_trans cH.
  apply/subsetP => i /imsetP[j]; rewrite !inE => jLn->.
  apply/imsetP; exists (trshift 1 j); first by rewrite inE.
  by rewrite ffunE.
pose N : disk n.+1 := ord_max.
have {}cH : codom v \subset [:: p2; p3].
  apply: subset_trans cH.
  apply/subsetP=> i /codomP[j ->]; apply: mem_imset.
  by rewrite !inE (leq_trans _ nLk).
revert E.
have -> : [set i in isO n.+1 k | u i == p0] = [set i  | u i == p0].
  by apply/setP => i; rewrite !inE (leq_trans _ nLk).
move=> E.
have [NiE|NniE] := boolP (N \in E); last first.
  have->: E = E :\ N.
    apply/setP=> i; rewrite 2![in RHS]inE.
    case: eqP => // ->.
    by rewrite (negPf NniE).
  rewrite psi_ord_max.
  apply: leq_trans (gdist_cunlift (connect_move _ _)).
  have -> : [set i | lift ord_max i \in E] =
            [set i in isO n (n - 0) | ↓[u] i == p0].
    by apply/setP => i; rewrite !inE /= !ffunE // trshift_lift subn0 ltn_ord.
  apply: IH.
    by split; [exact: p3Dp2 | exact: p3Dp0 | exact p2Dp0].
  apply: subset_trans cH.
  apply/subsetP=> i /imsetP[j]; rewrite !ffunE !inE => _ ->.
  by apply: codom_f.
have uN0 : u N = p0 by move: NiE; rewrite inE => /eqP.
(* maybe I should do a wlog *)
pose np2 : peg _ := v N.
have vN2 : v N = np2 by [].
pose np3 : peg _ := if np2 == p2 then p3 else p2.
have np2Dp0 : np2 != p0.
  have /subsetP /(_  (v N)) := cH.
  by rewrite /np2 !inE => /(_ (codom_f v N))/orP[]/eqP->.
have [np3Dp0 np3Dp2] : np3 != p0 /\  np3 != np2.
  rewrite /np3; case: (_ =P p2) => [->|/eqP] => //.
  by move=> H; split => //; rewrite eq_sym.
have {}cH : codom v \subset [:: np2; np3].
  apply/subsetP=> i /(subsetP cH); rewrite /np3 /np2 !inE.
  have := subsetP cH (v N); rewrite !inE codom_f => /(_ isT) /orP[] /eqP->.
    by rewrite eqxx.
  by rewrite orbC ifN.
have uDv : u != v.
  by apply: contra_neq np2Dp0 => uE; rewrite -uN0 uE vN2.
have /gdist_path [g [gH1 gH2 gH3 gH4]] := connect_move u v.
rewrite -gH4.
have vIg : v \in g.
  by have := mem_last u g; rewrite inE gH2 eq_sym (negPf uDv).
pose E' := [set i | [exists c, (c \in (u :: g)) && (c i == np3) ]] :&: E.
have [Ez|EnZ] := boolP (E' == set0).
  pose P := [set~ np3].
  have aH : all (cvalid E P) (u :: g).
    apply/allP => c cIg; apply/cvalidP => /= i iIE.
    rewrite !inE; apply/eqP=> ciP3.
    have /eqP/setP/(_ i) := Ez.
    rewrite [in _ \in set0]inE => /idP[].
    rewrite 2!inE iIE andbT.
    by apply/existsP; exists c; rewrite cIg; apply/eqP.
  have p0Isp : p0 \in P by rewrite !inE eq_sym.
  have F pg1 pg2 : pg1 \in P -> pg2 \in P -> drel pg1 pg2 -> 
                    drel (enum_rank_in p0Isp pg1) (enum_rank_in p0Isp pg2).
    rewrite !inE /drel /= => pg1Dp3 pg2Dpg3 pg1Dpg2.
    apply: contra_neq pg1Dpg2 => /enum_rank_in_inj.
    by rewrite !inE; apply.
  apply: leq_trans (gdist_cproj F aH gH2 gH1).
  have -> : cproj E p0Isp u = `c[enum_rank_in p0Isp p0].
    apply/ffunP=> i.
    rewrite !ffunE; congr (enum_rank_in _ _).
    by have := enum_valP i; rewrite !inE => /eqP.
  have -> : cproj E p0Isp v = `c[enum_rank_in p0Isp np2].
    apply/ffunP=> i.
    rewrite !ffunE; congr (enum_rank_in _ _).
    have := subsetP cH (v (enum_val i)); rewrite !inE codom_f => /(_ isT).
    case/orP=> /eqP //.
    have /eqP/setP/(_ (enum_val i)) := Ez.
    have := enum_valP i.
    rewrite !inE => -> /idP/negP; rewrite andbT negb_exists.
    by move=> /forallP/(_ v); rewrite -{1}gH2 mem_last => /= /eqP.
  have : (enum_rank_in p0Isp p0) != (enum_rank_in p0Isp np2).
    rewrite eq_sym; apply/eqP => /enum_rank_in_inj.
    rewrite !inE eq_sym np3Dp2 eq_sym np3Dp0 => /(_ isT isT) H.
    by case/eqP: np2Dp0.
  have U : #|P| = 3.
    have := cardsC [set np3]; rewrite -/P.
    by rewrite cards1 add1n card_ord => [] [].
  move: (enum_rank_in p0Isp p0) (enum_rank_in p0Isp np2).
  rewrite U => u1 v1 u1Dv1.
  rewrite gdist_perfect (negPf u1Dv1) muln1.
  apply: psi_exp.
  rewrite -{5}[n.+1]card_ord.
  by apply: max_card.
rewrite -card_gt0 in EnZ.
case: (eq_bigmax_cond (@nat_of_ord _) EnZ) => /= T TinE' Tmax.
have {}Tmax := sym_equal Tmax.
have uT0 : u T = p0.
  by apply/eqP; move: TinE'; rewrite !inE => /andP[].
pose E'' := [set i in E | i > T].
pose K := #|E''|.
have memE'' c i  : c \in u :: g -> i \in E'' -> c i != np3.
  move=> cIug; rewrite inE => /andP[iIE].
  rewrite ltnNge Tmax; apply: contra => ciE.
  apply: leq_bigmax_cond; rewrite inE iIE andbT inE.
  by apply/existsP; exists c; rewrite cIug.
pose ST1 := isO n.+1 T.+1.
have cST1 : #|ST1| = T.+1 by rewrite card_isO; apply/minn_idPr.
(* This 3.2 *)
have KTE : T + K <= n.
  rewrite -ltnS -{2}[n.+1]card_ord -addSn.
  rewrite -[_ + _]subn0 -(_ : #|ST1 :&: E''| = 0); last first.
    apply/eqP; rewrite cards_eq0; apply/eqP/setP => i.
    rewrite /ST1 !inE; apply/idP => /and3P[].
    by rewrite ltnS leqNgt => /negPf->.
  by rewrite -cST1 -cardsU max_card.
move: TinE'.
rewrite !inE => /andP[/existsP[/= c_p3 /andP[]]].
  rewrite inE => /orP[/eqP->|]; first by rewrite uT0 eq_sym (negPf np3Dp0).
move=> c_p3Ig /eqP c_p3T3 _.
case (@split_first _ u g (fun c : configuration _ _ => c(T) == p0)) => /=.
- by rewrite uT0.
- by apply/negP => /allP /(_  _ c_p3Ig); rewrite c_p3T3 (negPf np3Dp0).
move=> x0s [x0sb [x0sa [/allP x0sbP0 x0sTD0 gE]]].
pose x0 := last u x0sb.
have x0T0 : x0 T = p0.
  by have := mem_last u x0sb; rewrite !inE /x0 => /orP[/eqP->|/x0sbP0/eqP].
have x0Mx0s : x0 `--> x0s.
  by move: gH1; rewrite gE cat_path /= -/x0 => /and3P[].
case (@split_first _ x0 (x0s :: x0sa)
                (fun c : configuration _ _ => c(T) != np3)) => /=.
- by rewrite x0T0 eq_sym.
- rewrite negb_and negbK.
  move: c_p3Ig; rewrite gE mem_cat !inE => /or3P[].
  * by move /x0sbP0; rewrite c_p3T3 (negPf np3Dp0).
  * by move/eqP<-; rewrite c_p3T3 eqxx.
  move=> cp3Ix0a; apply/orP; right; apply/negP=> /allP /(_ _ cp3Ix0a).
  by rewrite c_p3T3 eqxx.
move => x3 [x3b [x3a [/allP x3bP0 x3T3 x0xaE]]].
rewrite negbK in x3T3; have /eqP {}x3T3 := x3T3.
pose x3p := last x0 x3b.
have x3pND3 : x3p T != np3.
  have := mem_last x0 x3b; rewrite -/x3p inE => /orP[/eqP->|/x3bP0//].
  by rewrite x0T0 eq_sym.
have x3pMx3 : x3p `--> x3.
  by move: gH1; rewrite gE x0xaE cat_path /= cat_path /= => /and4P[].
case (@split_first _ u g (fun c : configuration _ _ => c(N) == p0)) => /=.
- by rewrite uN0.
- apply/negP => /allP /(_  _ vIg).
  by rewrite vN2 (negPf np2Dp0).
move=> z0s [z0sb [z0sa [/allP z0sbP0 z0sND0 gE']]].
pose z0 := last u z0sb.
have z0N0 : z0 N = p0.
  by have := mem_last u z0sb; rewrite !inE /z0 => /orP[/eqP->|/z0sbP0/eqP].
have z0Mz0s : z0 `--> z0s.
   by move: gH1; rewrite gE' cat_path /= => /and3P[].
case (@split_last _ z0 (z0s :: z0sa) 
             (fun c : configuration _ _ => c(N) != np2)) => /=.
- by rewrite z0N0 eq_sym.
- rewrite negb_and negbK.
  move: vIg; rewrite gE' mem_cat !inE => /or3P[].
  * by move /z0sbP0; rewrite vN2 (negPf np2Dp0).
  * by move/eqP<-; rewrite vN2 eqxx.
  move=> vIz0sa; apply/orP; right; apply/negP=> /allP /(_ _ vIz0sa).
  by rewrite vN2 eqxx.
move=> z2 [z2b [z2a1 [z2a2 [/andP[z2N2 /allP z2a1P2] 
                             /allP z2a2PD2 z2pND2 z0sz0saE]]]].
rewrite negbK in z2N2; have /eqP {}z2N2 := z2N2.
pose z2p := last z0 z2b.
rewrite -/z2p in z2pND2.
have z2pMz2 : z2p `--> z2.
  by move: gH1; rewrite gE' z0sz0saE cat_path /= cat_path /= => /and4P[].
(* This is 3.3 *)
have duz0_leq : psi (E :\ N) <= `d[u, z0]_hmove. 
  rewrite psi_ord_max.
  have -> : [set i | lift ord_max i \in E] =
            [set i in isO n (n - 0) | ↓[u] i == p0].
    apply/setP => i; rewrite !inE /= !ffunE // trshift_lift.
    by rewrite !subn0 ltn_ord.
  have /peg4comp2[pp2 [pp3 [[H1 H2 H3] [H4 H5] H6]]] := z0sND0.
  have cH1 : [set ↓[z0] x | x in isO n (n - 0)] \subset [::pp2; pp3].
    apply/subsetP=> i /imsetP[j _ ->].
    rewrite !inE !ffunE.
    case/moveP: z0Mz0s => d [_ z1H /on_topP dO1 /on_topP dO2].
    have dE : d = N.
      apply/eqP; move: (z1H N); case: (d =P N) => // _ /(_ isT) /eqP.
      by rewrite z0N0 eq_sym (negPf z0sND0).
    have tLd : trshift 1 j < d by rewrite dE /= ltn_ord.
    case: (H6 (z0 (trshift 1 j))) => [||->|->]; last 2 first.
    - by rewrite eqxx.
    - by rewrite eqxx orbT.
    - rewrite z1H; last by rewrite neq_ltn tLd orbT.
      by rewrite -dE => /(@sym_equal _ _ _) /dO2; first by rewrite leqNgt tLd.
    rewrite -z0N0 -dE => /(@sym_equal _ _ _) /dO1.
    by rewrite leqNgt tLd. 
  apply: leq_trans (gdist_cunlift (connect_move _ _)).
  by apply: IH cH1.
(* This is 3.4 *)
pose ST := isO n.+1 T.
have cST : #|ST| = T by rewrite card_isO; apply/minn_idPr; rewrite ltnW.
have dux0_leq : psi (E :&: ST) <= `d[u, x0]_hmove.
  have->: E :&: ST = (E :&: ST) :\ N.
    apply/setP => i; rewrite !inE /= neq_ltn /=.
    case: ltngtP; rewrite ?andbF // => iLT.
    by rewrite (leq_trans iLT _) // -ltnS. 
  rewrite psi_ord_max.
  have -> : [set i | lift ord_max i \in E :&: ST] =
            [set i in isO n T | ↓[u] i == p0].
    apply/setP => i; rewrite !inE /= !ffunE // trshift_lift.
    by rewrite  /bump [n <= i]leqNgt ltn_ord //= add0n andbC.
  have /peg4comp2[pp2 [pp3 [[H1 H2 H3] [H4 H5] H6]]] := x0sTD0.
  have cH1 : [set ↓[x0] x | x in isO n T] \subset [::pp2; pp3].
    apply/subsetP=> i /imsetP[j]; rewrite !inE !ffunE => jLT ->.
    case/moveP: x0Mx0s => d [_ z1H /on_topP dO1 /on_topP dO2].
    have dE : d = T.
      apply/eqP; move: (z1H T); case: (d =P T) => // _ /(_ isT) /eqP.
      by rewrite x0T0 eq_sym (negPf x0sTD0).
    case: (H6 (x0 (trshift 1 j))) => [||->|->]; last 2 first.
    - by rewrite eqxx.
    - by rewrite eqxx orbT.
    - rewrite z1H; last by rewrite neq_ltn /= dE jLT orbT.
      by rewrite -dE => /(@sym_equal _ _ _) /dO2; rewrite leqNgt dE jLT.
    by rewrite -x0T0 -dE => /(@sym_equal _ _ _) /dO1; rewrite leqNgt dE jLT.
  apply: leq_trans (gdist_cunlift (connect_move _ _)).
  by apply: IH cH1.
have [KLT|TLK] := leqP (delta K) T; last first.
  have K_gt0 : 0 < K by case: (K) TLK.
  have TLN : T < N by apply: leq_trans KTE; rewrite -addn1 leq_add2l.
  (* This is 3. 5 *)
  have psiDN : psi E - psi (E :\ N) <= 2 ^ K.-1. 
    apply: psi_delta => //.
    apply: subset_leq_card.
    apply/subsetP=> i; rewrite !inE andTb -leqNgt.
    case: (_ == _); rewrite /= !(andbT, andbF) // => KLi.
    by apply: leq_trans KLi.
  rewrite gE' in gH1 gH2 gH4 |- *.
  have gH5 : size (z0s :: z0sa) =  `d[z0, v]_hmove.
    by rewrite (gdist_catr gH4) //.
  rewrite size_cat (gdist_catl gH4) // -/z0.
  rewrite cat_path in gH1; have /andP[_ {}gH1] := gH1.
  rewrite {gH4}last_cat in gH2.
  rewrite z0sz0saE in gH1, gH2, gH5 |- *.
  have gH6 : size (z2 :: z2a1 ++ z2a2) = `d[last z0 z2b, v]_hmove.
    rewrite (gdist_catr gH5) //.
  rewrite size_cat (gdist_catl gH5) //=.
  rewrite last_cat in gH2.
  move: gH1; rewrite cat_path => /andP[_ {}gH1].
  have gH7 : size (z2a1 ++ z2a2) = `d[z2, v]_hmove.
    by apply: gdist_cons gH6 _ _.
  apply: leq_trans (leq_add duz0_leq (leqnn _)).
  rewrite addnCA gH7.
  apply: leq_trans (leq_addl _ _).
  rewrite -[psi E](@subnK (psi (E :\ N))) 1?addnC ?leq_add2l; last first.
    by apply/psi_sub/subD1set.
  apply: leq_trans psiDN _.
  rewrite -[_ ^ _]prednK ?expn_gt0 // ltnS.
  pose P := [set~ np3].
  have aH : all (cvalid (E'' :\ N) P) (z2 :: (z2a1 ++ z2a2)).
    apply/allP => c cIg; apply/cvalidP => /= i.
    rewrite 3!inE =>  /andP[_ /andP[iIE TLi]].
    rewrite !inE.
    apply: memE''.
      by rewrite gE' z0sz0saE /= inE !mem_cat cIg !orbT. 
    by rewrite inE iIE.
  have p0Isp : p0 \in P by rewrite !inE eq_sym.
  have F pg1 pg2 : pg1 \in P -> pg2 \in P -> drel pg1 pg2 -> 
                    drel (enum_rank_in p0Isp pg1) (enum_rank_in p0Isp pg2).
    rewrite !inE /drel /= => pg1Dp3 pg2Dpg3 pg1Dpg2.
    apply: contra_neq pg1Dpg2 => /enum_rank_in_inj.
    by rewrite !inE; apply.
  move: gH1; rewrite /= => /andP[_ {}gH1].
  rewrite -gH7.
  apply: leq_trans (gdist_cproj F aH gH2 gH1).
  case: (@peg4comp3 (z2p N) np2 np3) => // [||p1 [[p1Dnp3 p1Dnp2 p1Dz] Hz]].
  - move: TLN; rewrite Tmax ltnNge.
    apply: contra => /eqP z2pNE; apply: leq_bigmax_cond.
    rewrite inE NiE andbT inE; apply/existsP; exists z2p.
    rewrite z2pNE eqxx andbT.
    rewrite gE' z0sz0saE /z2p /z0 -!last_cat -!cat_cons !catA 2!mem_cat.
    by rewrite mem_last.
  - by rewrite eq_sym.
  have -> : cproj (E'' :\ N) p0Isp z2 = `c[enum_rank_in p0Isp p1].
    apply/ffunP=> i.
    rewrite !ffunE; congr (enum_rank_in _ _).
    case/moveP : z2pMz2 => d [_ dH1 /on_topP dH2 /on_topP dH3].
    have dE : d = N.
      apply/eqP; rewrite -[_ == _]negbK.
      have : z2p N != z2 N by rewrite z2N2.
      by apply: contra => H; apply/eqP/dH1.
    case: (Hz (z2 (enum_val i))) => // /eqP; rewrite -[_ == _]negbK; case/negP.
    - have: ~~ (d <= (enum_val i)).
        have := enum_valP i; rewrite !inE dE -ltnNge.
        by rewrite [_ < N]ltn_neqAle => /andP[-> _]; rewrite -ltnS /=.
      rewrite -{3}dE -dH1 eq_sym.
        by apply: contra  =>  /eqP /dH2.
      by have := enum_valP i; rewrite dE 2!inE => /andP[].
    - have: ~~ (d <= (enum_val i)).
        have := enum_valP i; rewrite !inE dE -ltnNge.
        by rewrite [_ < N]ltn_neqAle => /andP[-> _]; rewrite -ltnS /=.
      rewrite -z2N2 -{3}dE eq_sym.
      by apply: contra  =>  /eqP /dH3.
    apply: memE''.
      by rewrite gE' z0sz0saE !(mem_cat, inE) eqxx !orbT.
    by have := enum_valP i; rewrite inE => /andP[].
  have -> : cproj (E'' :\ N) p0Isp v = `c[enum_rank_in p0Isp np2].
    apply/ffunP=> i.
    rewrite !ffunE; congr (enum_rank_in _ _).
    have := subsetP cH (v (enum_val i)); rewrite !inE codom_f => /(_ isT).
    case/orP=> /eqP //.
    suff /eqP : v (enum_val i) != np3 by [].
    apply: memE''; first by rewrite inE vIg orbT.
    by have := enum_valP i; rewrite inE => /andP[].
  have : (enum_rank_in p0Isp p1) != (enum_rank_in p0Isp np2).
    rewrite eq_sym; apply/eqP => /enum_rank_in_inj.
    rewrite !inE eq_sym np3Dp2 p1Dnp3 => /(_ isT isT) H.
    by case/eqP: p1Dnp2. 
  have U : #|P| = 3.
    have := cardsC [set np3]; rewrite -/P.
    by rewrite cards1 add1n card_ord => [] [].
  move: (enum_rank_in p0Isp p1) (enum_rank_in p0Isp np2).
  rewrite U => u1 v1 u1Dv1.
  rewrite gdist_perfect (negPf u1Dv1) muln1 /K.
  by rewrite (cardsD1 N) inE NiE TLN.
pose s := ∇((T + K).+1).
(* This is 3.7 *)
have psiDN : psi E - psi (E :\ N) <= 2 ^ s.-1. 
  apply: psi_delta => //.
  rewrite -isOE.
  set tS1 := isO _ _; pose tS2 := isO n.+1 T.+1. 
  apply: leq_trans (_ : #| E'' :|: (tS2 :\: tS1) | <= s).
    apply/subset_leq_card/subsetP => i.
    by rewrite !inE ltnS => /andP[-> ->]; case: (leqP i T).
  apply: leq_trans (_ : #| E''|  + #| tS2 :\:  tS1 | <= s).
    by rewrite cardsU leq_subr.
  rewrite -/K.
  case: (leqP T.+1 (delta s)) => [TLd|dLT].
    rewrite (_ : _ :\: _ = set0) ?cards0 ?addn0.
      apply: leq_trans (_ : ∇ T <= _); first by rewrite root_delta_le.
      by apply: troot_le; rewrite -addnS leq_addr.
    apply/setP=> i; rewrite !inE.
    case: leqP => //= H.
    by rewrite ltnS leqNgt (leq_trans TLd).
  rewrite (_ : tS2 :\: tS1 = sint n.+1 (delta s) T.+1). 
    rewrite card_sint //.
    rewrite -(@leq_add2r (delta s)) -addnA subnK; last by rewrite ltnW.
    rewrite [s + _]addnC -ltnS -!addnS -deltaS !addnS.
    by rewrite -root_delta_lt [K + _]addnC -/s.
  by apply/setP => i; rewrite !inE -leqNgt.
(* This is 3. 8 *)
have duz0_leq2 : psi E - 2 ^ s.-1 <= `d[u, z0]_hmove.
  apply: leq_trans duz0_leq. 
  by rewrite leq_subCl.
have [|K_gt0] := leqP K 0.
  rewrite leqn0 => /eqP KE0.
  have TE : T = N.
    apply/val_inj/eqP; rewrite eqn_leq [T <= _](ltn_ord T) /=.
    suff : N \notin E'' by rewrite inE NiE -leqNgt.
    suff -> : E'' = set0 by rewrite inE.
    by apply: cards0_eq.
  pose c := z2p N.
  case: (@peg4comp3 p0 np2 np3) => [|||p1 [[p1Dnp3 p1Dnp2 p1Dp0] Hz]];
      try by rewrite eq_sym.
  have cDnp2 : c != np2 by rewrite /c.
  have /peg4comp2[pp2 [pp3 [[H1 H2 H3] [H4 H5] H6]]] := cDnp2.
  pose a := if (pp2 \in [:: p0 ; np3]) && (pp3 \in [:: p0 ; p1])
            then pp2 else pp3.
  pose b := if (pp2 \in [:: p0 ; np3]) && (pp3 \in [:: p0 ; p1]) 
            then pp3 else pp2.
  have [aDc aD2 aDb bDc bDnp2] :
       [/\ a != c, a != np2, a != b, b != c & b != np2]. 
    by rewrite /a /b; case: (_ && _); split; rewrite // eq_sym.
  have /andP[aI bI] : (a \in [:: p0; np3]) && (b \in [:: p0; p1]).
    rewrite  /a /b !inE;
       case: (Hz c) cDnp2 H5 H4 H3 H2 H1 => ->; 
           rewrite /= ?(eqxx, andbT, andbF, orbT, orbF);
       case: (Hz pp2) => ->; rewrite /= ?(eqxx, andbT, andbF, orbT, orbF) ;
       case: (Hz pp3) => ->; rewrite /= ?(eqxx, andbT, andbF, orbT,orbF) //;
       rewrite ?[_ == p1]eq_sym ?[_ == np2]eq_sym ?[_ == np3]eq_sym;
       do 6 (case: eqP; rewrite ?eqxx ?orbT //=).
  have Hz1 p : [\/ p = np2, p = c, p = a | p = b].
    by rewrite /a /b; case: (_ && _); case: (H6 p);
       (exact: Or41 ||exact: Or42 || exact: Or43 || exact: Or44).
pose A := [set i in isO n n| ↓[z2] i == a].
pose B := [set i in isO n n| ↓[z2] i == b].
case/moveP : z2pMz2 => d [_ dH1 /on_topP dH2 /on_topP dH3].
have dE : d = N.
  apply/eqP; rewrite -[_ == _]negbK.
  have : z2p N != z2 N by rewrite z2N2.
  by apply: contra => H; apply/eqP/dH1.
have z2iD2 i : ↓[z2] i != np2.
  rewrite -z2N2 -dE ffunE.
  have: ~~ (d <= (trshift 1 i)) by rewrite -ltnNge dE /=.
  by apply: contra  =>  /eqP H; apply: dH3.
have z2iDc i : ↓[z2] i != c.
  rewrite /c ffunE.
  have: ~~ (d <= trshift 1 i) by rewrite -ltnNge dE /=.
  move=> iLN; rewrite -dE eq_sym -dH1.
    have: ~~ (d <=  trshift 1 i) by rewrite -ltnNge dE /=.
    by apply: contra  =>  /eqP H; apply: dH2.
  by rewrite neq_ltn dE /= ltn_ord orbT.
have ABE : A :|: B = sint n 0 n.
  apply/setP=> i; rewrite !inE.
  case: leqP => //= iLn.
  by case: (Hz1 (↓[z2] i)) (z2iD2 i) (z2iDc i) => ->; rewrite eqxx ?orbT.
  (* This is 3.9 *)
  have psiAB_le :  2 ^ ∇(T + K + 1) + psi (isO N N) <= (psi A + psi B).+1.*2.
    rewrite -leq_double -(leq_add2r 1) !doubleS !addSnnS.
    have := @psi_cap_ge n A B.
    rewrite ABE card_sint // subn0 => /(_ (leqnn _)) /(leq_trans _)-> //.
    rewrite (@phi_3_5_4_phi N) // !addnS ltnS addn0 isOE doubleD // leq_add2r.
    rewrite KE0 addn0 TE addn0 /= -addnn leq_add2r.
    by rewrite leq_pexp2l // troot_le.
Admitted.

End Hanoi4.


