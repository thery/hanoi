From mathcomp Require Import all_ssreflect.
Require Import tsplit gdist ghanoi triangular phi hanoi3 psi.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


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

(* This is theorem 2.9 *)
Lemma phi_2_9 n (u v : configuration 4 n) (E := [set i | u i == peg0 ]) : 
  (codom v) \subset [:: peg2 ; peg3] -> psi E  <= `d[u, v]_hmove.
Proof.
revert E.
elim: n u v => // [u v E cH |n IH u v E cH].
  suff ->: E = set0 by rewrite psi_set0.
  by apply/setP=> [] [].
pose N : disk n.+1 := ord_max.
have [NiE|NniE] := boolP (N \in E); last first.
  have->: E = E :\ N.
    apply/setP=> i; rewrite 2![in RHS]inE.
    case: eqP => // ->.
    by rewrite (negPf NniE).
  rewrite psi_ord_max.
  apply: leq_trans (gdist_cunlift (connect_move _ _)).
  have -> : [set i | lift ord_max i \in E] = [set i | ↓[u] i == peg0].
    by apply/setP => i; rewrite !inE /= !ffunE // trshift_lift.
  apply: IH.
  apply/subsetP=> i /codomP[j]; rewrite !ffunE !inE => ->.
  have /subsetP /(_  (v (trshift 1 j))) := cH.
  rewrite !inE; apply.
  by apply: codom_f.
(* maybe I should do a wlog *)
pose npeg2 : peg _ := v N.
pose npeg3 : peg _ := if npeg2 == peg2 then peg3 else peg2.
have [np2Dp0 np2Dp1] : (npeg2 != peg0) /\ (npeg2 != peg1).
  have /subsetP /(_  (v N)) := cH.
  by rewrite /npeg2 /peg2 !inE => /(_ (codom_f v N))/orP[]/eqP->; 
     split; apply/eqP/val_eqP; rewrite /= ?inordK.
have [np3Dp0 np3Dp1 np3Dp2] :
   [/\ npeg3 != peg0,  npeg3 != peg1 & npeg3 != npeg2].
  rewrite /npeg3; case: (_ =P peg2) => [->|/eqP].
    by split; apply/eqP/val_eqP; rewrite /= ?inordK.
  rewrite eq_sym => ->.
  by split=> //; apply/eqP/val_eqP; rewrite /= ?inordK.
have npeg4E p : [\/ p = peg0, p = peg1, p = npeg2 | p = npeg3].
  have /subsetP /(_  (v N)) := cH.
  rewrite /npeg3 /npeg2 !inE => /(_ (codom_f v N))/orP[]/eqP->.
    by rewrite eqxx; apply: peg4E.
  rewrite ifN; last by apply/eqP/val_eqP; rewrite /= !inordK.
  by have [] := (peg4E p) => ->; 
    [apply: Or41 | apply: Or42| apply: Or44 | apply: Or43].
have {}cH : codom v \subset [:: npeg2; npeg3].
  apply/subsetP=> i /(subsetP cH); rewrite /npeg3 /npeg2 !inE.
  have := subsetP cH (v N); rewrite !inE codom_f => /(_ isT) /orP[] /eqP->.
    by rewrite eqxx.
  by rewrite orbC ifN // /peg2 /peg3; apply/eqP/val_eqP; rewrite /= !inordK.
have /gdist_path [g [gH1 gH2 gH3 <-]] := connect_move u v.
pose E' := [set i | [exists c, (c \in (u :: g)) && (c i == npeg3) ]] :&: E.
have [Ez|EnZ] := boolP (E' == set0).
  pose P := [set~ npeg3].
  have aH : all (cvalid E P) (u :: g).
    apply/allP => c cIg; apply/cvalidP => /= i iIE.
    rewrite !inE; apply/eqP=> ciP3.
    have /eqP/setP/(_ i) := Ez.
    rewrite [in _ \in set0]inE => /idP[].
    rewrite 2!inE iIE andbT.
    by apply/existsP; exists c; rewrite cIg; apply/eqP.
  have p0Isp : peg0 \in P by rewrite !inE eq_sym.
  have F p1 p2 : p1 \in P -> p2 \in P -> drel p1 p2 -> 
                    drel (enum_rank_in p0Isp p1) (enum_rank_in p0Isp p2).
    rewrite !inE /drel /= => p1D3 p2Dp3 p1Dp2.
    apply: contra_neq p1Dp2 => /enum_rank_in_inj.
    by rewrite !inE; apply.
  apply: leq_trans (gdist_cproj F aH gH2 gH1).
  have -> : cproj E p0Isp u = `c[enum_rank_in p0Isp peg0].
    apply/ffunP=> i.
    rewrite !ffunE; congr (enum_rank_in _ _).
    by have := enum_valP i; rewrite !inE; apply/eqP.
  have -> : cproj E p0Isp v = `c[enum_rank_in p0Isp npeg2].
    apply/ffunP=> i.
    rewrite !ffunE; congr (enum_rank_in _ _).
    have := subsetP cH (v (enum_val i)); rewrite !inE codom_f => /(_ isT).
    case/orP=> /eqP //.
    have /eqP/setP/(_ (enum_val i)) := Ez.
    have := enum_valP i.
    rewrite !inE => -> /idP/negP; rewrite andbT negb_exists.
    by move=> /forallP/(_ v); rewrite -{1}gH2 mem_last => /= /eqP.
  have : (enum_rank_in p0Isp peg0) != (enum_rank_in p0Isp npeg2).
    rewrite eq_sym; apply/eqP => /enum_rank_in_inj.
    rewrite !inE eq_sym np3Dp2 eq_sym np3Dp0 => /(_ isT isT) H.
    by case/eqP: np2Dp0.
  have U : #|P| = 3.
    have := cardsC [set npeg3]; rewrite -/P.
    by rewrite cards1 add1n card_ord => [] [].
  move: (enum_rank_in p0Isp peg0) (enum_rank_in p0Isp npeg2).
  rewrite U => u1 v1 u1Dv1.
  rewrite gdist_perfect (negPf u1Dv1) muln1.
  apply: psi_exp.
  rewrite -{5}[n.+1]card_ord.
  by apply: max_card.
Admitted.

End Hanoi4.


