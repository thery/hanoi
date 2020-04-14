From mathcomp Require Import all_ssreflect.
Require Import gdist ghanoi triangular phi hanoi3 psi.

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
Check psi.

(* This is theorem 2.9 *)
Lemma phi_2_9 n (u v : configuration 4 n) (E := [set i | u i == peg0 ]) : 
  (codom v) \subset [:: peg2 ; peg3] -> psi E  <= `d[u, v]_hmove.
Proof.
elim: n u v E => // [u v E cH |n IH u v E cH].
  suff ->: E = set0 by rewrite psi_set0.
  by apply/setP=> [] [].
pose N : disk n.+1 := ord_max.
have [NiE|NniE] := boolP (N \in E); last first.
  
  Search psi.
Search gdist cliftrn.
Check cliftrn.

Check plift.

Search psi.

End Hanoi4.


