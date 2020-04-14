From mathcomp Require Import all_ssreflect.
Require Import ghanoi gdist.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(******************************************************************************)
(*                                                                            *)
(*              Generalised Hanoi Problem with only 3 pegs                    *)
(*                                                                            *)
(******************************************************************************)


Section GHanoi3.

(******************************************************************************)
(*  The pegs are the three elements of 'I_3                                   *)
(******************************************************************************)

Implicit Type p : peg 3.
Let peg1 : peg 3 := ord0.
Let peg2 : peg 3 := inord 1.
Let peg3 : peg 3 := inord 2.

Lemma peg3E p : [\/ p = peg1, p = peg2 | p = peg3].
Proof.
by case: p => [] [|[|[|]]] // H; [apply: Or31|apply: Or32|apply: Or33];
   apply/val_eqP; rewrite //= inordK.
Qed.

(* Finding the free peg that differs from p1 and p2 *)

Lemma opeg3E p p1 p2 : p1 != p2 -> (`p[p1, p2] == p) = ((p1 != p) && (p2 != p)).
Proof.
move=> p1Dp2.
have D p3 p4 : (p3 == p4) = (val p3 == val p4).
  by apply/eqP/idP => /val_eqP.
move: p1Dp2 (opegDl p1 p2) (opegDr p1 p2).
by case: (peg3E (opeg p1 p2)) => ->;
   case: (peg3E p1) => ->; 
   case: (peg3E p2) => ->; 
   case: (peg3E p) => ->; 
   rewrite !D /peg1 /peg2 /peg3 /= ?inordK.
Qed.

Variable hrel : rel (peg 3).
Hypothesis hirr : irreflexive hrel.
Hypothesis hsym : symmetric hrel.

Let hmove {n} := @move 3 hrel n.
Let hmove_sym n (c1 c2 : configuration 3 n) : hmove c1 c2 = hmove c2 c1
  := move_sym hsym c1 c2.
Let hconnect n := connect (@hmove n).

Local Notation "c1 `--> c2" := (hmove c1 c2)
    (format "c1  `-->  c2", at level 60).
Local Notation "c1 `-->* c2" := (hconnect c1 c2) 
    (format "c1  `-->*  c2", at level 60).

(* In a move the largest disk has moved, all the smaller disks are pilled up *)
Lemma move_perfectr n (c1 c2 : configuration 3 n.+1) : 
  c1 `--> c2 -> c1 ldisk != c2 ldisk -> 
   ↓[c2] = perfect (`p[c1 ldisk, c2 ldisk]).
Proof.
move=> c1Mc2 c1lDc2l.
apply/ffunP => i; rewrite !ffunE.
have /ffunP/(_ i) := move_ldisk c1Mc2 c1lDc2l; rewrite !ffunE => c1Ec2.
apply/sym_equal/eqP; rewrite opeg3E //; apply/andP; split.
  rewrite -c1Ec2 /=; apply/eqP => c1lEc1r.
  have /on_topP /(_ _ c1lEc1r) := move_on_topl c1Mc2 c1lDc2l.
  by rewrite /= leqNgt ltn_ord.
apply/eqP => c2lEc2r.
have /on_topP /(_ _ c2lEc2r):= move_on_topr c1Mc2 c1lDc2l.
by rewrite /= leqNgt ltn_ord.
Qed.

Lemma move_perfectl n (c1 c2 : configuration 3 n.+1) : 
  c1 `--> c2 -> c1 ldisk != c2 ldisk -> 
  ↓[c1] = perfect (`p[c1 ldisk, c2 ldisk]).
Proof.
rewrite hmove_sym eq_sym opeg_sym.
exact: move_perfectr.
Qed.

Inductive path3S_spec (n : nat)  (c : configuration 3 n.+1)
                                 (cs : seq (configuration 3 n.+1)) :
   forall (b : bool), Type  :=
| path3S_specW : 
    forall (c' := ↓[c]) (cs' := [seq ↓[i] | i <- cs]) (p := c ldisk),
      cs = [seq ↑[i]_p | i <- cs'] ->
      path hmove c' cs' -> path3S_spec c cs true 
| path3S_spec_move : 
    forall cs1 cs2
           (p1 := c ldisk) p2 (p3 :=`p[p1, p2])
           (c1 := ↓[c]) 
           (c2 := ↑[perfect p3]_p2),
        p1 != p2 -> hrel p1 p2 ->
        last c1 cs1 = perfect p3 ->
        cs = [seq ↑[i]_p1 | i <- cs1] ++ c2 :: cs2 ->
        path hmove c1 cs1 -> path hmove c2 cs2 ->
        path3S_spec c cs true |
  path3S_spec_false : path3S_spec c cs false.

(* Inversion theorem on a path for disk n.+1 *)
Lemma path3SP  n (c : _ _ n.+1) cs : path3S_spec c cs (path hmove c cs).
Proof.
case: pathSP=> //; try by constructor.
move=> p1 p2 cs1 cs2 c1 c2 p1Dp2 p1Rp2 csE c1Pcs1 lMc2 c2Pcs2.
have lc1cs1E : last c1 cs1 =  perfect (opeg p1 p2).
  have := move_perfectl lMc2.
  by rewrite !cliftr_ldisk cliftrK; apply.
apply: path3S_spec_move (lc1cs1E) _ _ _  => //.
- by rewrite csE; congr (_ ++ cliftr _ _ :: _).
by rewrite -lc1cs1E.
Qed.

End GHanoi3.