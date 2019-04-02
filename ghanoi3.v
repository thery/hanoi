From mathcomp Require Import all_ssreflect.
Require Import ghanoi gdist.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Section GHanoi3.

(*****************************************************************************)
(*  The pegs are the three elements of 'I_3                                  *)
(*****************************************************************************)

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

Definition opeg3 p1 p2 : peg 3 := inord (3 - (p1 + p2)).

Lemma opeg3_sym p1 p2 : opeg3 p1 p2 = opeg3 p2 p1.
Proof. by rewrite /opeg3 addnC. Qed.

Lemma opeg3Dl p1 p2 : p1 != p2 -> opeg3 p1 p2 != p1.
Proof.
move=> /eqP/val_eqP /= p1Dp2; apply/eqP/val_eqP.
by case: p1 p1Dp2  => [] [|[|[|[|]]]] //;
   case p2 => [] [|[|[|[|]]]] //=;
   rewrite /opeg3 /= inordK.
Qed.

Lemma opeg3Dr p1 p2 : p1 != p2 -> opeg3 p1 p2 != p2.
Proof. by rewrite eq_sym opeg3_sym; exact: opeg3Dl. Qed.

Lemma opeg3E p p1 p2 : p1 != p2 -> (opeg3 p1 p2 == p) = ((p1 != p) && (p2 != p)).
Proof.
move=> /eqP/val_eqP /= p1Dp2.
have H : (opeg3 p1 p2 == p :> nat) = (p1 != p :> nat) && (p2 != p :>nat).
  by case: p1 p1Dp2 => [] [|[|[|[|]]]];
     case: p2  => [] [|[|[|[|]]]] //;
     case: p => [] [|[|[|[|]]]] /=;
     rewrite /opeg3 /= inordK.
apply/eqP/andP=> [/val_eqP /=|[/eqP/val_eqP H1 /eqP/val_eqP H2]].
  rewrite H => /andP[H1 H2].
  by split; apply/eqP/val_eqP.
by apply/val_eqP; rewrite H H1.
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
Local Notation "`c[ p ] " := (perfect p )
    (format "`c[ p ]", at level 60).
Local Notation "`p[ p1 , p2 ] " := (opeg3 p1 p2)
    (format "`p[ p1 ,  p2 ]", at level 60).

Lemma move_perfect3 n p1 p2 (p3 := opeg3 p1 p2) (c : _ _ n := perfect p3) :
  hrel p1 p2 ->  hmove (clift p1 c) (clift p2 c).
Proof.
move=> p1Rp2.
have p1Dp2 : p1 != p2.
  by apply/eqP=> p1Ep2; have /idP := hirr p1; rewrite {2}p1Ep2.
apply/moveP; exists ldisk; split => [|d|d|d]; rewrite ?ffunE ?unlift_none //=.
- by case: unliftP => [j -> | U /eqP[]].
- case: unliftP => [j -> /eqP |->] //=.
  by rewrite eq_sym ffunE opeg3E // eqxx.
case: unliftP => [j -> /eqP |->] //=.
by rewrite eq_sym ffunE opeg3E // eqxx andbF.
Qed.

(* In a move only one, all the smaller disks are pilled up *)
Lemma move_perfect3r n (c1 c2 : configuration 3 n.+1) : 
  hmove c1 c2 -> c1 ldisk != c2 ldisk -> 
  cunlift c2 = perfect (opeg3 (c1 ldisk) (c2 ldisk)).
Proof.
move=> c1Mc2 c1lDc2l.
apply/ffunP => i; rewrite !ffunE.
have /ffunP/(_ i) := move_ldisk c1Mc2 c1lDc2l; rewrite !ffunE => c1Ec2.
apply/sym_equal/eqP; rewrite opeg3E //; apply/andP; split.
  rewrite -c1Ec2; apply/eqP => /(move_on_topl c1Mc2 c1lDc2l).
  by rewrite lift_max leqNgt ltn_ord.
apply/eqP => /(move_on_topr c1Mc2 c1lDc2l).
by rewrite lift_max leqNgt ltn_ord.
Qed.

Lemma move_perfect3l n (c1 c2 : configuration 3 n.+1) : 
  hmove c1 c2 -> c1 ldisk != c2 ldisk -> 
  cunlift c1 = perfect (opeg3 (c1 ldisk) (c2 ldisk)).
Proof.
rewrite hmove_sym eq_sym opeg3_sym.
exact: move_perfect3r.
Qed.

Inductive path3S_spec (n : nat)  (c : configuration 3 n.+1)
                                 (cs : seq (configuration 3 n.+1)) :
   forall (b : bool), Type  :=
  path3S_specW : 
    forall (c' := cunlift c) (cs' := map cunlift cs) (p := c ldisk),
      cs = map (clift p) cs'  -> path hmove c' cs' -> path3S_spec c cs true |
  path3S_spec_move : 
    forall cs1 cs2
           (p1 := c ldisk) p2 (p3 := opeg3 p1 p2)
           (c1 := cunlift c) 
           (c2 := clift p2 (perfect p3)),
        p1 != p2 -> hrel p1 p2 ->
        last c1 cs1 = perfect p3 ->
        cs = map (clift p1) cs1 ++ c2 :: cs2 ->
        path hmove c1 cs1 -> path hmove c2 cs2 ->
        path3S_spec c cs true |
  path3S_spec_false : path3S_spec c cs false.

(* Inversion theorem on a path for disk n.+1 *)
Lemma path3SP  n (c : _ _ n.+1) cs : path3S_spec c cs (path hmove c cs).
Proof.
case: pathSP=> //; try by constructor.
move=> p1 p2 cs1 cs2 c1 c2 p1Dp2 p1Rp2 csE c1Pcs1 lMc2 c2Pcs2.
have lc1cs1E : last c1 cs1 =  perfect (opeg3 p1 p2).
  by have := move_perfect3l lMc2; rewrite !ffunE unlift_none /= cliftK => ->.
apply: path3S_spec_move (lc1cs1E) _ _ _  => //.
- by rewrite csE; congr (_ ++ clift _ _ :: _).
by rewrite -lc1cs1E.
Qed.

End GHanoi3.