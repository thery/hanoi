From mathcomp Require Import all_ssreflect.
Require Import ghanoi gdist.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(******************************************************************************)
(*                                                                            *)
(*              Generalised Hanoi Problem with only 4 pegs                    *)
(*                                                                            *)
(******************************************************************************)


Section GHanoi4.

(*****************************************************************************)
(*  The pegs are the four elements of 'I_4                                   *)
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

End GHanoi4.