From mathcomp Require Import all_ssreflect.
Require Import gdist ghanoi.


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Section sHanoi.

(*****************************************************************************)
(*  The pegs are the elements of 'I_n.+3                                     *)
(*****************************************************************************)

Variable m : nat.
Implicit Type p : peg m.+3.

Let smove {n} := @move m.+3 (@srel m.+3) n.
Let smove_sym n (c1 c2 : configuration m.+3 n) : smove c1 c2 = smove c2 c1
  := move_sym (@ssym _) c1 c2.
Let sconnect n := connect (@smove n).

Local Notation "c1 `--> c2" := (smove c1 c2)
    (format "c1  `-->  c2", at level 60).
Local Notation "c1 `-->* c2" := (sconnect c1 c2) 
    (format "c1  `-->*  c2", at level 60).
Local Notation "`c[ p ] " := (perfect p )
    (format "`c[ p ]", at level 60).

Let p0 : peg m.+3 := ord0.

Definition so1 p : (peg m.+3) := if (p == inord 1) then inord 2 else inord 1.

Lemma so1_cor p : so1 p != p0 /\ so1 p != p.
Proof.
rewrite /so1; case: (p =P _) => [->|/eqP pD1]; split.
- by apply/eqP/val_eqP; rewrite /= !inordK.
- by apply/eqP/val_eqP; rewrite /= !inordK.
- by apply/eqP/val_eqP; rewrite /= !inordK.
by rewrite eq_sym.
Qed.

Definition so2 p1 p2 : (peg m.+3) := 
if (p1 == inord 1) then 
  if (p2 == inord 2) then inord 3 else inord 2
else 
  if (p2 == inord 1) then
    if (p1 == inord 2) then inord 3 else inord 2
  else inord 1.

Lemma so2_cor p1 p2 : 
  0 < m ->
  [/\ so2 p1 p2 != p0, so2 p1 p2 != p1 & so2 p1 p2 != p2].
Proof.
move=> m_gt0.
rewrite /so2; case: (p1 =P _) => [->|/eqP p1D1];
  rewrite /so2; case: (p2 =P _) => [->|/eqP p2D].
- by split; apply/eqP/val_eqP; rewrite /= !inordK.
- by split; try (by rewrite eq_sym); apply/eqP/val_eqP; rewrite /= !inordK.
- case: (p1 =P _) => [->|/eqP p1D2].
    by split; apply/eqP/val_eqP; rewrite /= !inordK.
  by split; try (by rewrite eq_sym); apply/eqP/val_eqP; rewrite /= !inordK.
by split; try (by rewrite eq_sym); apply/eqP/val_eqP; rewrite /= !inordK.
Qed. 

Lemma shanoi_connect_perfect n (c : configuration _ n) p :
  sconnect c (perfect p).
Proof.
have sirr := @sirr m.+3.
elim: n c p => [c p | n IH c p]; first by apply/eq_connect0/ffunP=> [] [[]].
pose p1 := c ldisk.
rewrite -[c]cunliftrK -/p1 -[perfect p]cunliftrK perfect_unliftr ffunE.
have [<-|/eqP pDp1] := p =P p1; first by apply/connect_liftr/IH.
have [p1Ep0|/eqP p1Dp0] := p1 =P p0.
  rewrite p1Ep0.
  case: (so1_cor p) => sDp0 sDp.
  apply: connect_trans (_ : connect _ ↑[`c[so1 p]]_p _); last first.
    by apply/connect_liftr/IH.
  apply: connect_trans (_ : connect _ ↑[`c[so1 p]]_p0 _).
    by apply/connect_liftr/IH.
  apply/connect1/move_liftr_perfect; try by rewrite eq_sym.
  by rewrite /srel /= eq_sym -p1Ep0 pDp1.
have [pEp0|/eqP pDp0] := p =P p0.
  case: (so1_cor p1) => sDp0 sDp1.
  apply: connect_trans (_ : connect _ ↑[`c[so1 p1]]_p1 _).
    by apply/connect_liftr/IH.
  apply: connect_trans (_ : connect _ ↑[`c[so1 p1]]_p _).
    apply/connect1/move_liftr_perfect; try by rewrite eq_sym.
      by rewrite /srel /= eq_sym pDp1 pEp0 muln0.
    by rewrite eq_sym pEp0.
  by apply/connect_liftr/IH.
apply: connect_trans (_ : connect _ ↑[`c[p]]_p1 _).
  by apply/connect_liftr/IH.
apply: connect_trans (_ : connect _ ↑[`c[p]]_p0 _).
  apply/connect1/move_liftr_perfect; try by rewrite eq_sym.
  by rewrite /srel /= p1Dp0 muln0.
apply: connect_trans (_ : connect _ ↑[`c[p1]]_p0 _).
  by apply/connect_liftr/IH.
apply: connect_trans (_ : connect _ ↑[`c[p1]]_p _).
  apply/connect1/move_liftr_perfect; try by rewrite // eq_sym.
  by rewrite /srel /= eq_sym pDp0.
by apply/connect_liftr/IH.
Qed.

Lemma shanoi_connect n (c1 c2 : configuration _ n) : sconnect c1 c2.
Proof.
apply: connect_trans (shanoi_connect_perfect _ p0) _.
rewrite (connect_sym (@ssym m.+3)).
apply: shanoi_connect_perfect.
Qed.

End sHanoi.