(******************************************************************************)
(*                                                                            *)
(*                              Triangular number                             *)
(*                                                                            *)
(******************************************************************************)
(*                                                                            *)
(*     delta n = the n^th triangular number                                   *)
(*     troot n = the triangular root of n                                     *)
(*      tmod n = the triangular modulo of n                                   *)
(*                                                                            *)
(*                                                                            *)
(******************************************************************************)

From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma prednDl m n : 0 < m -> (m + n).-1 = m.-1 + n.
Proof. by case: m. Qed.

Lemma prednDr m n : 0 < n -> (m + n).-1 = m + n.-1.
Proof. by case: n => // n; rewrite addnS. Qed.

Lemma leq_sub_sub a b c : ((a - b) - (c - b)) <= a - c.
Proof.
have [aLb|bLa] := leqP b a; last first.
  rewrite (_ : a - _ = 0) ?sub0n //.
  by apply/eqP; rewrite subn_eq0 ltnW.
have [cLb|bLc] := leqP c b; last first.
  by rewrite subnBA ?subnK // ltnW.
rewrite (_ : c - _ = 0); last by apply/eqP; rewrite subn_eq0.
by rewrite subn0 leq_sub2l.
Qed.

Lemma leq_sub_add b a c : a - c <= (a - b) + (b - c).
Proof.
rewrite leq_subLR addnC -addnA.
have [/subnK->|H] := leqP c b.
  have [/subnK->//|H] := leqP b a.
  apply: leq_trans (ltnW H) _.
  by apply: leq_addl.
have := ltnW H.
rewrite -subn_eq0 => /eqP->.
rewrite addnC -leq_subLR.
by apply: leq_sub2l; apply: ltnW.
Qed.

Lemma sum_set_diff (I : finType) (P : I -> nat) (e1 e2 : {set I}) :
   \sum_(i in e1 :\: e2) P i = \sum_(i in e1 | i \notin e2) P i.
Proof.
rewrite big_mkcond [RHS]big_mkcond /=.
apply: eq_bigr => i _.
by rewrite !inE andbC.
Qed.

Lemma sum_set_swap (I : finType) (P : I -> nat) (e1 e2 : {set I}) :
   \sum_(i in e1 | i \in e2) P i = \sum_(i in e2 | i \in e1) P i.
Proof.
rewrite big_mkcond [RHS]big_mkcond /=.
by apply: eq_bigr => i _; rewrite andbC.
Qed.

(******************************************************************************)
(*                                                                            *)
(*                               Triangular number                            *)
(*                                                                            *)
(******************************************************************************)

Definition delta n := (n.+1 * n)./2.

Notation "'Δ' n " := (delta n) (format "'Δ' n", at level 10).

Compute zip (iota 1 20) (map delta (iota 1 20)).

Lemma deltaS n : delta n.+1 = delta n + n.+1.
Proof.
rewrite /delta -addn2 mulnDl mulnC halfD.
rewrite !odd_mul andbF add0n mul2n.
by rewrite -{4}(half_bit_double n.+1 false).
Qed.

Lemma delta_gt0 n : 0 < n -> 0 < delta n.
Proof. by case: n => // n _; rewrite deltaS addnS ltnS leq_addr. Qed.

Lemma deltaE n : delta n = \sum_(i < n.+1) i.
Proof.
elim: n => [|n IH]; first by rewrite big_ord_recl big_ord0.
by rewrite big_ord_recr /= -IH deltaS.
Qed.

Compute zip (iota 0 11) (map delta (iota 0 11)).

Lemma delta_le m n : m <= n -> delta m <= delta n.
Proof. by move=> H; apply/half_leq/leq_mul. Qed.

Lemma delta_square n : (8 * delta n).+1 = n.*2.+1 ^ 2.
Proof.
elim: n => // n IH.
rewrite deltaS mulnDr -addSn IH.
rewrite doubleS -addn1 -addnS -addSn addn1.
rewrite sqrnD -addnA /=.
congr (_ + _).
rewrite mulnS.
rewrite [_ * 2]mulSn mulnDr addnA.
congr (_ + _).
by rewrite mulnCA -muln2 -!mulnA mulnC.
Qed.

Lemma geq_deltann n : n <= delta n.
Proof.
by case: n => // n; rewrite deltaS addnS ltnS leq_addl.
Qed.

(******************************************************************************)
(*                                                                            *)
(*                               Triangular root                              *)
(*                                                                            *)
(******************************************************************************)

Definition troot n := 
 let l := iota 0 n.+2 in
 (find (fun x => n < delta x) l).-1.

Notation "∇ n" := (troot n) (format "∇ n", at level 10).

Compute zip (iota 0 11) (map troot (iota 0 11)).

Lemma troot_gt0 n : 0 < n -> 0 < troot n.
Proof. by case: n. Qed.

Lemma delta_root_le m : delta (troot m) <= m.
Proof.
rewrite /troot leqNgt.
set l := iota _ _; set f := (fun _ => _).
case E : _.-1 => [|n] //.
have  /(before_find 0) : 
   (find f l).-1 < find f l by rewrite prednK // E.
rewrite E  nth_iota // /f => [->//|].
rewrite -[m.+2](size_iota 0) -E prednK; first by apply: find_size.
by case: find E.
Qed.

Lemma delta_root_gt m : m < delta (troot m).+1.
Proof.
rewrite /troot leqNgt.
set l := iota _ _; set f := (fun _ => _).
have Hfl : has f l.
  apply/hasP; exists m.+1; first by rewrite mem_iota leq0n leqnn.
  rewrite /f /delta -{1}[m.+1](half_bit_double _ false).
  by apply/half_leq; rewrite add0n -mul2n leq_mul2r orbT.
have := nth_find 0 Hfl; rewrite {1}/f.
case E : _.-1 => [|n] //.
  case: find E => // [] [|n] //.
  by rewrite nth_iota //=; case: (m).
rewrite nth_iota.
  by rewrite -E prednK // ltnNge ltnS.
by rewrite -(size_iota 0 m.+2) -has_find.
Qed.

(* Galois connection *)
Lemma root_delta_le m n : (n <= troot m) = (delta n <= m).
Proof.
case: leqP => [/delta_le/leq_trans->//|dmLn].
  apply: delta_root_le.
apply/sym_equal/idP/negP.
rewrite -ltnNge.
by apply: leq_trans (delta_root_gt _) (delta_le dmLn).
Qed.

Lemma root_delta_lt m n : (troot m < n) = (m < delta n).
Proof. by rewrite ltnNge root_delta_le -ltnNge. Qed.

Lemma troot_le m n : m <= n -> troot m <= troot n.
Proof.
by move=> mLn; rewrite root_delta_le (leq_trans (delta_root_le _)).
Qed.

Lemma trootE m n : (troot m == n) = (delta n <= m < delta n.+1).
Proof.
rewrite ltnNge -!root_delta_le -ltnNge.
by rewrite ltnS -eqn_leq.
Qed.

Lemma troot_delta n : troot (delta n) = n.
Proof. by apply/eqP; rewrite trootE leqnn deltaS -addn1 leq_add2l. Qed.

Lemma leq_rootnn n : troot n <= n.
Proof.
by rewrite -{2}[n]troot_delta troot_le // geq_deltann.
Qed.

(******************************************************************************)
(*                                                                            *)
(*                               Triangular modulo                            *)
(*                                                                            *)
(******************************************************************************)

Definition tmod n := n - delta (troot n).

Lemma tmod_delta n : tmod (delta n) = 0.
Proof. by rewrite /tmod troot_delta subnn. Qed.

Lemma tmodE n : n = delta (troot n) + tmod n.
Proof. by rewrite addnC (subnK (delta_root_le _)). Qed.

Lemma tmod_le n : tmod n <= troot n.
Proof.  by rewrite leq_subLR -ltnS -addnS -deltaS delta_root_gt. Qed.


Lemma ltn_root m n : troot m < troot n -> m < n.
Proof.
rewrite root_delta_le deltaS => /(leq_trans _) -> //.
by rewrite {1}[m]tmodE ltn_add2l ltnS tmod_le.
Qed.

Lemma leq_mod m n : troot m = troot n -> (tmod m <= tmod n) = (m <= n).
Proof.
by move=> tmEtn; rewrite {2}[m]tmodE {2}[n]tmodE tmEtn leq_add2l.
Qed.

Lemma ltn_mod m n : troot m = troot n -> (tmod m < tmod n) = (m < n).
Proof.
by move=> tmEtn; rewrite {2}[m]tmodE {2}[n]tmodE tmEtn ltn_add2l.
Qed.

Lemma troot_mod_case m : 
         ((troot m.+1 == troot m) && (tmod m.+1 == (tmod m).+1))
      || 
         [&& troot m.+1 == (troot m).+1, tmod m.+1 == 0 & tmod m == troot m].
Proof.
have := troot_le (leqnSn m).
rewrite leq_eqVlt => /orP[/eqP He|He].
  by rewrite /tmod -He subSn ?eqxx // {2}[m]tmodE leq_addr.
rewrite orbC.
have: troot m.+1 == (troot m).+1.
  rewrite trootE (leq_trans (delta_le He)) //; last first.
    by rewrite {2}[m.+1]tmodE leq_addr.
  rewrite !deltaS {1}[m]tmodE -addnS -addnS -addnA.
  by rewrite leq_add2l (leq_trans _ (leq_addl _ _)) // !ltnS tmod_le.
move/eqP=> He1.
rewrite He1 eqxx.
have := eqxx m.+1.
rewrite {1}[m]tmodE {1}[m.+1]tmodE He1 deltaS -addnS.
rewrite -!addnA eqn_add2l addSn eqSS => /eqP He2.
have := tmod_le m.
rewrite leq_eqVlt => /orP[/eqP He3|]; last first.
  by rewrite He2 ltnNge leq_addr.
rewrite He3 -(eqn_add2l (tmod m)) {1}He3 -He2 addn0.
by rewrite !eqxx.
Qed.

Lemma troot_mod_le m n : 
   m <= n = 
   ((troot m < troot n) || ((troot m == troot n) && (tmod m <= tmod n))).
Proof.
case: leqP => [|dmGdn] /= ; last first.
  apply/idP.
  apply: (leq_trans (_ : _ <= delta (troot m).+1)).
    by rewrite ltnW // delta_root_gt.
  apply: (leq_trans (_ : _ <= delta (troot n))).
    by apply: delta_le.
  by apply: delta_root_le.
rewrite leq_eqVlt => /orP[/eqP dnEdm|dmLdn].
  rewrite dnEdm eqxx /=.
  by rewrite {1}[m]tmodE {1}[n]tmodE dnEdm leq_add2l.
rewrite (gtn_eqF dmLdn) /=.
apply/idP/negP.
rewrite -ltnNge.
apply: (leq_trans (delta_root_gt _)).
apply: (leq_trans _ (delta_root_le _)).
by apply: delta_le.
Qed.

Lemma troot_mod_lt m n : 
   m < n = 
   ((troot m < troot n) || ((troot m == troot n) && (tmod m < tmod n))).
Proof.
case: (leqP (troot n) (troot m))  => [|dmGdn] /= ; last first.
  apply/idP.
  apply: (leq_trans (delta_root_gt _)).
  apply: (leq_trans (delta_le dmGdn)).
  by apply: delta_root_le.
rewrite leq_eqVlt => /orP[/eqP dnEdm|dmLdn].
  rewrite dnEdm eqxx /=.
  by rewrite {1}[m]tmodE {1}[n]tmodE dnEdm ltn_add2l.
rewrite (gtn_eqF dmLdn) /=.
apply/idP/negP.
rewrite -ltnNge ltnS ltnW //.
apply: (leq_trans (delta_root_gt _)).
apply: (leq_trans _ (delta_root_le _)).
by apply: delta_le.
Qed.

(******************************************************************************)
(*                                                                            *)
(*                  Correspondence between N and N x N                        *)
(*                                                                            *)
(******************************************************************************)

(* An explicit definition of N <-> N * N *)
Definition tpair n := (troot n - tmod n, tmod n).
 
Compute zip (iota 0 20) (map tpair (iota 0 20)).

Definition pairt p := delta (p.1 + p.2) + p.2.

Lemma tpairt n : pairt (tpair n) = n.
Proof.
rewrite /tpair /pairt /= (subnK (tmod_le _)).
by rewrite /tmod addnC subnK // delta_root_le.
Qed.

Lemma tpairt_inv p : tpair (pairt p) = p.
Proof.
case: p => a b.
rewrite /tpair /pairt /= /tmod.
have ->: ∇(Δ(a + b) + b)  = a + b.
  apply/eqP.
  rewrite trootE leq_addr /= deltaS.
  by rewrite addnS ltnS addnCA leq_addl.
by rewrite [delta _ + _]addnC !addnK.
Qed.
