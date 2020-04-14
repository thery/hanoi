(******************************************************************************)
(* We develop a twisted version of split that fills 'I_{m + n} with           *)
(* first the element of 'I_n (x -> x) then the element of m (x -> x + n)      *)
(* This is mostly motivated to naturally get an element of 'I_n from 'I_n.+1  *)
(* by removing max_ord                                                        *)
(******************************************************************************)

From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Lemma tlshift_subproof m n (i : 'I_m) : i + n < m + n.
Proof. by rewrite ltn_add2r. Qed.
Lemma trshift_subproof m n (i : 'I_n) : i < m + n.
Proof. by apply: leq_trans (valP i) _; apply: leq_addl. Qed.

Definition tlshift m n (i : 'I_m) := Ordinal (tlshift_subproof n i).
Definition trshift m n (i : 'I_n) := Ordinal (trshift_subproof m i).

Lemma tlshift_inj m n : injective (@tlshift m n).
Proof. by move=> ? ? /(f_equal val) /addIn /val_inj. Qed.

Lemma trshift_inj m n : injective (@trshift m n).
Proof. by move=> ? ? /(f_equal val) /= /val_inj. Qed.

Lemma tsplit_subproof m n (i : 'I_(m + n)) : i >= n -> i - n < m.
Proof. by move/subSn <-; rewrite leq_subLR [n + m]addnC. Qed.

Definition tsplit {m n} (i : 'I_(m + n)) : 'I_m + 'I_n :=
  match ltnP (i) n with
  | LtnNotGeq lt_i_n =>  inr _ (Ordinal lt_i_n)
  | GeqNotLtn ge_i_n =>  inl _ (Ordinal (tsplit_subproof ge_i_n))
  end.

Variant tsplit_spec m n (i : 'I_(m + n)) : 'I_m + 'I_n -> bool -> Type :=
  | TSplitLo (j : 'I_n) of i = j :> nat : tsplit_spec i (inr _ j) true
  | TSplitHi (k : 'I_m) of i = k + n :> nat : tsplit_spec i (inl _ k) false.

Lemma tsplitP m n (i : 'I_(m + n)) : tsplit_spec i (tsplit i) (i < n).
Proof.
set lt_i_n := i < n; rewrite /tsplit.
by case: {-}_ lt_i_n / ltnP; [left |right; rewrite subnK].
Qed.

Definition tunsplit {m n} (jk : 'I_m + 'I_n) :=
  match jk with inl j => tlshift n j | inr k => trshift m k end.


Lemma ltn_tunsplit m n (jk : 'I_m + 'I_n) : (n <= tunsplit jk) = jk.
Proof.
by case: jk => [j|k]; rewrite /= ?ltn_ord ?leq_addl // leqNgt ltn_ord.
Qed.

Lemma tsplitK {m n} : cancel (@tsplit m n) tunsplit.
Proof. by move=> i; apply: val_inj; case: tsplitP. Qed.

Lemma tunsplitK {m n} : cancel (@tunsplit m n) tsplit.
Proof.
move=> jk; have:= ltn_tunsplit jk; rewrite leqNgt.
by do [case: tsplitP; case: jk => //= i j] => [|/addIn] => /ord_inj->.
Qed.
