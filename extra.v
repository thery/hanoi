From mathcomp Require Import all_ssreflect finmap.

Set Implicit Arguments.
Unset Strict Implicit.

(******************************************************************************)
(*                                                                            *)
(*   Extra theorems and definitions                                           *)
(*                                                                            *)
(******************************************************************************)

(******************************************************************************)
(*                                                                            *)
(*   Extra theorems about lists                                               *)
(*                                                                            *)
(******************************************************************************)


Lemma rcons_injl (A : Type) (a: seq A) : injective (rcons a).
Proof. by elim: a => /= [s1 s2 /= [] | b l IH s1 s2 [] /IH]. Qed.

Lemma rcons_injr (A : Type) (a: A) : injective (rcons ^~a).
Proof.
elim => [ [|b [|c]] //= | b s1 IH /= [/= [] -> |c s2 [] -> /IH-> //]].
by case: (s1) => // [] [].
Qed.

Lemma cat_injl (A : Type) (a: seq A) : injective (cat a).
Proof. by elim: a => // b l IH s1 s2 /= [] /IH. Qed.

Lemma cat_injr (A : Type) (a: seq A) : injective (cat ^~a).
Proof.
elim: a => [s1 s2 |b l IH s1 s2]; first by rewrite !cats0.
by rewrite -!cat_rcons => /IH; apply: rcons_injr.
Qed.

Lemma in_split (A : eqType) (a : A)  l :
  a \in l -> exists l1, exists l2, l = l1 ++ a :: l2.
Proof.
elim: l => //= b l IH; rewrite inE => /orP[/eqP<-|aIl].
  by exists [::]; exists l.
case: (IH aIl) => l1 [l2 lE].
by exists (b :: l1); exists l2; rewrite /= lE.
Qed.

Lemma split_first (A : eqType) (l : seq A) (P : pred A) :
  ~~ all [predC P] l -> exists b, exists l1, exists l2,
    [/\ all [predC P] l1, P b &  l = l1 ++ b :: l2].
Proof.
elim: l => //= b l IH.
rewrite negb_and negbK; case: (boolP (b \in P)) =>
      [bIP| bNIP /= /IH [c [l1 [l2 [H1 H2 ->]]]]].
  by exists b; exists [::]; exists l; split.
by exists c; exists (b :: l1); exists l2; split; rewrite /= ?bNIP.
Qed.

Lemma split_last (A : eqType) (l : seq A) (P : pred A) :
  ~~ all [predC P] l  -> exists b, exists l1, exists l2,
    [/\  P b, all [predC  P] l2 &  l = l1 ++ b :: l2].
Proof.
move=> lA.
case: (@split_first _ (rev l) P); first by rewrite all_rev.
move=> b [l1 [l2 [H1 H2 H3]]].
exists b; exists (rev l2); exists (rev l1); split => //.
  by rewrite all_rev.
by rewrite -{1}[l]revK H3 rev_cat /= rev_cons cat_rcons.
Qed.

Lemma split_head (A : eqType) (a b : A) l1 l2 l3 l4 :
  l1 ++ a :: l2 = l3 ++ b :: l4 ->
  [\/ [/\ l1 = l3, a = b & l2 = l4],
      exists l5, l3 = l1 ++ a :: l5 |
      exists l5, l1 = l3 ++ b :: l5].
Proof.
elim: l1 l3 => /= [[[<- <-]|c l3 [<- ->]] /= | c l1 IH [[<- <-]|d l3 /= [<-]]].
- by apply: Or31.
- by apply: Or32; exists l3.
- by apply: Or33; exists l1.
move=> /IH[[<- <- <-]|[l5 ->]|].
- by apply: Or31.
- by apply: Or32; exists l5.
by case=> l5 ->; apply: Or33; exists l5.
Qed.

Lemma split_tail (A : eqType) (a b : A) l1 l2 l3 l4 :
  l1 ++ a :: l2 = l3 ++ b :: l4 ->
  [\/ [/\ l1 = l3, a = b & l2 = l4],
      exists l5, l4 = l5 ++ a :: l2 |
      exists l5, l2 = l5 ++ b :: l4].
Proof.
elim/last_ind : l2 l4 => [l4|l2 c IH l4].
  case: (lastP l4) => /= [|l5 c].
    rewrite !cats1 => /rcons_inj[<- <-].
    by apply: Or31.
  rewrite cats1 -rcons_cons -rcons_cat => /rcons_inj[-> <-].
  by apply: Or32; exists l5; rewrite cats1.
case: (lastP l4) => /= [|l5 d].
  rewrite cats1 -rcons_cons -rcons_cat => /rcons_inj[<- ->].
  by apply: Or33; exists l2; rewrite cats1.
rewrite -!rcons_cons -!rcons_cat => 
   /rcons_inj[/IH [[<- <- <-]|[l6 ->]|[l6 ->]]] <-.
- by apply: Or31.
- by apply: Or32; exists l6; rewrite -rcons_cat.
by apply: Or33; exists l6; rewrite -rcons_cat.
Qed.

(******************************************************************************)
(* We develop a twisted version of split that fills 'I_{m + n} with           *)
(* first the element of 'I_n (x -> x) then the element of m (x -> x + n)      *)
(* This is mostly motivated to naturally get an element of 'I_n from 'I_n.+1  *)
(* by removing max_ord                                                        *)
(******************************************************************************)

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

Lemma trshift_lift n (i : 'I_ n) : trshift 1 i = lift ord_max i.
Proof. by apply/val_eqP; rewrite /= /bump leqNgt ltn_ord. Qed.

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

(******************************************************************************)
(*                                                                            *)
(*   Extra theorems about fset                                                *)
(*                                                                            *)
(******************************************************************************)

Open Scope fset_scope.

Definition sint a b : {fset nat} :=
   [fset @nat_of_ord _ i | i in 'I_b & a <= i].

Lemma mem_sint a b i : i \in sint a b = (a <= i < b).
Proof.
apply/imfsetP/idP => [[j /= aLj ->]|/andP[aLi iLb]].
  by rewrite ltn_ord andbT.
by exists (Ordinal iLb).
Qed.

Lemma sint_sub a b c : a <= c ->
   [fset i in  (sint a b) | c <= i] = sint c b.
Proof.
move=> aLc.
apply/fsetP => i.
rewrite mem_sint.
apply/imfsetP/idP => [[j /=]|/andP[cLi iLb]].
  rewrite inE mem_sint => /andP[/andP[aLj jLb] cLj] ->.
  by rewrite cLj.
by exists i; rewrite //= inE mem_sint cLi iLb (leq_trans aLc).
Qed.

Lemma sintSl a b : sint a.+1 b = sint a b `\ a.
Proof.
apply/fsetP => /= i; rewrite !inE !mem_sint.
by do 2 case: ltngtP.
Qed.

Lemma sintSr a b : sint a b.+1 `\ b = sint a b.
Proof.
apply/fsetP => /= i; rewrite !inE !mem_sint ltnS.
by do 2 case: ltngtP.
Qed.

Lemma sint_split a b : sint a b = sint 0 b `\` sint 0 a.
Proof.
by apply/fsetP => /= i; rewrite !inE !mem_sint /= -leqNgt.
Qed.

Lemma card_sint a b : #|`sint a b| = (b - a).
Proof.
elim: b => [|b IH].
  apply/eqP; rewrite cardfs_eq0; apply/eqP/fsetP=> i.
  by rewrite mem_sint andbF inE.
have [aLb|bLa] := leqP a b; last first.
  rewrite (_ : _ - _ =  0); last first.
    by apply/eqP; rewrite subn_eq0.
  apply/eqP; rewrite cardfs_eq0; apply/eqP/fsetP=> i; rewrite mem_sint inE ltnS.
  by apply/idP => /andP[H1 /(leq_trans H1)]; rewrite leqNgt bLa.
rewrite (cardfsD1 b) (_ : _ \in _); last by rewrite mem_sint aLb /=.
by rewrite sintSr IH subSn.
Qed.

Notation "`[ n ]" := (sint 0 n) (format "`[ n ]").

Lemma sint0_set0 : `[0] = fset0.
Proof.  by apply/fsetP=> i; rewrite mem_sint inE; case: ltngtP. Qed.

Definition s2f n (s : {set 'I_n}) := [fset nat_of_ord i | i in s]. 

Lemma mem_s2f n (s : {set 'I_n}) (i : 'I_n) : (i : nat) \in s2f s = (i \in s).
Proof.
apply/imfsetP/idP => /= [[j jIs iEj]|iIs]; last by exists i.
by rewrite (_ : i = j) //; apply: val_inj.
Qed.

Lemma s2f_set0 n : s2f (set0 : {set 'I_n}) = fset0.
Proof.
apply/fsetP => i; rewrite inE.
by apply/idP => /imfsetP[j /=]; rewrite inE.
Qed.

Lemma s2f_setT n : s2f (setT : {set 'I_n}) = sint 0 n.
Proof.
apply/fsetP => i; rewrite mem_sint /=.
apply/imfsetP/idP => /= [[j _ -> //]| iLn].
by exists (Ordinal iLn).
Qed.


Lemma s2fD n (s1 s2 : {set 'I_n}) : s2f (s1 :\: s2)  = s2f s1 `\` s2f s2.
Proof.
apply/fsetP => j; rewrite !inE.
apply/imfsetP/andP => /= [[k]|[jDi /imfsetP[/= k kIs jEk]]].
  by rewrite !inE -!mem_s2f => /andP[kDi kIs] ->.
by exists k => //; rewrite !inE kIs -mem_s2f -jEk jDi.
Qed.

Lemma s2fU n (s1 s2 : {set 'I_n}) : s2f (s1 :|: s2)  = s2f s1 `|` s2f s2.
Proof.
apply/fsetP => j; rewrite !inE.
apply/imfsetP/orP => /= [[k]|[] /imfsetP[/= k]].
- by rewrite !inE -!mem_s2f => /orP[] kIs ->; [left|right].
- by move => kIs1 ->; exists k; rewrite // inE kIs1.
by move => kIs2 ->; exists k; rewrite // inE kIs2 orbT.
Qed.

Lemma s2fI n (s1 s2 : {set 'I_n}) : s2f (s1 :&: s2)  = s2f s1 `&` s2f s2.
Proof.
apply/fsetP => j; rewrite !inE.
apply/imfsetP/andP => /= [[k]|[jDi /imfsetP[/= k kIs jEk]]].
  by rewrite !inE -!mem_s2f => /andP[kDi kIs] ->.
by exists k => //; rewrite !inE kIs -mem_s2f -jEk jDi.
Qed.

Lemma s2f1 n (i : 'I_n) : s2f [set i] = [fset (nat_of_ord i)].
Proof.
apply/fsetP => j; rewrite !inE.
apply/imfsetP/eqP => /= [[k]|->]; first by rewrite inE => /eqP ->.
by exists i; rewrite ?inE.
Qed.

Lemma s2f_pred n (s : {set 'I_n}) (P : pred nat) : 
   s2f [set i in s | P i] = [fset i in (s2f s) | P i].
Proof.
apply/fsetP=> i; rewrite !inE /=.
apply/imfsetP/andP => /= [[j]|].
  rewrite !inE => /andP[jIs jP] ->; split => //.
  by apply/imfsetP; exists j.
move=> [/imfsetP[/= j jIs ->] jP]; exists j => //.
by rewrite inE jIs.
Qed.

Lemma s2fD1 n (s : {set 'I_n}) i : s2f (s :\ i) = s2f s `\ (nat_of_ord i).
Proof. by rewrite s2fD s2f1. Qed.

Lemma card_s2f n (s : {set 'I_n}) : #|` s2f s| = #|s|.
Proof.
elim: {s}_.+1 {-2}s (leqnn #|s|.+1) => // [] m IH s sLm.
case: (set_0Vmem s) => [->|[i iIs]]; first by rewrite s2f_set0 cards0.
rewrite (cardsD1 i) iIs /= -IH //; last first.
  by move: sLm; rewrite (cardsD1 i) iIs.
rewrite [LHS](cardfsD1 (nat_of_ord i)) (_ : _ \in _); last first.
  by rewrite mem_s2f.
by rewrite s2fD1.
Qed.

(* initial section of an ordinal *)
Definition isO n t := [set i | (i : 'I_n) < t].

Lemma isOE n t : t <= n -> s2f (isO n t) = sint 0 t.
Proof.
move=> tLn.
apply/fsetP => i; rewrite mem_sint.
apply/imfsetP/idP => /= [[j]|iLt]; first by rewrite inE => jLt ->.
have iLn : i < n by apply: leq_trans tLn.
by exists (Ordinal iLn); rewrite // inE.
Qed.

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

Lemma s2fD_isO n (s : {set 'I_n}) t : s2f (s :\: isO n t)  = s2f s `\` sint 0 t.
Proof.
apply/fsetP => j; rewrite !inE.
apply/imfsetP/andP => /= [[k]|[jDi /imfsetP[/= k kIs jEk]]].
  by rewrite !inE -!mem_s2f mem_sint /= => /andP[kDi kIs] ->.
move: jDi; rewrite mem_sint /= -leqNgt => jDi.
by exists k; rewrite // !inE -leqNgt kIs -jEk jDi.
Qed.


