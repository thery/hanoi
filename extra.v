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
  ~~ all [predC P] l -> {bl1l2 : (A * seq A * seq A) |
    [/\ all [predC P] bl1l2.1.2, P bl1l2.1.1 &  
             l = bl1l2.1.2 ++ bl1l2.1.1 :: bl1l2.2]}.
Proof.
elim: l => //= b l IH.
rewrite negb_and negbK; case: (boolP (b \in P)) =>
      [bIP _| bNIP /= /IH [[[c l1] l2] [H1 H2 ->]]].
  by exists (b, [::], l); split.
by exists (c, b :: l1, l2); split; rewrite /= ?bNIP.
Qed.

Lemma split_last (A : eqType) (l : seq A) (P : pred A) :
  ~~ all [predC P] l  -> 
  {bl1l2 | [/\  P bl1l2.1.1, all [predC  P] bl1l2.2 &  
                l = bl1l2.1.2 ++ bl1l2.1.1 :: bl1l2.2]}.
Proof.
move=> lA.
case: (@split_first _ (rev l) P); first by rewrite all_rev.
move=> [[b l1] l2] [H1 H2 H3].
exists (b, rev l2, rev l1); split => //; first by rewrite all_rev.
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

(******************************************************************************)
(*                                                                            *)
(*              Specific theorems for shanoi                                  *)
(*                                                                            *)
(******************************************************************************)

Open Scope nat_scope.

Lemma codom_subC (A : finType) (B : finType) (f : {ffun A -> B}) 
          (p1 p2 : B) : 
  codom f \subset [:: p1; p2] -> codom f \subset [:: p2; p1].
Proof.
by move=> /subsetP sB; apply/subsetP => i /sB; rewrite !inE orbC.
Qed.

Lemma inord_eq0 n k : k = 0 -> inord k = ord0 :> 'I_n.+1.
Proof. by move=> -> /=; apply/val_eqP; rewrite /= inordK. Qed.

Lemma mod3_0 a : (3 * a) %% 3 = 0.
Proof. by rewrite modnMr. Qed.

Lemma mod3_1 a : (3 * a).+1 %% 3 = 1.
Proof. by rewrite mulnC -addn1 modnMDl. Qed.

Lemma mod3_2 a : (3 * a).+2 %% 3 = 2.
Proof. by rewrite mulnC -addn2 modnMDl. Qed.

Definition mod3E := (mod3_0, mod3_1, mod3_2).

Lemma div3_0 a : (3 * a) %/ 3 = a.
Proof. by rewrite mulKn. Qed.

Lemma div3_1 a : (3 * a).+1 %/ 3 = a.
Proof. by rewrite mulnC -addn1 divnMDl // divn_small // addn0. Qed.

Lemma div3_2 a : (3 * a).+2 %/ 3 = a.
Proof. by rewrite mulnC -addn2 divnMDl // divn_small // addn0. Qed.

Definition div3E := (div3_0, div3_1, div3_2).

Lemma sum3E n (f : nat -> nat) : 
  \sum_(i < 3 * n) f i =
  \sum_(i < n) (f (3 * i) + f (3 * i).+1 + f (3 * i).+2).
Proof.
elim: n => [|n IH]; first by rewrite !big_ord0.
by rewrite mulnS !big_ord_recr /= IH !addnA.
Qed.

Lemma Ival_eq n (x y : 'I_n) : (x == y) = (val x == val y).
Proof. by apply/eqP/val_eqP. Qed.

Lemma even_halfMl k m : 
  ~~ odd m -> (k * m)./2 = k * m./2.
Proof.
move=> mE.
have := odd_double_half m; rewrite (negPf mE) add0n => {1}<-.
by rewrite -doubleMr doubleK.
Qed.

Lemma even_halfMr k m : 
  ~~ odd m -> (m * k)./2 = m./2 * k.
Proof.
move=> mE.
have := odd_double_half m; rewrite (negPf mE) add0n => {1}<-.
by rewrite -doubleMl doubleK.
Qed.

Lemma even_halfD m n : 
  ~~ odd m -> ~~ odd n -> (m + n)./2 = (m./2 + n./2).
Proof.
move=> mE nE.
have := odd_double_half m; rewrite (negPf mE) add0n => {1}<-.
have := odd_double_half n; rewrite (negPf nE) add0n => {1}<-.
by rewrite -doubleD doubleK.
Qed.

Lemma even_halfB m n : 
  ~~ odd m -> ~~ odd n -> (m - n)./2 = m./2 - n./2.
Proof.
move=> mE nE.
have := odd_double_half m; rewrite (negPf mE) add0n => {1}<-.
have := odd_double_half n; rewrite (negPf nE) add0n => {1}<-.
by rewrite -doubleB doubleK.
Qed.

Lemma leq_pred2 m n : m <= n -> m.-1 <= n.-1.
Proof. by case: m; case: n => //=. Qed.

Lemma subn_minr : left_distributive subn minn.
Proof.
move=> m n p; rewrite /minn; case: leqP => [nLm|mLn].
  by rewrite ltnNge leq_sub2r.
have [nLp|pLn] := leqP n p; last by rewrite ltn_sub2r.
apply/eqP; move: (nLp); rewrite -subn_eq0 => /eqP->.
by rewrite ltnNge //= subn_eq0 (leq_trans (ltnW mLn)).
Qed.

Lemma subn_maxr : left_distributive subn maxn.
Proof.
move=> m n p; rewrite /maxn; case: leqP => [nLm|mLn].
  by rewrite ltnNge leq_sub2r.
have [nLp|pLn] := leqP n p; last by rewrite ltn_sub2r.
apply/eqP; move: (nLp); rewrite -subn_eq0 => /eqP->.
by rewrite ltnNge //= eq_sym subn_eq0 (leq_trans (ltnW mLn)).
Qed.

Lemma leq_minn2r m n p : m <= n -> minn m p <= minn n p.
Proof.
move=> mLn; rewrite /minn.
case: leqP => pLm; case: leqP => //.
  by rewrite ltnNge (leq_trans pLm).
by move=> _; rewrite ltnW.
Qed.

Lemma leq_minn2l m n p : m <= n -> minn p m <= minn p n.
Proof.
move=> mLn; rewrite /minn.
case: leqP => pLm; case: leqP => //.
by move=> _; rewrite (leq_trans (ltnW pLm)).
Qed.

(******************************************************************************)
(* Definiion of discrete convex and concave version                           *)
(*  it contains just what is needed for shanoi4                               *)
(******************************************************************************)

Section Convex.

Definition increasing (f : nat -> nat) := forall n, f n <= f n.+1.

Definition decreasing (f : nat -> nat) := forall n, f n.+1 <= f n.

Lemma increasing_ext f1 f2 : f1 =1 f2 -> increasing f1 -> increasing f2.
Proof. by move=> fE fI i; rewrite -!fE. Qed.

Lemma increasingE f m n : increasing f -> m <= n -> f m <= f n.
Proof.
move=> fI mLn; rewrite -(subnK mLn).
elim: (_ - _) => //= d fL.
by apply: leq_trans (fI (d + m)).
Qed.

Lemma decreasingE f m n : decreasing f -> m <= n -> f n <= f m.
Proof.
move=> fI mLn; rewrite -(subnK mLn).
elim: (_ - _) => //= d fL.
by apply: leq_trans (fI _) fL.
Qed.

Definition delta (f : nat -> nat) n := f n.+1 - f n.

Lemma delta_ext f1 f2 : f1 =1 f2 -> delta f1 =1 delta f2.
Proof. by move=> fE i; rewrite /delta !fE. Qed.

Definition fnorm (f : nat -> nat) n := f n - f 0.

Lemma increasing_fnorm f : increasing f -> increasing (fnorm f).
Proof. by move=> fI n; rewrite leq_sub2r. Qed.

Lemma delta_fnorm f n : increasing f -> delta (fnorm f) n = delta f n.
Proof.
by move=> fI; rewrite /delta /fnorm -subnDA addnC subnK // increasingE.
Qed.

Lemma sum_delta f n : 
increasing f -> fnorm f n = \sum_(i < n) delta (fnorm f) i.
Proof.
move=> iF.
elim: n => [|n IH]; first by rewrite [LHS]subnn big_ord0.
by rewrite big_ord_recr /= -IH addnC subnK // increasing_fnorm.
Qed.

(* we restrict this to increasing function because of the behavior -*)
Definition convex f :=
  increasing f /\ increasing (delta f).

(* we restrict this to increasing function because of the behavior -*)
Definition concave f :=
  increasing f /\ decreasing (delta f).

Lemma concaveE f : 
  increasing f -> (forall i, f i + f i.+2 <= (f i.+1).*2) -> concave f.
Proof.
move=> fI fH; split => // i.
rewrite /delta.
rewrite -(leq_add2r (f i.+1 + f i)) addnA subnK // addnCA subnK //.
by rewrite addnn addnC.
Qed.

Lemma concaveEk f i k : 
  concave f -> k <= i -> f (i - k) + f (i + k) <= (f i).*2.
Proof.
move=> [fI dfD].
elim: k => /= [kLi|k IH kLi]; first by rewrite subn0 addn0 addnn.
have H : i - k.+1 <= i + k.
  by apply: leq_trans (leq_subr _ _) (leq_addr _ _).
have fk1Lfk : f (i - k.+1) <= f (i - k).
  by apply/(increasingE fI)/leq_sub2l.
have := leq_add (decreasingE dfD H) (IH (ltnW kLi)).
rewrite /delta [f (i - k) + _]addnC addnA subnK ?fU // addnC.
rewrite -subSn // subSS addnBAC // leq_subRL.
  by rewrite addnCA leq_add2l addnS.
by apply: leq_trans fk1Lfk (leq_addr _ _).
Qed.

Lemma concaveEk1 (f : nat -> nat) (i k1 k2 : nat) :
  concave f -> f (i + k1 + k2) + f i <= f (i + k2) + f (i + k1).
Proof.
move=> fC; have [fI dfD] := fC.
elim: k2 k1 i => [k1 i|k2 IHH k1 i]; first by rewrite !addn0 addnC.
rewrite !addnS -(subnK (fI _)) -[X in _ <= X + _](subnK (fI _)).
rewrite -addnA -[X in _ <= X]addnA leq_add //.
by apply: (decreasingE dfD); rewrite addnAC leq_addr.
Qed.

Lemma convexE f : 
  increasing f -> (forall i, (f i.+1).*2 <= f i + f i.+2) -> convex f.
Proof.
move=> fI fH; split => // i.
rewrite /delta.
rewrite -(leq_add2r (f i.+1 + f i)) [_ + f i]addnC addnA subnK //.
by rewrite addnn [f i + _]addnC addnA subnK // addnC.
Qed.

Lemma convexEk f i k : 
  convex f -> k <= i -> (f i).*2 <= f (i - k) + f (i + k).
Proof.
move=> [fI dfI].
elim: k => /= [kLi|k IH kLi]; first by rewrite subn0 addn0 addnn.
have H : i - k.+1 <= i + k.
  by apply: leq_trans (leq_subr _ _) (leq_addr _ _).
have fk1Lfk : f (i - k.+1) <= f (i - k).
  by apply/(increasingE fI)/leq_sub2l.
have := leq_add (increasingE dfI H) (IH (ltnW kLi)).
rewrite /delta [f (i - k) + _]addnC addnA subnK ?fU // addnC.
by rewrite -subSn // subSS addnS addnBA // leq_subLR addnA leq_add2r.
Qed.

(* Ad-hoc bigmin operator *)

Fixpoint bigmin f n := 
 if n is n1.+1 then minn (f n) (bigmin f n1)
 else f 0.

Notation "\min_ ( i <= n ) F" := (bigmin (fun i => F) n)
 (at level 41, F at level 41, i, n at level 50,
  format "\min_ ( i  <=  n )  F").

Lemma bigmin_constD  f n k :
 \min_(i <= n) (f i + k) =  (\min_(i <= n) f i) + k.
Proof. by elim: n => //=  n ->; rewrite addn_minl. Qed.

Lemma bigmin_constB  f n k :
 \min_(i <= n) (f i - k) =  (\min_(i <= n) f i) - k.
Proof. by elim: n => //=  n ->; rewrite subn_minr. Qed.

Lemma eq_bigmin f n : {i0 : 'I_n.+1 | \min_(i <= n) f i = f i0}.
Proof.
elim: n => /= [|n [i ->]]; first by exists ord0.
rewrite /minn; case: leqP => H.
  by exists (inord i); rewrite inordK // (leq_trans (ltn_ord i)).
by exists ord_max.
Qed.

Lemma bigmin_leqP f n m :
  reflect (forall i, i <= n -> m <= f i) 
          (m <= \min_(i <= n) f i).
Proof.
elim: n => /= [|n IH].
  by apply: (iffP idP) => [mLf0 [|i] //|->].
apply: (iffP idP) => [|H].
  rewrite leq_min => /andP[mLf mLmin] i.
  case: ltngtP => // [iLn _|-> _ //].
  by rewrite ltnS in iLn; move: i iLn; apply/IH.
rewrite leq_min H //=.
by apply/IH => i iLn; rewrite H // (leq_trans iLn).
Qed.

Lemma bigmin_inf f n i0 m :
  i0 <= n -> f i0 <= m -> \min_(i <= n) f i <= m.
Proof.
move=> i0Ln fi0Lm; apply: leq_trans fi0Lm.
elim: n i0Ln => /= [|n IH]; first by case: i0.
by case: ltngtP => // [i0Ln _| -> _]; rewrite geq_min ?leqnn ?IH ?orbT.
Qed.

Lemma bigmin_fnorm f n : \min_(i <= n) fnorm f i = fnorm (bigmin f) n. 
Proof. by elim: n => //= n ->; rewrite -subn_minr. Qed.

Lemma bigmin_ext f1 f2 n : 
  (forall i, i <= n -> f1 i = f2 i) -> \min_(i <= n) f1 i = \min_(i <= n) f2 i.
Proof.
elim: n => /= [->//|n IH H].
by rewrite H // IH // => i iH; rewrite H // (leq_trans iH).
Qed.

(* Convolution *)

Definition conv (f g : nat -> nat) n :=
  \min_(i <= n) (f i + g (n - i)).

Lemma conv0 f g : conv f g 0 = f 0 + g 0.
Proof. by []. Qed.

Lemma conv1 f g : 
  conv f g 1 = minn (f 1 + g 0) (f 0 + g 1).
Proof. by []. Qed.

Lemma conv_fnorm f g : 
  increasing f -> increasing g -> 
  conv (fnorm f) (fnorm g) =1 fnorm (conv f g).
Proof.
move=> fI gI i.
rewrite /fnorm /conv /= -bigmin_constB subnn.
apply: bigmin_ext => j.
by rewrite addnBA ?increasingE // addnBAC ?increasingE // subnDA.
Qed.

Lemma conv_ext f1 g1 f2 g2 : f1 =1 f2 -> g1 =1 g2 -> conv f1 g1 =1 conv f2 g2.
Proof. by move=> fE gE i; apply: bigmin_ext => j; rewrite fE gE. Qed.

Lemma convC f g : conv f g =1 conv g f.
Proof.
move=> n; apply/eqP; rewrite /conv eqn_leq; apply/andP; split.
  apply/bigmin_leqP => i iLn.
  rewrite -{1}(subKn iLn) addnC.
  by apply: bigmin_inf (leq_subr _ _) (leqnn _).
apply/bigmin_leqP => i iLn.
rewrite -{1}(subKn iLn) addnC.
by apply: bigmin_inf (leq_subr _ _) (leqnn _).
Qed.

Lemma increasing_conv f g : 
  increasing f -> increasing g -> increasing (conv f g).
Proof.
move=> fI gI i.
apply/bigmin_leqP => j.
case: ltngtP => // [jLi | ->] _.
  by apply: bigmin_inf (_ : j <= i) _; rewrite // leq_add2l subSn.
rewrite subnn.
by apply: bigmin_inf (leqnn i) _; rewrite subnn leq_add2r.
Qed.

(* merging increasing functions *)

Fixpoint fmerge_aux (f g : nat -> nat) i j n := 
 if n is n1.+1 then
   if f i < g j then fmerge_aux f g i.+1 j n1 
   else fmerge_aux f g i j.+1 n1
 else minn (f i) (g j).

Definition fmerge f g n := fmerge_aux f g 0 0 n.

Lemma fmerge_aux_ext f1 f2 g1 g2 i j : f1 =1 f2 -> g1 =1 g2 -> 
  fmerge_aux f1 g1 i j =1 fmerge_aux f2 g2 i j.
Proof.
move=> fE gE n; elim: n i j => /= [i1 j1|n IH i j]; first by rewrite fE gE.
by rewrite !(fE, gE, IH).
Qed.

Lemma fmerge_ext f1 f2 g1 g2 : f1 =1 f2 -> g1 =1 g2 -> 
  fmerge f1 g1 =1 fmerge f2 g2.
Proof. by move=> fE gE n; apply: fmerge_aux_ext. Qed.

Lemma fmerge_aux_correct f g i j n :
  increasing f -> increasing g -> 
  (forall k, k <= n ->  
     minn (f (i + k)) (g (j + (n - k))) <=  
     fmerge_aux f g i j n).
Proof.
move=> fI gI.
elim: n i j => /= [i j [|] // _|n IH i j k kLn].
  by rewrite !addn0.
case: leqP => [gLf|fLg].
  move: kLn; rewrite leq_eqVlt => /orP[/eqP->|kLn].
    rewrite subnn addn0 (minn_idPr _); last first.
      by rewrite (leq_trans gLf) // increasingE // leq_addr.
    apply: leq_trans (IH _ _ _ (leqnn _)).
    rewrite subnn addn0 leq_min increasingE // andbT (leq_trans gLf) //.
    by rewrite increasingE // leq_addr.
  by rewrite subSn // -addSnnS IH.
case: k kLn => [_ | k kLn].
  rewrite addn0 subn0 (minn_idPl _); last first.
    by rewrite (leq_trans (ltnW fLg)) // increasingE // leq_addr.
  apply: leq_trans (IH i.+1 j 0 isT).
  rewrite addn0 leq_min increasingE //= (leq_trans (ltnW fLg)) //.
  by rewrite increasingE // leq_addr.
by rewrite subSS -addSnnS IH.
Qed.

Lemma fmerge_aux_exist f g i j n :
  exists2 k, k <= n & fmerge_aux f g i j n = minn (f (i + k)) (g (j + (n - k))).
Proof.
elim: n i j => /= [i j | n IH i j]; first by exists 0; rewrite //= !addn0.
case: (leqP (g j) (f i)) => [gLf|fLg]; last first.
  by case: (IH i.+1 j) => k kLn ->; exists k.+1; rewrite // addnS subSS.
case: (IH i j.+1) => [] [|k] kLn ->.
  by exists 0; rewrite // addn0 !subn0 addnS.
by exists k.+1; rewrite ?(leq_trans kLn) // addSnnS -subSn.
Qed.

Lemma fmergeE (f g : nat -> nat) n : 
 increasing f -> increasing g ->
 fmerge f g n = \max_(i < n.+1) minn (f i) (g (n - i)).
Proof.
move=> fI gI.
apply/eqP; rewrite /fmerge eqn_leq; apply/andP; split.
  case: (@fmerge_aux_exist f g 0 0 n) => // i1 i1Ln ->.
  by apply: (@leq_bigmax_cond _ _ _ (Ordinal (i1Ln : i1 < n.+1))).
apply/bigmax_leqP => /= i _.
by apply: fmerge_aux_correct; rewrite -1?ltnS.
Qed.

Lemma increasing_fmerge f g : 
  increasing f -> increasing g -> increasing (fmerge f g).
Proof.
move=> fI gI n; rewrite !fmergeE //.
apply/bigmax_leqP => /= i _.
apply: leq_trans (leq_bigmax_cond _ (isT : xpredT (inord i : 'I_n.+2))).
rewrite inordK ?(leq_trans (ltn_ord _)) //.
rewrite leq_min geq_minl /= (leq_trans (geq_minr _ _)) //.
apply: increasingE gI _.
by rewrite leq_sub2r.
Qed.

Lemma fmerge0 f g : fmerge f g 0 = minn (f 0) (g 0).
Proof. by []. Qed.

Fixpoint sum_fmerge_aux (f g : nat -> nat) i j n := 
 if n is n1.+1 then
   if f i < g j then f i + sum_fmerge_aux f g i.+1 j n1 
   else g j + sum_fmerge_aux f g i j.+1 n1
 else minn (f i) (g j).

Definition sum_fmerge f g n := sum_fmerge_aux f g 0 0 n.

Lemma sum_fmerge_aux_correct f g n i j : 
  sum_fmerge_aux f g i j n = \sum_(k < n.+1) fmerge_aux f g i j k.
Proof.
elim: n i j => //= [i j|n IH i j]; first by rewrite big_ord_recr big_ord0.
by rewrite big_ord_recl /= /minn; case: leqP; rewrite IH.
Qed.

Lemma sum_fmerge_correct f g n : 
  sum_fmerge f g n = \sum_(k < n.+1) fmerge f g k.
Proof. by apply: sum_fmerge_aux_correct. Qed.

Lemma sum_fmerge_aux_conv_correct f g i j n :
  increasing f -> increasing g -> 
  (forall k, k <= n.+1 -> 
    sum_fmerge_aux f g i j n <= 
    \sum_(l < k) f (i + l) + \sum_(l < n.+1 - k) g (j + l)).
Proof.
move=> fI gI.
elim: n i j => /= [i j [_|[_|]]//|n IH i j k kLn].
- by rewrite big_ord_recr !big_ord0 /= !addn0 !add0n geq_minr.
- by rewrite big_ord_recr !big_ord0 /= !addn0 !add0n geq_minl.
case: leqP => [gLf|fLg].
  move: kLn; case: ltngtP => // [kLn _ |-> _]; last first.
    rewrite subnn big_ord0 addn0 big_ord_recl addn0 /=.
    apply: leq_add => //.
    rewrite /bump /=.
    apply: leq_trans (IH _ _ _ (leqnn _)) _.
    rewrite subnn big_ord0 addn0 leq_sum // => l _.
    by apply: increasingE; rewrite // addnCA leq_addl.
  rewrite subSn // big_ord_recl addn0 addnCA leq_add2l.
  apply: leq_trans (IH _ _ _ (kLn : k <= n.+1)) _.
  rewrite leq_add2l leq_sum // => l _.
  by rewrite increasingE //= /bump addnCA add1n.
move: kLn; case: ltngtP => // [kLn _ |-> _]; last first.
  rewrite subnn big_ord0 addn0 big_ord_recl addn0 /= leq_add2l /bump /=.
  apply: leq_trans (IH _ _ _ (leqnn _)) _.
  rewrite subnn big_ord0 addn0 leq_sum // => l _.
  by rewrite increasingE // addnCA add1n.
case: k kLn => [_|k kLn]; last first.
  rewrite subSS.
  apply: leq_trans (leq_add  (leqnn _) (IH i.+1 j k _)) _ .
    by rewrite -ltnS ltnW.
  rewrite addnA leq_add2r big_ord_recl addn0 leq_add2l leq_sum // => l _.
  by rewrite addnCA.
rewrite big_ord0 add0n subn0.
apply: leq_trans (leq_add  (leqnn _) (IH i.+1 j 0 isT)) _ .
rewrite big_ord0 add0n subn0 [X in _ <= X]big_ord_recr addnC leq_add //.
apply: leq_trans (ltnW fLg) _.
by rewrite increasingE // leq_addr.
Qed.

Lemma leq_sum_fmerge_conv f g k n :
  increasing f -> increasing g -> k <= n -> 
  \sum_(i < n) fmerge f g i <= \sum_(i < k) f i + \sum_(i < n - k) g i.
Proof.
move=> fI gI; case: n => [|n kLn].
  by case: k; rewrite // !big_ord0.
rewrite -sum_fmerge_correct.
exact: (sum_fmerge_aux_conv_correct 0 0 fI gI kLn).
Qed.

Lemma sum_fmerge_aux_exist f g i j n :
  exists2 k, k <= n.+1 & 
  sum_fmerge_aux f g i j n =     
  \sum_(l < k) f (i + l) + \sum_(l < n.+1 - k) g (j + l).
Proof.
elim: n i j => /= [i j | n IH i j].
  rewrite /minn; case: leqP => [gLf|fLg].
    by exists 0; rewrite // big_ord_recl !big_ord0 !(add0n, addn0).
  by exists 1; rewrite // subnn big_ord_recl !big_ord0 !(add0n, addn0).
case: (leqP (g j) (f i)) => [gLf|fLg].
  case: (IH i j.+1) => k kLn ->.
  exists k; first by apply: leq_trans kLn _.
  rewrite (subSn kLn) big_ord_recl addn0 addnCA.
  by congr (_ + (_ + _)); apply: eq_bigr => l _; rewrite addnCA.
case: (IH i.+1 j) => k kLn ->; exists k.+1; first by apply: leq_trans kLn _.
rewrite big_ord_recl addn0 subSS -addnA.
by congr (_ + (_ + _)); apply: eq_bigr => l _; rewrite addnCA.
Qed.

Lemma sum_fmerge_exist f g n :
  exists2 k, k <= n & 
  \sum_(i < n) fmerge f g i = \sum_(i < k) f i + \sum_(i < n - k) g i.
Proof.
case: n => [|n]; first by exists 0; rewrite // !big_ord0.
case: (sum_fmerge_aux_exist f g 0 0 n) => k kLn sE.
by exists k; rewrite // -sum_fmerge_correct [LHS]sE.
Qed.

Lemma sum_fmerge_conv f g n : 
  increasing f -> increasing g ->
  \sum_(i < n) (fmerge f g) i  =
     conv (fun n => \sum_(i < n) f i) (fun n => \sum_(i < n) g i) n.
Proof.
move=> fI gI.
apply/eqP; rewrite eqn_leq; apply/andP; split; last first.
  case: (sum_fmerge_exist f g n) => k kLn ->.
  by apply: (bigmin_inf _ (leqnn _)).
apply/bigmin_leqP => k kLn.
by apply: leq_sum_fmerge_conv.
Qed.

(* This is 3.2 *)
Lemma delta_conv f g : 
  convex f -> convex g -> delta (conv f g) =1 fmerge (delta f) (delta g).
Proof.
move=> [fI dfI] [gI dgI] n.
rewrite -delta_fnorm; last by apply: increasing_conv.
rewrite -(delta_ext (conv_fnorm _ _)) //.
have/delta_ext-> : conv (fnorm f) (fnorm g) =1
         conv (fun n => \sum_(i < n) (delta (fnorm f)) i) 
              (fun n => \sum_(i < n) (delta (fnorm g)) i).
  by apply: conv_ext => i; apply: sum_delta.
have/delta_ext-> :
  (conv (fun n : nat => \sum_(i < n) delta (fnorm f) i)
        (fun n : nat => \sum_(i < n) delta (fnorm g) i)) =1
  (fun n => \sum_(i < n) (fmerge (delta (fnorm f)) (delta (fnorm g))) i).
  move=> k; rewrite -sum_fmerge_conv //.
    by apply: increasing_ext dfI => i; rewrite delta_fnorm.
  by apply: increasing_ext dgI => i; rewrite delta_fnorm.
rewrite /delta big_ord_recr /= addnC addnK.
by apply: fmerge_aux_ext => i; apply: delta_fnorm.
Qed.

Lemma convex_conv f g : convex f -> convex g -> convex (conv f g).
Proof.
move=> [fI dfI] [gI dgI]; split; first by apply: increasing_conv.
apply: increasing_ext => [i|]; first by apply/sym_equal/delta_conv.
by apply: increasing_fmerge.
Qed.

End Convex.

Notation "\min_ ( i <= n ) F" := (bigmin (fun i => F) n)
 (at level 41, F at level 41, i, n at level 50,
  format "\min_ ( i  <=  n )  F").


(* Mimic AC match for leq_trans *)
Ltac is_num term :=
 match term with 
 | 0 => true 
 | S ?X => is_num X
 | _ => false
end.

Ltac split_term term :=
 match term with 
 | ?X * ?Y => match is_num X with true =>  constr:((X, Y))
              | false => 
              let v := once (split_term X) in constr:((fst v, snd v * Y)) 
              end
 | ?X => match is_num X with true => constr:((X, 1)) 
                             | _ => constr:((1, X)) end
 | _ => false
end.


Ltac delta_term n1 n2 t2 :=
  let n :=  constr:(n1 - n2) in
  let n1 := eval compute in n in
  let vt2 := eval lazy delta [fst snd] iota beta in t2 in 
  let r :=
    match n1 with 
    | 0 => constr:(0) 
    | 1 => constr:(t2) 
    | ?X  => 
    match vt2 with | 1 => X | _ => constr:(X * vt2) end
    end in
   eval lazy delta [fst snd] iota beta in r. 
    
Ltac delta_lterm2 n1 t1 lt2 :=
 match lt2 with 
 |  ?X2 + ?Y2 =>
     let v2 := split_term Y2 in
     let n2 := constr:(fst v2) in
     let t2 := constr:(snd v2) in
     let t := constr:((t1, t2)) in
     let vt := eval lazy delta [fst snd] iota beta in t in 
     match vt with 
     | (?X, ?X) => delta_term n1 n2 t2
     |  _  => delta_lterm2 n1 t1 X2
     end
 |   ?Y2 =>
     let v2 := split_term Y2 in
     let n2 := constr:(fst v2) in
     let t2 := constr:(snd v2) in 
     let t := constr:((t1, t2)) in
     let vt := eval lazy delta [fst snd] iota beta in t in 
     match vt with 
     | (?X, ?X) => delta_term n1 n2 t2
     |  _  => delta_term n1 0 t1
     end
end.

Ltac make_sum t1 t2 :=
  match t1 with 0 => t2 | _ => 
  match t2 with 0 => t1 | _ => constr:(t1 + t2) end end. 
  
Ltac delta_lterm1 lt1 lt2 :=
 match lt1 with 
 |  ?X1 + ?Y1 =>
     let v1 := split_term Y1 in
     let n1 := constr:(fst v1) in
     let t1 := constr:(snd v1) in 
     let r1 := delta_lterm1 X1 lt2 in
     let r2 := delta_lterm2 n1 t1 lt2 in make_sum r1 r2

 |   ?Y1 =>
     let v1 := split_term Y1 in
     let n1 := constr:(fst v1) in
     let t1 := constr:(snd v1) in delta_lterm2 n1 t1 lt2
end.

Ltac test t1 t2 := let xx := delta_lterm1 t1 t2 in pose kk := xx.

Ltac applyr H :=
  rewrite -?mul2n in H |- *;
  match goal with 
  H: is_true (leq _ ?X) |- is_true (leq _ ?Y) =>
    ring_simplify X Y in H;
    ring_simplify X Y; rewrite ?[nat_of_bin _]/= in H |- *
  end;
  let Z := fresh "Z" in
  match goal with 
  H: is_true (leq _ ?X1) |- is_true (leq _ ?Y1) =>
    let v := delta_lterm1 Y1 X1 in
    (try (rewrite [Z in _ <= Z](_ : _ = v + X1))); 
    [ apply: leq_trans (leq_add (leqnn _) H); rewrite {H}// ?(add0n,addn0) 
     | ring]
  end.
  
Ltac applyl H :=
  rewrite -?mul2n in H |- *;
  match goal with 
  H: is_true (leq ?X _) |- is_true (leq ?Y _) =>
    ring_simplify X Y; ring_simplify X Y in H;
    rewrite ?[nat_of_bin _]/= in H |- *
  end;
  let Z := fresh "Z" in
  match goal with 
  H: is_true (leq ?X1 _) |- is_true (leq ?Y1 _) =>
    let v := delta_lterm1 Y1 X1 in
    (try rewrite [Z in Z <= _](_ : Y1 = v + X1));
    [apply: leq_trans (leq_add (leqnn _) H) _;
     rewrite {H}// ?(add0n,addn0) | ring]
  end.

Ltac gsimpl :=
  rewrite -?mul2n in |- *;
  match goal with 
  |- is_true (leq ?X ?Y) =>
    ring_simplify X Y; rewrite ?[nat_of_bin _]/=
  end;
  let Z := fresh "Z" in
  match goal with 
    |- is_true (leq ?X1 ?Y1) =>
    let v := delta_lterm1 Y1 X1 in
    match v with 
    | 0 => 
    let v := delta_lterm1 X1 Y1 in
    let v1 := delta_lterm1 X1 v in
    let v2 := delta_lterm1 Y1 v1 in
    (try (rewrite [Z in _ <= Z](_ : Y1 = v2 + v1); last by ring));
    (try (rewrite [Z in Z <= _](_ : X1 = v + v1); last by ring));
    rewrite ?leq_add2r
    | _ => 
    let v1 := delta_lterm1 Y1 v in
    let v2 := delta_lterm1 X1 v1 in
    (try (rewrite [Z in _ <= Z](_ : Y1 = v + v1); last by ring));
    (try (rewrite [Z in Z <= _](_ : X1 = v2 + v1); last by ring));
    rewrite ?leq_add2r
  end
  end.
  
Ltac sring := rewrite -!mul2n; ring.
Ltac changel t :=
  let X := fresh "X" in 
  rewrite [X in X <= _](_ : _ = t); last by (ring || sring).
Ltac changer t := 
  let X := fresh "X" in 
  rewrite [X in _ <= X](_ : _ = t); last by (ring || sring).
