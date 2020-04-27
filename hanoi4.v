From mathcomp Require Import all_ssreflect finmap.
Require Import tsplit gdist ghanoi triangular phi hanoi3 psi.

Set Implicit Arguments.
Unset Strict Implicit.

Section Hanoi4.

(*****************************************************************************)
(*  The pegs are the three elements of 'I_4                                  *)
(*****************************************************************************)


Lemma in_split (A : eqType) (a : A)  l :
  a \in l -> exists l1, exists l2, l = l1 ++ a :: l2.
Proof.
elim: l => //= b l IH; rewrite inE => /orP[/eqP<-|aIl].
  by exists [::]; exists l.
case: (IH aIl) => l1 [l2 lE].
by exists (b :: l1); exists l2; rewrite /= lE.
Qed.

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

Notation "`[ n ]" := (sint 0 n) (format "`[ n ]").

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

Lemma codom_lift k n (c : configuration k n.+1) (s : seq (peg k)) :
  codom c \subset s -> codom ↓[c] \subset s.
Proof.
move=> H; apply/subsetP => i /mapP[j _ ->].
by rewrite ffunE; apply: (subsetP H); apply: codom_f.
Qed.

Lemma codom_cut k n (c : configuration k n) t (tLn : t <= n) (s : seq (peg k)) :
  codom c \subset s -> codom (ccut tLn c) \subset s.
Proof.
move=> H; apply/subsetP => i /mapP[j _ ->].
by rewrite ffunE; apply: (subsetP H); apply: codom_f.
Qed.

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

Lemma s2f_setT n : s2f (setT : {set disk n}) = `[n].
Proof.
apply/fsetP => i; rewrite mem_sint /=.
apply/imfsetP/idP => /= [[j _ -> //]| iLn].
by exists (Ordinal iLn).
Qed.

Lemma s2f_lift k n (c : configuration k n.+1) (p : disk k):
  s2f ([set i | c i == p] :\ ord_max) = 
  s2f [set i | cunliftr c i == p].
Proof.
apply/fsetP=> i.
apply/imfsetP/imfsetP => [] [/= j].
  rewrite !inE => /andP[jDn /eqP cjEp] jEi.
  have jLn : j < n.
    rewrite -val_eqE /= in jDn.
    by have := ltn_ord j; rewrite ltnS leq_eqVlt (negPf jDn).
  exists (Ordinal jLn) => //=; rewrite !inE ffunE; apply/eqP.
  by rewrite -cjEp; congr (c _); apply: val_eqP.
rewrite inE ffunE => /eqP cjEp iEj; exists (trshift 1 j) => //.
by rewrite !inE cjEp -val_eqE //= neq_ltn ltn_ord /=.
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

Lemma s2f1 n (s : {set 'I_n}) (i : 'I_n) :
  s2f [set i] = [fset (nat_of_ord i)].
Proof.
apply/fsetP => j; rewrite !inE.
apply/imfsetP/eqP => /= [[k]|->]; first by rewrite inE => /eqP ->.
by exists i; rewrite ?inE.
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

Lemma s2f_ccut k n (c : configuration k n) t (tLn : t <= n) (p : disk k) : 
  s2f ([set i | c i == p] :&: isO n t) =
  s2f [set i | ccut tLn c i == p].
Proof.
apply/fsetP=> /= i.
apply/imfsetP/imfsetP => [] /= [j]; rewrite !inE.
  case/andP => cjEp jLt ->.
  by exists (Ordinal jLt); rewrite //= inE !ffunE ordinalK.
rewrite !ffunE => cjEp ->; exists (widen_ord tLn j) => //=.
by rewrite !inE /= cjEp /=.
Qed.

(* This is theorem 2.9 *)
Lemma phi_2_9 n (u v : configuration 4 n) (p0 p2 p3 : peg 4) :
  [/\ p3 != p2, p3 != p0 & p2 != p0] ->
  (codom v) \subset [:: p2 ; p3] -> 
  psi (s2f [set i | u i == p0]) <= `d[u, v]_hmove.
Proof.
move=> pH.
elim: {n}_.+1 {-2}n (leqnn n.+1) u v p0 p2 p3 pH => //
   [] m IH [|n] nLm u v p0 p2 p3 [p3Dp2 p3Dp0 p2Dp0] cH.
  set E := [set i | _].
  suff ->: E = set0 by rewrite s2f_set0 psi_set0.
  by apply/setP=> [] [].
set E := [set i | _].
pose N : disk n.+1 := ord_max.
have [NiE|NniE] := boolP (N \in E); last first.
  have->: E = E :\ N.
    apply/setP=> i; move: NniE; rewrite !inE.
    by case: (_ =P N) => // <- /negPf->.
  rewrite s2f_lift.
  apply: leq_trans (gdist_cunlift (connect_move _ _)).
  by apply: IH (codom_lift cH).
have uN0 : u N = p0 by move: NiE; rewrite inE => /eqP.
(* maybe I should do a wlog *)
pose np2 : peg _ := v N.
have vN2 : v N = np2 by [].
pose np3 : peg _ := if np2 == p2 then p3 else p2.
have np2Dp0 : np2 != p0.
  have /subsetP /(_  (v N)) := cH.
  by rewrite /np2 !inE => /(_ (codom_f v N))/orP[]/eqP->.
have [np3Dp0 np3Dp2] : np3 != p0 /\  np3 != np2.
  rewrite /np3; case: (_ =P p2) => [->|/eqP] => //.
  by move=> H; split => //; rewrite eq_sym.
have {}cH : codom v \subset [:: np2; np3].
  apply/subsetP=> i /(subsetP cH); rewrite /np3 /np2 !inE.
  have := subsetP cH (v N); rewrite !inE codom_f => /(_ isT) /orP[] /eqP->.
    by rewrite eqxx.
  by rewrite orbC ifN.
have uDv : u != v.
  by apply: contra_neq np2Dp0 => uE; rewrite -uN0 uE vN2.
have /gpath_connect [g gH] := connect_move u v.
have vIg : v \in g.
  by have := mem_last u g; rewrite inE (gpath_last gH) eq_sym (negPf uDv).
pose E' := [set i | [exists c, (c \in (u :: g)) && (c i == np3)]] :&: E.
have [Ez|EnZ] := boolP (E' == set0).
  pose P := [set~ np3].
  have aH : all (cvalid E P) (u :: g).
    apply/allP => c cIg; apply/cvalidP => /= i iIE.
    rewrite !inE; apply/eqP=> ciP3.
    have /eqP/setP/(_ i) := Ez.
    rewrite [in _ \in set0]inE => /idP[].
    rewrite 2!inE iIE andbT.
    by apply/existsP; exists c; rewrite cIg; apply/eqP.
  have p0Isp : p0 \in P by rewrite !inE eq_sym.
  have F pg1 pg2 : pg1 \in P -> pg2 \in P -> drel pg1 pg2 -> 
                    drel (enum_rank_in p0Isp pg1) (enum_rank_in p0Isp pg2).
    rewrite !inE /drel /= => pg1Dp3 pg2Dpg3 pg1Dpg2.
    apply: contra_neq pg1Dpg2 => /enum_rank_in_inj.
    by rewrite !inE; apply.
  apply: leq_trans (gpath_cproj F aH gH).
  have -> : cproj E p0Isp u = `c[enum_rank_in p0Isp p0].
    apply/ffunP=> i.
    rewrite !ffunE; congr (enum_rank_in _ _).
    by have := enum_valP i; rewrite !inE => /eqP.
  have -> : cproj E p0Isp v = `c[enum_rank_in p0Isp np2].
    apply/ffunP=> i.
    rewrite !ffunE; congr (enum_rank_in _ _).
    have := subsetP cH (v (enum_val i)); rewrite !inE codom_f => /(_ isT).
    case/orP=> /eqP //.
    have /eqP/setP/(_ (enum_val i)) := Ez.
    have := enum_valP i.
    rewrite !inE => -> /idP/negP; rewrite andbT negb_exists.
    by move=> /forallP/(_ v); rewrite -{1}(gpath_last gH) mem_last => /= /eqP.
  have : (enum_rank_in p0Isp p0) != (enum_rank_in p0Isp np2).
    rewrite eq_sym; apply/eqP => /enum_rank_in_inj.
    rewrite !inE eq_sym np3Dp2 eq_sym np3Dp0 => /(_ isT isT) H.
    by case/eqP: np2Dp0.
  have U : #|P| = 3.
    have := cardsC [set np3]; rewrite -/P.
    by rewrite cards1 add1n card_ord => [] [].
  move: (enum_rank_in p0Isp p0) (enum_rank_in p0Isp np2).
  rewrite U => u1 v1 u1Dv1.
  rewrite gdist_perfect (negPf u1Dv1) muln1 -card_s2f.
  by apply: psi_exp.
rewrite -card_gt0 in EnZ.
case: (eq_bigmax_cond (@nat_of_ord _) EnZ) => /= T TinE' Tmax.
have {}Tmax := sym_equal Tmax.
have uT0 : u T = p0.
  by apply/eqP; move: TinE'; rewrite !inE => /andP[].
pose E'' := [set i in E | i > T].
pose K := #|E''|.
have memE'' c i  : c \in u :: g -> i \in E'' -> c i != np3.
  move=> cIug; rewrite inE => /andP[iIE].
  rewrite ltnNge Tmax; apply: contra => ciE.
  apply: leq_bigmax_cond; rewrite inE iIE andbT inE.
  by apply/existsP; exists c; rewrite cIug.
pose ST1 := isO n.+1 T.+1.
have cST1 : #|ST1| = T.+1 by rewrite card_isO; apply/minn_idPr.
(* This 3.2 *)
have KTE : T + K <= n.
  rewrite -ltnS -{2}[n.+1]card_ord -addSn.
  rewrite -[_ + _]subn0 -(_ : #|ST1 :&: E''| = 0); last first.
    apply/eqP; rewrite cards_eq0; apply/eqP/setP => i.
    rewrite /ST1 !inE; apply/idP => /and3P[].
    by rewrite ltnS leqNgt => /negPf->.
  by rewrite -cST1 -cardsU max_card.
move: TinE'.
rewrite !inE => /andP[/existsP[/= c_p3 /andP[]]].
  rewrite inE => /orP[/eqP->|]; first by rewrite uT0 eq_sym (negPf np3Dp0).
move=> c_p3Ig /eqP c_p3T3 _.
case (@split_first _ g (fun c : configuration _ _ => c(T) != p0)).
  apply/negP=> /allP /(_ _ vIg); rewrite /= -topredE negbK.
  have /subsetP/(_ (v T))/(_ (codom_f _ _)) := cH.
  by rewrite !inE => /orP[] /eqP->; rewrite (negPf np2Dp0, negPf np3Dp0).
move=> x0s [x0sb [x0sa [/allP x0sbP0 x0TD0 gE]]].
pose x0 := last u x0sb.
have x0T0 : x0 T = p0.
  have := mem_last u x0sb; rewrite !inE /x0 => /orP[/eqP->|/x0sbP0] //.
  by rewrite /= -topredE negbK => /eqP.
have x0TDx0sT : x0 T != x0s T by rewrite x0T0 eq_sym.
have x0sTD0 : x0s T != p0 by rewrite eq_sym -x0T0.
have x0Mx0s : x0 `--> x0s.
  by move: (gpath_path gH); rewrite gE cat_path /= -/x0 => /and3P[].
case (@split_first _  (x0s :: x0sa)
                (fun c : configuration _ _ => c(T) == np3)).
  have c_p3Ix0sa : c_p3 \in x0s :: x0sa.
    move: c_p3Ig; rewrite gE mem_cat => /orP[/x0sbP0|//].
    by rewrite /= -topredE negbK c_p3T3 (negPf np3Dp0).
  apply/negP=> /allP /(_ _ c_p3Ix0sa); rewrite /= -topredE /=.
  by rewrite c_p3T3 eqxx.
move => x3 [x3b [x3a [/allP x3bP0 /eqP x3T3 x0sx0saE]]].
pose x3p := last x0 x3b.
have x3pND3 : x3p T != np3.
  have := mem_last x0 x3b; rewrite -/x3p inE => /orP[/eqP->|/x3bP0//].
  by rewrite x0T0 eq_sym.
have x3pTDx3T : x3p T != x3 T by rewrite x3T3.
have x3pMx3 : x3p `--> x3.
  by move: (gpath_path gH); 
     rewrite gE x0sx0saE cat_path /= cat_path /= => /and4P[].
case (@split_first _ g (fun c : configuration _ _ => c(N) != p0)) => /=.
  apply/negP=> /allP /(_ _ vIg); rewrite /= -topredE negbK.
  have /subsetP/(_ (v N))/(_ (codom_f _ _)) := cH.
  by rewrite !inE => /orP[] /eqP->; rewrite (negPf np2Dp0, negPf np3Dp0).
move=> z0s [z0sb [z0sa [/allP z0sbP0 z0sND0 gE']]].
pose z0 := last u z0sb.
have z0N0 : z0 N = p0.
  have := mem_last u z0sb; rewrite !inE /z0 => /orP[/eqP->|/z0sbP0] //.
  by rewrite /= -topredE negbK => /eqP.
have z0NDz0sN : z0 N != z0s N by rewrite z0N0 eq_sym.
have z0Mz0s : z0 `--> z0s.
   by move: (gpath_path gH); rewrite gE' cat_path /= => /and3P[].
case (@split_last _ (z0 :: z0s :: z0sa) 
             (fun c : configuration _ _ => c(N) != np2)).
  have z0Iz0sz0sa : z0 \in z0 :: z0s :: z0sa by rewrite inE eqxx.
  apply/negP=> /allP /(_ _ z0Iz0sz0sa); rewrite /= -topredE negbK.
  by rewrite z0N0 eq_sym (negPf np2Dp0).
move=> z2p [z2b [[|z2 z2a] [z2pN2 /allP z2aDp2 z0sz0saE]]].
  have : last z0 (z0s :: z0sa) = z2p.
    by rewrite -[last _ _]/(last z0 (z0 :: z0s :: z0sa)) z0sz0saE last_cat.
  move: (gpath_last gH); rewrite gE' last_cat /= => -> vEz2p.
  by case/eqP: z2pN2; rewrite -vEz2p.
have z0Ez2p : z2b = [::] -> z0 = z2p by case: z2b z0sz0saE => [[]|].
have {}z0sz0saE : z0s :: z0sa = (rcons (behead (rcons z2b z2p)) z2) ++ z2a.
  case: (z2b) z0sz0saE => [[_ -> ->]|zz ll [_ ->]] //=.
  by rewrite !cat_rcons.
have z2Ig : z2 \in g.
  by rewrite gE' z0sz0saE !(inE, mem_cat, mem_rcons, eqxx, orbT).
have z2N2 : z2 N = np2.
  have /z2aDp2 : z2 \in z2 :: z2a by rewrite inE eqxx.
  by rewrite /= -topredE negbK => /eqP.
have z2pNDz2N : z2p N != z2 N by rewrite z2N2.
have z2pMz2 : z2p `--> z2.
  move: (gpath_path gH); rewrite gE' z0sz0saE.
  case: (z2b) z0Ez2p => [<-//=|zz ll _ /=].
    by rewrite  !cat_path /= => /and3P[].
  by rewrite cat_rcons !cat_path /= last_rcons => /and4P[].
(* This is 3.3 *)
have duz0_leq : psi (s2f (E :\ N)) <= `d[u, z0]_hmove. 
  rewrite s2f_lift.
  have /peg4comp2[pp2 [pp3 [[H1 H2 H3] [H4 H5] H6]]] := z0sND0.
  have cH1 : codom ↓[z0] \subset [::pp2; pp3].
    apply/subsetP=> i; rewrite !inE => /codomP[j].
    rewrite !ffunE => ->.
    case: (H6 (z0 (trshift 1 j))) => [/eqP|/eqP|->|->]; last 2 first.
    - by rewrite eqxx.
    - by rewrite eqxx orbT.
    - by rewrite (negPf ( move_on_toplDr z0Mz0s z0NDz0sN _)) // -ltnS.
    by rewrite -z0N0 (negPf ( move_on_toplDl z0Mz0s z0NDz0sN _)) //=.
  apply: leq_trans (gdist_cunlift (connect_move _ _)).
  by apply: IH cH1.
(* This is 3.4 *)
pose ST := isO n.+1 T.
have cST : #|ST| = T by rewrite card_isO; apply/minn_idPr; rewrite ltnW.
have dux0_leq : psi ((s2f E) `&` sint 0 T) <= `d[u, x0]_hmove.
  have TLN : T <= n.+1 by rewrite ltnW.
  move: gH; rewrite gE => /gpath_catl /(gpath_ccut TLN)/(leq_trans _)-> //.
  rewrite -(@isOE n.+1) // -s2fI s2f_ccut.
  have /peg4comp2[pp2 [pp3 [[H1 H2 H3] [H4 H5] H6]]] := x0sTD0.
  have cH1 : codom (ccut TLN x0) \subset [:: pp2; pp3].
    apply/subsetP=> i /codomP [j]; rewrite !inE !ffunE => ->.
    case: (H6 (x0 (widen_ord TLN j))) => [/eqP|/eqP|->|->]; last 2 first.
    - by rewrite eqxx.
    - by rewrite eqxx orbT.
    - by rewrite (negPf (move_on_toplDr x0Mx0s x0TDx0sT _)) //= // ltnW.
    by rewrite -x0T0 (negPf (move_on_toplDl x0Mx0s x0TDx0sT _)) /=.
  apply: IH cH1 => //.
  by apply: leq_trans (ltn_ord _) _.
have [KLT|TLK] := leqP (delta K) T; last first.
  have K_gt0 : 0 < K by case: (K) TLK.
  have TLN : T < N by apply: leq_trans KTE; rewrite -addn1 leq_add2l.
  (* This is 3. 5 *)
  have psiDN : psi (s2f E) - psi (s2f (E :\ N)) <= 2 ^ K.-1. 
    rewrite s2fD1.
    apply: psi_delta => //; last by rewrite (mem_s2f _ N).
    rewrite -s2fD_isO card_s2f.
    apply: subset_leq_card.
    apply/subsetP=> i; rewrite !inE -leqNgt.
    case: (_ == _); rewrite /= !(andbT, andbF) // => KLi.
    by apply: leq_trans KLi.
  rewrite gE' in gH |- *.
  have gH5 : size (z0s :: z0sa) = `d[z0, v]_hmove.
    by have := gpath_dist (gpath_catr gH).
  rewrite (gdist_cat gH) -/z0 -/hmove.
  apply: leq_trans (leq_add duz0_leq (leqnn _)).
  rewrite -leq_subLR; apply: leq_trans psiDN _.
  have gH1 := gpath_catr gH; rewrite -/z0 -/hmove in gH1.
  have [-> gH2] : `d[z0, v]_hmove = `d[z0, z2]_hmove + `d[z2, v]_hmove
                   /\ gpath hmove z2 v z2a.
    split.
      by move: gH1; rewrite z0sz0saE => /gdist_cat; rewrite last_rcons.
    by move: gH1; rewrite z0sz0saE => /gpath_catr; rewrite last_rcons.
  rewrite -[_ ^ _]prednK ?expn_gt0 // -add1n.
  apply: leq_add.
    rewrite gdist_gt0.
    by apply/eqP => /ffunP/(_ N) /eqP; rewrite z0N0 z2N2 eq_sym (negPf np2Dp0).
  pose P := [set~ np3].
  have aH : all (cvalid (E'' :\ N) P) (z2 :: z2a).
    apply/allP => c cIg; apply/cvalidP => /= i iIE''.
    rewrite !inE; apply: memE''; last first.
      by move: iIE''; rewrite inE => /andP[].
    by rewrite gE' z0sz0saE cat_rcons inE !mem_cat cIg !orbT.
  have p0Isp : p0 \in P by rewrite !inE eq_sym.
  have F pg1 pg2 : pg1 \in P -> pg2 \in P -> drel pg1 pg2 -> 
                    drel (enum_rank_in p0Isp pg1) (enum_rank_in p0Isp pg2).
    rewrite !inE /drel /= => pg1Dp3 pg2Dpg3 pg1Dpg2.
    apply: contra_neq pg1Dpg2 => /enum_rank_in_inj.
    by rewrite !inE; apply.
  case: (@peg4comp3 (z2p N) np2 np3) =>  // [||p1 [[p1Dnp3 p1Dnp2 p1Dz] Hz]].
  - move: TLN; rewrite Tmax ltnNge.
    apply: contra => /eqP z2pNE; apply: leq_bigmax_cond.
    rewrite inE NiE andbT inE; apply/existsP; exists z2p.
    rewrite z2pNE eqxx andbT gE' /z0 z0sz0saE.
    case: (z2b) z0Ez2p => [<-//=|zz ll _ /=].
      by rewrite -cat_cons -/z0 mem_cat (mem_last u z0sb).
    by rewrite !(inE, mem_cat, mem_rcons, eqxx, orbT).
  - by rewrite eq_sym.
  apply: leq_trans (gpath_cproj F aH gH2).
  have -> : cproj (E'' :\ N) p0Isp z2 = `c[enum_rank_in p0Isp p1].
    apply/ffunP=> i.
    rewrite !ffunE; congr (enum_rank_in _ _).
    case: (Hz (z2 (enum_val i))) => // /eqP; rewrite -[_ == _]negbK; case/negP.
    - by rewrite (negPf ( move_on_toprDl z2pMz2 z2pNDz2N _)) // -ltnS.
    - rewrite -z2N2 (negPf (move_on_toprDr z2pMz2 z2pNDz2N _)) //.
      have := enum_valP i; rewrite  /= !inE => /andP[/eqP/val_eqP/=].
      have := ltn_ord (enum_val i); rewrite leq_eqVlt /= eqSS ltnS.
      by case: ltngtP.
    apply: memE''; first by rewrite inE z2Ig orbT.
    by have := enum_valP i; rewrite inE => /andP[].
  have -> : cproj (E'' :\ N) p0Isp v = `c[enum_rank_in p0Isp np2].
    apply/ffunP=> i.
    rewrite !ffunE; congr (enum_rank_in _ _).
    have := subsetP cH (v (enum_val i)); rewrite !inE codom_f => /(_ isT).
    case/orP=> /eqP //.
    suff /eqP : v (enum_val i) != np3 by [].
    apply: memE''; first by rewrite inE vIg orbT.
    by have := enum_valP i; rewrite inE => /andP[].
  have : (enum_rank_in p0Isp p1) != (enum_rank_in p0Isp np2).
    rewrite eq_sym; apply/eqP => /enum_rank_in_inj.
    rewrite !inE eq_sym np3Dp2 p1Dnp3 => /(_ isT isT) H.
    by case/eqP: p1Dnp2. 
  have U : #|P| = 3.
    have := cardsC [set np3]; rewrite -/P.
    by rewrite cards1 add1n card_ord => [] [].
  move: (enum_rank_in p0Isp p1) (enum_rank_in p0Isp np2).
  rewrite U => u1 v1 u1Dv1.
  rewrite gdist_perfect (negPf u1Dv1) muln1 /K.
  by rewrite (cardsD1 N) inE NiE TLN.
pose s := ∇((T + K).+1).
(* This is 3.7 *)
have psiDN : psi (s2f E) - psi (s2f (E :\ N)) <= 2 ^ s.-1. 
  rewrite s2fD1.
  apply: psi_delta; last by rewrite mem_s2f.
  rewrite -s2fD_isO // card_s2f.
  set tS1 := isO _ _; pose tS2 := isO n.+1 T.+1. 
  apply: leq_trans (_ : #| E'' :|: (tS2 :\: tS1) | <= s).
    apply/subset_leq_card/subsetP => i.
    by rewrite !inE ltnS => /andP[-> ->]; case: (leqP i T).
  apply: leq_trans (_ : #| E''|  + #| tS2 :\:  tS1 | <= s).
    by rewrite cardsU leq_subr.
  rewrite -/K.
  case: (leqP T.+1 (delta s)) => [TLd|dLT].
    rewrite (_ : _ :\: _ = set0) ?cards0 ?addn0.
      apply: leq_trans (_ : ∇ T <= _); first by rewrite root_delta_le.
      by apply: troot_le; rewrite -addnS leq_addr.
    apply/setP=> i; rewrite !inE.
    case: leqP => //= H.
    by rewrite ltnS leqNgt (leq_trans TLd).
  rewrite -card_s2f.
  rewrite (_ : s2f (tS2 :\: tS1) = sint (delta s) T.+1). 
    rewrite card_sint //.
    rewrite -(@leq_add2r (delta s)) -addnA subnK; last by rewrite ltnW.
    rewrite [s + _]addnC -ltnS -!addnS -deltaS !addnS.
    by rewrite -root_delta_lt [K + _]addnC -/s.
  by rewrite s2fD_isO // isOE // -sint_split.
(* This is 3.8 *)
have duz0_leq2 : psi (s2f E) - 2 ^ s.-1 <= `d[u, z0]_hmove.
  by apply: leq_trans duz0_leq; rewrite leq_subCl.
have [|K_gt0] := leqP K 0.
  rewrite leqn0 => /eqP KE0.
  have TE : T = N.
    apply/val_inj/eqP; rewrite eqn_leq [T <= _](ltn_ord T) /=.
    suff : N \notin E'' by rewrite inE NiE -leqNgt.
    suff -> : E'' = set0 by rewrite inE.
    by apply: cards0_eq.
  have x3Ircons : x3 \in rcons (behead (rcons z2b z2p)) z2.
    have : x3 \in g by rewrite gE x0sx0saE !(inE, mem_cat, eqxx, orbT).
    rewrite gE' z0sz0saE !(inE, mem_cat).
    case/or3P => // [/z0sbP0 | iIz2].
      by rewrite !inE negbK -TE x3T3 (negPf np3Dp0).
    have /z2aDp2 : x3 \in z2 :: z2a by rewrite inE iIz2 orbT.
      by rewrite !inE negbK -TE x3T3 (negPf np3Dp2).
  pose c := z2p N.
  have x0Ez0 : x0 = z0.
    congr last.
    move: gE; rewrite gE'; move:  x0sbP0 z0sbP0; rewrite TE.
    elim: (x0sb) (z0sb) => //=.
      move=> l1 _; elim: l1 => //= a l1 IH1 H [] aE.
      have := H _ (_ : a \in a :: l1).
      by rewrite aE -TE inE eqxx /= negbK (negPf x0sTD0) => /(_ isT).
    move=> a l1 IH1 [|b l2] /=.
      move=> H _ [] z0sE.
      have := H _ (_ : a \in a :: l1).
      by rewrite -z0sE negbK (negPf z0sND0) inE eqxx /= => /(_ isT).
    move=> H1 H2 [] -> H3; congr (_ :: _); apply: IH1 => //.
      by move=> i iH; apply: H1; rewrite inE iH orbT.
    by move=> i iH; apply: H2; rewrite inE iH orbT.
  case: (@peg4comp3 p0 np2 np3) => [|||p1 [[p1Dnp3 p1Dnp2 p1Dp0] Hz]];
      try by rewrite eq_sym.
  have cDnp2 : c != np2 by rewrite /c.
  have /peg4comp2[pp2 [pp3 [[H1 H2 H3] [H4 H5] H6]]] := cDnp2.
  pose a := if (pp2 \in [:: p0 ; np3]) && (pp3 \in [:: p0 ; p1])
            then pp2 else pp3.
  pose b := if (pp2 \in [:: p0 ; np3]) && (pp3 \in [:: p0 ; p1]) 
            then pp3 else pp2.
  have [aDc aD2 aDb bDc bDnp2] :
       [/\ a != c, a != np2, a != b, b != c & b != np2]. 
    by rewrite /a /b; case: (_ && _); split; rewrite // eq_sym.
  have /andP[aI bI] : (a \in [:: p0; np3]) && (b \in [:: p0; p1]).
    rewrite  /a /b !inE;
       case: (Hz c) cDnp2 H5 H4 H3 H2 H1 => ->; 
           rewrite /= ?(eqxx, andbT, andbF, orbT, orbF);
       case: (Hz pp2) => ->; rewrite /= ?(eqxx, andbT, andbF, orbT, orbF) ;
       case: (Hz pp3) => ->; rewrite /= ?(eqxx, andbT, andbF, orbT,orbF) //;
       rewrite ?[_ == p1]eq_sym ?[_ == np2]eq_sym ?[_ == np3]eq_sym;
       do 6 (case: eqP; rewrite ?eqxx ?orbT //=).
  have Hz1 p : [\/ p = np2, p = c, p = a | p = b].
    by rewrite /a /b; case: (_ && _); case: (H6 p);
       (exact: Or41 ||exact: Or42 || exact: Or43 || exact: Or44).
  pose A := [set i | ↓[z2] i == a].
  pose B := [set i | ↓[z2] i == b].
  have z2iD2 i : ↓[z2] i != np2.
    rewrite !ffunE -z2N2.
    by apply: move_on_toprDr z2pMz2 _ _ => //=.
  have z2iDc i : ↓[z2] i != c.
    rewrite /c ffunE.
    by apply: move_on_toprDl z2pMz2 _ _; rewrite //= ltnW.
  have ABE : A :|: B = setT.
    apply/setP=> i; rewrite !inE.
    by case: (Hz1 (↓[z2] i)) (z2iD2 i) (z2iDc i) => ->; rewrite eqxx ?orbT.
  (* This is 3.9 *)
  have psiAB_le :
      2 ^ ∇(T + K + 1) + psi `[n] <= (psi (s2f A) + psi (s2f B)).+1.*2.
    rewrite -leq_double -(leq_add2r 1) !doubleS !addSnnS.
    have := @psi_cap_ge (s2f A) (s2f B).
    rewrite -s2fU ABE s2f_setT card_sint subn0 => /(leq_trans _)-> //.
    rewrite phi_3_5_4_phi !psi_sintS addn1 ltnS leq_double.
    rewrite addnC -!addnA leq_add2l !addnA.
    rewrite KE0 TE addn0 addn1 -leq_double doubleD -!mul2n -!expnS.
    rewrite ![(troot _).-1.+1]prednK // expnS mul2n -addnn leq_add2l.
    by rewrite leq_pexp2l // troot_le.
  pose xa := if a == p0 then x0 else x3.
  have xaIrcons : xa \in z0 :: rcons (behead (rcons z2b z2p)) z2.
    by rewrite /xa; case: (_ == p0); rewrite !inE ?x0Ez0 ?eqxx // x3Ircons orbT.
  pose p1a := if a == p0 then p0 else np3.
  pose p2a := if a == p0 then x0s N else x3p N.
  have p1aDp2a : p1a != p2a.
    by rewrite /p1a /p2a; case: (a =P p0) => aP0 //; rewrite eq_sym -TE.
  have /peg4comp2[p3a [p4a [[p4aDp3a p4aDp2a p4aDp1a] [p3aDp2a p3aDp1a] p1aH]]]
         := p1aDp2a.
  have acodom : codom ↓[xa] \subset [:: p3a; p4a].
    apply/subsetP => i /codomP[j ->]; rewrite !inE.
    case: (p1aH (↓[xa] j)) => /eqP H; try by rewrite H ?orbT.
      rewrite -[_ == _]negbK in H; case/negP: H.
      rewrite /xa /p1a; case: (_ == p0); rewrite !ffunE -?x0T0 -?x3T3.
        by apply: (move_on_toplDl x0Mx0s x0TDx0sT); rewrite TE /=.
      apply: (move_on_toprDr x3pMx3 x3pTDx3T).
      by rewrite TE /=.
    rewrite -[_ == _]negbK in H; case/negP: H.
    rewrite /xa /p2a; case: (_ == p0); rewrite !ffunE -?x0T0 -?x3T3 -TE.
      by apply: (move_on_toplDr x0Mx0s x0TDx0sT); rewrite TE ltnW /=.
    apply: (move_on_toprDl x3pMx3 x3pTDx3T).
    by rewrite TE /= ltnW.
  have psiA_le :  psi (s2f A) <= `d[↓[xa], ↓[z2]]_hmove.
    rewrite gdistC //.
    apply: IH acodom; first by rewrite -ltnS.
    split => //.
      move: aI p4aDp1a p4aDp2a; rewrite !inE /p1a /p2a.
      by case eqP => [-> _|_ /= /eqP-> ].
    move: aI p3aDp1a p3aDp2a; rewrite !inE /p1a /p2a.
    by case eqP => [-> _|_ /= /eqP-> ].
  have bcodom : codom ↓[v] \subset [:: np2; np3].
    apply/subsetP => i; rewrite !inE => /codomP[j ->].
    rewrite !ffunE.
    have /subsetP /(_ (v (trshift 1 j))) := cH.
    by rewrite !inE; apply; apply: codom_f.
  move: (gH); rewrite gE' => /gdist_cat->; rewrite -/z0.
  have psiB_le :  psi (s2f B) <= `d[↓[z2], ↓[v]]_hmove.
    apply: IH bcodom; first by rewrite -ltnS. 
    split => //.
      by have := bI; rewrite !inE => /orP[] /eqP->; rewrite // eq_sym.
    by have := bI; rewrite !inE => /orP[] /eqP->; rewrite // eq_sym.
  have gH3 : gpath hmove z0 z2 (rcons (behead (rcons z2b z2p)) z2).
    move: gH; rewrite gE' z0sz0saE => /gpath_catr /gpath_catl.
    by rewrite last_rcons.
  have dz0z2_leq : (psi (s2f A)).+1 < `d[z0, z2]_hmove.
    rewrite (gpath_dist gH3) //.
    rewrite [size _](@path_shift _ _ _ 1 _ _ _ (gpath_path gH3)) //.
    rewrite -add2n; apply: leq_add.
      pose sx3 := @clshift _ 1 _ x3; pose sz2 := @clshift _ 1 _ z2.
      have  CD : #|[set i in [:: sx3; sz2]]| = 2.
        rewrite (cardsD1 sx3) (cardsD1 sz2); rewrite !inE !eqxx ?orbT /=.
        case: eqP => /= sz2Rsx3; last first.
          congr (S (S _)); apply: eq_card0 => i; rewrite !inE.
          by do 2 case: (_ == _).
        have /ffunP/(_ ord0) := sz2Rsx3.
        rewrite !ffunE (_ : tlshift _ _ = (ord_max : 'I_(1 + n))).
          move=> /eqP.
          by rewrite /= z2N2 -[ord_max]TE x3T3 eq_sym (negPf np3Dp2).
        by apply/val_eqP/eqP.
      rewrite -{1}CD.
      apply: size_rm_dup_subset => //.
        move=> i; rewrite !inE => /orP[]/eqP->; apply: map_f => //.
        by rewrite mem_rcons !inE eqxx.
      rewrite !inE negb_or; apply/andP; split; apply/eqP.
        move=> /ffunP /( _ ord_max) /eqP.
        rewrite !ffunE (_ : tlshift _ _ = (ord_max : 'I_(1 + n))) /=.
          by rewrite [z0 _]z0N0 -[ord_max]TE x3T3 eq_sym (negPf np3Dp0).
        by apply/val_eqP.
      move=> /ffunP /( _ ord_max) /eqP.
      rewrite !ffunE (_ : tlshift _ _ = (ord_max : 'I_(1 + n))) /=.
        by rewrite [z0 _]z0N0 [z2 _]z2N2 eq_sym (negPf np2Dp0).
      by apply/val_eqP.
    apply: leq_trans psiA_le _.
    rewrite /xa; case: (_ == p0).
      rewrite x0Ez0.
      apply: gdist_path_le.
      apply: @path_crshift _ _ 1 _ _ _ (gpath_path gH3).
      by rewrite last_rm_dup last_map last_rcons.
    move: gH3.
    case: (in_split x3Ircons) => l1 [l2 rE].
    rewrite rE -cat_rcons  => /gpath_catr.
    rewrite map_cat cat_rm_dup size_cat map_rcons !last_rcons => gH3.
    apply: leq_trans (leq_addl _ _).
      apply: gdist_path_le.
      apply: @path_crshift _ _ 1 _ _ _ (gpath_path gH3).
      rewrite last_rm_dup last_map.
      suff <- : last x3 (l1 ++ x3 :: l2) = last x3 l2 by rewrite -rE last_rcons.
      by rewrite last_cat.
  apply: leq_trans (leq_add duz0_leq2 (leqnn _)).
  move: (gH); rewrite gE' z0sz0saE => /gpath_catr /gdist_cat.
  rewrite last_rcons -/hmove -/z0 => ->; rewrite addnA.
  apply: leq_trans (leq_add (leqnn _)  (gdist_cunlift _)); last first.
    move: (gH); rewrite gE' z0sz0saE cat_rcons catA.
    move=> /gpath_catr /gpath_consr /gpath_path /path_connect.
    apply; rewrite /= -(gpath_last gH) gE' z0sz0saE !last_cat last_rcons.
    by apply: mem_last.
  apply: leq_trans (leq_add (leq_add (leqnn _) dz0z2_leq) psiB_le).
  rewrite -addnA addnC -leq_subLR.
  apply: leq_sub2l.
  rewrite !addSn -[(_ + _).+2]addn1 -leq_double doubleD.
  apply: leq_trans (leq_add psiAB_le (leqnn _)).
  by rewrite /s -mul2n -expnS prednK // addn1 -addnA leq_addr.
have TLN : T < N by apply: leq_trans KTE; rewrite -addn1 leq_add2l.
have NiE'' : N \in E'' by rewrite inE TLN NiE.
pose c : disk _ := z2p N.
case: (@peg4comp3 p0 np2 np3); rewrite // 1?eq_sym //.
move=> p1 [[p1Dnp3 p1Dnp2 p1Dp0] Hz].
have cI01 : c \in [:: p0; p1].
  rewrite !inE; case: (Hz c) => /eqP => [->//|||->]; rewrite ?orbT //.
    by rewrite /c -z2N2 (negPf z2pNDz2N).
  rewrite /c.
  suff /memE''/(_ NiE'')/negPf-> : z2p \in u :: g by [].
  rewrite gE' z0sz0saE.
  case: (z2b) z0Ez2p => [<- //|zz1 ll1 _].
    by rewrite /z0 -cat_cons mem_cat mem_last.
  by rewrite /= !(inE, mem_cat, mem_rcons, eqxx, orbT).
pose d : disk _ := x3p T.
have dD3 : d != np3 by rewrite /d -x3T3.
pose a : disk 4 := if d == np2 then c else np2.
pose b : disk 4 := if d == np2 then if c == p0 then p1 else p0
                   else if d == p0 then p1 else p0.
have aI2c : a \in [:: np2; c].
  by rewrite /a; case: (_ == _); rewrite !(inE, eqxx, orbT).
have bI01 : b \in [:: p0; p1].
  by rewrite /b; do 2 case: (_ == _); rewrite !(inE, eqxx, orbT).
have dDa : d != a.
  rewrite /a; case: (d =P np2) => [->|/eqP//].
  by move: cI01; rewrite !inE => /orP[] /eqP-> //; rewrite eq_sym.
have dDb : d != b.
  rewrite /b; case: (d =P np2) => [->|_].
    by case: (_ == p0); rewrite // eq_sym.
  by case: (d =P p0) => [->|/eqP//]; rewrite eq_sym.
have bD3 : b != np3.
  by move: bI01; rewrite !inE => /orP[] /eqP-> ;rewrite // eq_sym.
have bDa : b != a.
  rewrite /a /b; case: (_ =P p0) => [->|/eqP cDp0].
    case: (_ == np2) =>  [//|].
    by case: (_ == p0); rewrite // eq_sym.
  case: (_ == np2) =>  [//|]; first by rewrite eq_sym.
  by case: (_ == p0); rewrite // eq_sym.
have aD3 : a != np3.
  rewrite /a; case: (_ == np2); last by rewrite eq_sym.
  by move: cI01; rewrite !inE => /orP[] /eqP->; rewrite // eq_sym.
have Hza i : [\/ i = a, i = b, i = np3 | i = d].
  case: (Hz i) => ->.
  - rewrite /a /b; do 2 (case: eqP => [->|_] //).
    - by apply: Or41.
    - by apply: Or42.
    - by apply: Or44.
    by apply: Or42.
  - rewrite /a /b; do 2 (case: eqP => [->|_] //).
    - by apply: Or44.
    - by apply: Or44.
    - by apply: Or41.
    by apply: Or41.
  - by apply: Or43.
  rewrite /a /b; case: eqP => [->|/eqP dD2]; case: eqP => [->|/eqP cD0].
  - by apply: Or42.
  - move: cI01 cD0; rewrite !inE => /orP[]/eqP->; first by rewrite eqxx.
    by move=> _; apply: Or41.
  - by apply: Or42.
  case: (Hz d) dD2 cD0 dD3 => ->; rewrite ?eqxx //.
  by move=> *; apply: Or44.
move: (gE); rewrite gE' z0sz0saE x0sx0saE.
have tln : T <= n.+1 by apply: ltnW.
rewrite !cat_rcons !catA => /split_tail[[lE z2Ex3 _]|[zz z2aE]|[zz z2aE]]; 
   last 1 first.
- pose A := [set i | ccut tln x3 i == a].
  pose B := [set i | ccut tln x3 i == b].
  have AIB : A :&: B = set0.
    apply/setP => i; rewrite !inE !ffunE /=.
    case: eqP => [->|] //=.
    by rewrite eq_sym (negPf bDa).
  have AUB : A :|: B = setT.
    apply/setP => i; rewrite !inE !ffunE.
    have : ccut tln x3 i != np3.
      rewrite ffunE -x3T3.
      by apply: (move_on_toprDr x3pMx3) => /=.
    have : ccut tln x3 i != d.
      rewrite ffunE /d.
      by apply: (move_on_toprDl x3pMx3) => //; rewrite ltnW /=.
    by case: (Hza (ccut tln x3 i)); rewrite !ffunE => ->; rewrite ?(eqxx, orbT).
  have dz2x3_leq : psi (s2f A) <= `d[z2, x3]_hmove.
    rewrite gdistC //.
    have cDnp2 : c != np2 by rewrite /c.
    have /peg4comp2[pp1 [pp2 [[H1 H2 H3] [H4 H5] H6]]] := cDnp2.
    have cH1 : codom (ccut tln z2) \subset [:: pp1; pp2].
      apply/subsetP=> i /codomP[j]; rewrite !ffunE !inE => ->.
        case: (H6 (z2 (widen_ord tln j))) => /eqP; try by move->; rewrite ?orbT.
        rewrite /c -[_ == z2p _]negbK => /negP[].
        apply: (move_on_toprDl z2pMz2) => //=.
        by apply/ltnW/(leq_trans (ltn_ord _))/ltnW.
      rewrite -z2N2 -[_ == z2 _]negbK => /negP[].
      apply: (move_on_toprDr z2pMz2) => //=.
      by apply: (leq_trans (ltn_ord _)) => /=; apply: ltnW.
    apply: leq_trans (_ : `d[ccut tln x3, ccut tln z2]_hmove <= _).
      apply: IH cH1; first by apply/(leq_trans TLN _)/ltnW.
      split => //.
        move: aI2c; rewrite !inE.
        by case: (H6 a) => -> //; rewrite (negPf H2) (negPf H3).
      move: aI2c; rewrite !inE.
      case: (H6 a) => -> //; first by rewrite (negPf H4) (negPf H5).
      by move=> *; rewrite eq_sym.
    move: gH; rewrite gE' z0sz0saE z2aE.
    rewrite cat_rcons catA => /gpath_catr.
    rewrite -cat_cons -cat_rcons => /gpath_catl.
    rewrite rcons_cons => /gpath_consr; rewrite /= last_rcons.
    move=>/(gpathC (@hmove_sym _)).
    by apply: gpath_ccut.
  have dx3v_leq : psi (s2f B) <= `d[x3, v]_hmove.
    have cH1 : codom (ccut tln v) \subset [:: np2; np3].
      by apply: codom_cut.
    apply: leq_trans (_ : `d[ccut tln x3, ccut tln v]_hmove <= _).
      apply: IH cH1; first by apply: leq_trans TLN _; apply: ltnW.
      by have := bI01; rewrite !inE => /orP[] /eqP->; split; rewrite // eq_sym.
    move: gH; rewrite gE' z0sz0saE z2aE.
    rewrite cat_rcons catA => /gpath_catr.
    rewrite -cat_cons -cat_rcons => /gpath_catr.
    rewrite last_rcons.
    by apply: gpath_ccut.
  move: gH.
  rewrite gE' => {}gH; rewrite (gdist_cat gH) -/z0.
  have {}gH := gpath_catr gH; rewrite z0sz0saE in gH.
  apply: leq_trans (leq_add duz0_leq2 (leqnn _)).
  rewrite (gpath_dist gH) size_cat size_rcons addnCA addnA addSnnS.
  apply: leq_trans (leq_add (leq_addl _ _) (leqnn _)).
  have {}gH := gpath_catr gH; rewrite last_rcons in gH.
  rewrite -(gpath_dist gH); rewrite z2aE -cat_rcons in gH.
  rewrite (gdist_cat gH) last_rcons -/hmove.
  apply: leq_trans (leq_add (leqnn _) (leq_add dz2x3_leq dx3v_leq)).
  rewrite addSnnS.
  suff psiAB_le :  2 ^ s <= (psi (s2f A) + psi (s2f B)).+1.*2.
    rewrite -leq_double doubleD doubleB.
    apply: leq_trans (leq_add (leqnn _) psiAB_le).
    rewrite addnC -leq_subLR leq_sub2l //.
    by rewrite -mul2n -expnS prednK.
  rewrite -leq_double -mul2n -expnS -ltnS !doubleS -[_.+4]addn1 !addSnnS.
  apply: leq_trans _ (psi_cap_ge _ _).
    rewrite -s2fU AUB s2f_setT -(@isOE n.+1) //.
    rewrite card_s2f card_isO (minn_idPr _) //.
    rewrite phi_3_5_4_phi ltnS expnS mul2n leq_double.
    apply: leq_trans (psi_SS_le _).
    rewrite leq_exp2l // -[s]prednK // ltnS root_delta_le.
    have ->: delta s.-1 = delta s - s 
      by rewrite -{2}[s]prednK // deltaS prednK // addnK.
    have -> : T = (T + K).+1 - K.+1 :> nat by rewrite subSS addnK.
    apply: leq_sub; first by apply: delta_root_le.
    by rewrite root_delta_le deltaS -addnS leq_add2r.
- have z2pEx3 : z2p = x3p.
    rewrite /x3p /x0 -last_cat -lE.
    case: (z2b) z0Ez2p => [<-//|zz ll _] /=; first by rewrite /z0 cats0.
    by rewrite last_cat last_rcons.
  have /(move_disk1 z2pMz2 z2pNDz2N)/eqP : N != T by rewrite neq_ltn TLN orbT.
  by rewrite z2pEx3 z2Ex3 (negPf x3pTDx3T).
pose sd : {set disk n.+1} := isO n.+1 T.
have card_sdE : #|sd| = T.
  by rewrite card_isO /minn ifN // -leqNgt -ltnS ltnW // ltnW.
pose u'' := ccut tln u.
pose x0'' := ccut tln x0.
pose z2'' := ccut tln z2.
pose x3'' := ccut tln x3.
clear b bI01 dDb bD3 bDa Hza.
pose b := if c == p0 then p1 else p0.
have np3Dc : np3 != c.
  by move: cI01; rewrite !inE => /orP[] /eqP->; rewrite // eq_sym.
have np3Db : np3 != b.
  by move: cI01; rewrite /b !inE => /orP[] /eqP->; 
     rewrite ?(eqxx, negPf p1Dp0) // eq_sym.
have np2Dc : np2 != c.
  by move: cI01; rewrite !inE => /orP[] /eqP->; rewrite // eq_sym.
have np2Db : np2 != b.
  by move: cI01; rewrite /b !inE => /orP[] /eqP->; 
     rewrite ?(eqxx, negPf p1Dp0) // eq_sym.
have cDb : c != b.
  by move: cI01; rewrite /b !inE => /orP[] /eqP->; 
     rewrite ?(eqxx, negPf p1Dp0) // eq_sym.
have Hzb i : [\/ i = np3, i = np2, i = c | i = b].
  by  move: cI01; rewrite /b !inE => /orP[] /eqP->;
      rewrite ?(eqxx, negPf p1Dp0); case: (Hz i) => ->; 
     (try by apply: Or41); (try by apply: Or42);
     (try by apply: Or43); (try by apply: Or44).
have bI01 : b \in [:: p0; p1].
  by move: cI01; rewrite /b !inE => /orP[] /eqP->; 
     rewrite ?(eqxx, negPf p1Dp0) // eq_sym.
pose A : {set disk T} := [set i | z2'' i == np3].
pose B : {set disk n} := [set i | ↓[z2] i == b].
have cH2 : codom ↓[z2] \subset [:: np3; b].
  apply/subsetP=> i /codomP[j]; rewrite !ffunE !inE => ->.
  case: (Hzb (z2 (trshift 1 j))) => /eqP; try by move->; rewrite ?orbT.
    rewrite -[_ == np2]negbK -z2N2 => /negP[].
    by apply: (move_on_toprDr z2pMz2) => /=.
  rewrite -[_ == c]negbK /c => /negP[].
  by apply: (move_on_toprDl z2pMz2) => //=; apply: ltnW.
have bsI (i : disk n.+1) : i \in E'' :\ N -> z2 i = b.
  rewrite 2!inE; rewrite -val_eqE /= => /andP[iDn iIE'']; apply/eqP.
  have iLn : i < n.
    by move: (ltn_ord i); rewrite leq_eqVlt eqSS (negPf iDn).
  have /subsetP := cH2.
  move=> /(_ (↓[z2] (Ordinal iLn))(codom_f _ _)).
  rewrite !inE !ffunE /= (_ : trshift _ _ = (i : 'I_(1 + n))); last first.
    by apply: val_inj.
  rewrite (negPf (memE'' _ _ _ _)) //=.
  by rewrite gE' z0sz0saE !(inE, mem_cat, mem_rcons, eqxx, orbT).
have dz2''x3''_leq : psi (s2f A) <= `d[z2'', x3'']_hmove.
  pose a1 : peg 4 := x3p T.
  have a1Dnp3 : a1 != np3 by [].
  have /peg4comp2[pp1 [pp2 [[H1 H2 H3] [H4 H5] H6]]] := a1Dnp3.
  have cH3 : codom x3'' \subset [:: pp1; pp2].
    apply/subsetP=> i /codomP[j]; rewrite !ffunE !inE => ->.
    case: (H6 (x3 (widen_ord tln j))) => /eqP; try by move->; rewrite ?orbT.
      rewrite -[_ == a1]negbK => /negP[].
      by apply: (move_on_toprDl x3pMx3) => //=; apply: ltnW.
    rewrite -[_ == np3]negbK -x3T3 => /negP[].
    by apply: (move_on_toprDr x3pMx3) => /=.
  by apply: IH cH3 => //; apply/(leq_trans TLN)/ltnW.
have du''x0''_leq : psi (s2f E `&` `[T]) <= `d[u'', x0'']_hmove.
  have -> : s2f E `&` `[T] = s2f [set i | u'' i == p0].
    by rewrite -(@isOE n.+1) // -s2fI -s2f_ccut.
  have /peg4comp2[pp2 [pp3 [[H1 H2 H3] [H4 H5] H6]]] := x0sTD0.
  have cH1 : codom x0'' \subset [:: pp2; pp3].
    apply/subsetP=> i /codomP[j]; rewrite !inE !ffunE => ->.
    case: (H6 (x0 (widen_ord tln j))) => /eqP; try by move->; rewrite ?orbT.
      rewrite -[_ == x0s T]negbK => /negP[].
      by apply: (move_on_toplDr x0Mx0s) => //=; apply: ltnW.
    rewrite -[_ == p0]negbK -x0T0 => /negP[].
    by apply: (move_on_toplDl x0Mx0s) => /=.
  by apply: IH cH1=> //; apply/(leq_trans TLN _)/ltnW.
have psiAB_leq : psi `[T + K + 1] <= (psi (s2f A) + psi (s2f B)).+1.*2.
  rewrite -leq_double psi_sint_phi -ltnS prednK ?phi_gt0 //.
  have ->: (T + K + 1).+1 = (T + K).-1.+3.
    rewrite -{1}[T + K]prednK ?addn1 ?addnS ?addn_gt0 ?K_gt0 ?orbT //.
  have : (T + K).-1 <= #|` (s2f A) `|` (s2f B)|.
     have : (`[T] `|` (s2f (E'' :\ N))) `<=` ((s2f A) `|` (s2f B)).
      apply/fsubsetP => i; rewrite inE mem_sint /=.
      case/orP => [iLT|iIEN]; last first.
        have iLn : i < n.
          move: iIEN; rewrite s2fD !inE s2f1 //= in_fset1.
          case/andP=> iDn /imfsetP[/= j _ iEj].
          by have := ltn_ord j; rewrite -iEj leq_eqVlt eqSS (negPf iDn).
        rewrite inE; apply/orP; right.
        rewrite (@mem_s2f _ _ (Ordinal iLn)) inE !ffunE; apply/eqP.
        by apply: bsI; rewrite -mem_s2f.
      have iLn : i < n by apply: leq_trans iLT (ltnW _).
      have /subsetP/(_ (↓[z2] (Ordinal iLn))(codom_f _ _)) := cH2.
      rewrite !inE !ffunE /=.
      rewrite (@mem_s2f _ _ (Ordinal iLn)) inE ffunE.
      rewrite (@mem_s2f _ _ (Ordinal iLT)) inE ffunE.
      rewrite (_ : trshift _ _ = widen_ord tln (Ordinal iLT) :> 'I_(1 + n)) //.
      by apply: val_inj.
    move => /fsubset_leq_card /(leq_trans _)->//.
    rewrite -(leq_add2r 0) addn0.
    suff {2}<- : #|` `[T] `&` s2f (n:=n.+1) (E'' :\ N)| = 0.
      rewrite cardfsUI card_sint subn0 card_s2f /K (cardsD1 N).
      by rewrite NiE'' addnS.
    apply/eqP; rewrite cardfs_eq0; apply/eqP/fsetP => i.
    rewrite !inE mem_sint; apply/idP => /= /andP[iLT /imfsetP[j /=]].
    rewrite !inE => /and3P[_ _ TLj] iEj.
    by move: iLT; rewrite ltnNge ltnW // iEj.
  rewrite -3!ltnS => /phi_le/leq_trans-> //.
  rewrite !doubleS -[_.+4]addn1 !addSnnS.
  by apply: psi_cap_ge.
Admitted.

End Hanoi4.


