From mathcomp Require Import all_ssreflect finmap.
Require Import zify extra star gdist ghanoi ghanoi4 shanoi.

Open Scope nat_scope.

Set Implicit Arguments.
Unset Strict Implicit.

(******************************************************************************)
(*                                                                            *)
(*  This file proves the formula that gives the distance between two perfect  *)
(*  configurations for the star puzlle. It follows the proof given by Thierry *)
(*  Bousch in  La tour de Stockmeyer                                          *)
(*                                                                            *)
(*                                                                            *)
(******************************************************************************)

Lemma sum3E n (f : nat -> nat) : 
  \sum_(i < 3 * n) f i =
  \sum_(i < n) (f (3 * i) + f (3 * i).+1 + f (3 * i).+2).
Proof.
elim: n => [|n IH]; first by rewrite !big_ord0.
by rewrite mulnS !big_ord_recr /= IH !addnA.
Qed.

Section sHanoi4.

Let srel : rel (peg 4) := @srel 4.
Let hirr : irreflexive srel := @sirr 4.
Let hsym : symmetric srel := @ssym 4.

Let smove {n} := @move 4 srel n.
Let smove_sym n (c1 c2 : configuration 4 n) : smove c1 c2 = smove c2 c1
  := move_sym hsym c1 c2.
Let hconnect n := connect (@smove n).

Local Notation "c1 `--> c2" := (smove c1 c2)
    (format "c1  `-->  c2", at level 60).
Local Notation "c1 `-->* c2" := (hconnect c1 c2) 
    (format "c1  `-->*  c2", at level 60).
Local Notation "`c[ p ] " := (perfect p )
    (format "`c[ p ]", at level 60).
Local Notation "`cf[ p , n ] ":= (perfect p : configuration _ n).

Local Notation " d[ a , b ] " := (gdist smove a b)
  (format " d[ a ,  b ]").

Fixpoint distanceL n (l : seq (configuration 4 n)) : nat := 
  if l is a :: l1 then
    if l1 is b :: _ then d[a, b] + distanceL l1
    else 0
  else 0.

Notation " D[ l ] " := (distanceL l)
  (format " D[ l ]").

Definition apeg n p1 p2 : peg 4 := if odd n then p2 else p1.

Let p0 : peg 4 := ord0.

Lemma gdist_cunlift_eq k n (r : rel (peg k)) (c1 c2 : configuration k n.+1) : 
  irreflexive r ->
  connect (move r) c1 c2 ->  c1 ldisk = c2 ldisk ->
    `d[c1, c2]_(move r) = `d[↓[c1], ↓[c2]]_(move r).
Proof.
move=> ir c1Cc2 c1Ec2; apply/eqP; rewrite eqn_leq gdist_cunlift // andbT.
rewrite -{1}[c1]cunliftrK -{1}[c2]cunliftrK -c1Ec2.
apply: gdist_liftr => //.
case/connectP: c1Cc2 => p pH c2E.
apply/connectP; exists (rm_rep (cunliftr c1) ([seq ↓[i] | i <- p])) => //.
  by apply: path_unlift.
by rewrite last_rm_rep c2E last_map.
Qed.

Lemma pE4 (p1 p2 p3 : peg 4) p : 
   p1 != p2 -> p1 != p3 -> p2 != p3 -> 
   p1 != p0 -> p2 != p0 -> p3 != p0 ->
  [\/ p = p0, p = p1, p = p2 | p = p3].
Proof. 
rewrite /p0.
by case: (peg4E p1) => ->; rewrite ?eqxx //; 
   case: (peg4E p2) => ->; rewrite ?eqxx //; 
   case: (peg4E p3) => ->; rewrite ?eqxx //; 
   case: (peg4E p) => ->; rewrite ?eqxx // => *; 
   try ((by apply: Or41) || (by apply: Or42) || 
        (by apply: Or43) || (by apply: Or44)).
Qed.

(* This is lemma 2.1 *)
Lemma sgdist_simple n (p2 : peg 4) (u v : configuration 4 n.+1) 
    (p1 := u ldisk) (p3 := v ldisk): 
   p1 != p2 -> p1 != p3 -> p2 != p3 -> 
   p1 != p0 -> p2 != p0 -> p3 != p0 ->
   {st : (configuration 4 n * configuration 4 n) |
     [/\ codom st.1 \subset [:: p2; p3], codom st.2 \subset [:: p1; p2] & 
         d[u, v] = D[[:: cunliftr u; st.1; st.2; cunliftr v]].+2]}.
Proof.
move=> p1Dp2 p1Dp3 p2Dp3 p1Dp0 p2Dp0 p3Dp0.
have pE p : [\/ p = p0, p = p1, p = p2 | p = p3] by apply: pE4.
have [cs /= csH] := gpath_connect (shanoi_connect u v).
have vIcs : v \in cs.
  have := mem_last u cs; rewrite (gpath_last csH).
  rewrite inE; case: eqP => //  vEu.
  by case/eqP : p1Dp3; rewrite /p3 vEu.
case: (@split_first _ cs (fun c => c ldisk != p1)) => [|[[sp cs1] cs2]].
  apply/negP=> /allP /(_ _ vIcs).
  rewrite /= -topredE /= negbK.
  by rewrite eq_sym (negPf p1Dp3).
case=> /allP spH spLE csE.
pose s := last u cs1.
have sMsp : s `--> sp.
  by have := gpath_path csH; rewrite csE cat_path => /and3P[].
have sLp1 : s ldisk = p1.
  move: (spH s); rewrite /s; case: (cs1) => //= c cs3 /(_ (mem_last _ _)).
  by rewrite -topredE negbK => /eqP.
have spLp0 : sp ldisk = p0.
  apply/eqP.
  have /(_ ldisk) := move_diskr sMsp.
  rewrite eq_sym sLp1 => /(_ spLE) /andP[].
  case: (_ =P p0) => // /val_eqP /=.
  have /eqP/val_eqP/= := p1Dp0.
  by case: (p1 : nat) => // k; case: (sp _ : nat).
have sCd : codom (cunliftr s) \subset [:: p2; p3].
  apply/subsetP=> i; rewrite !inE => /codomP[j] ->.
  case: (pE (cunliftr s j)) => [||->|->]; rewrite ?eqxx ?orbT //.
    rewrite ffunE trshift_lift /=.
    move/eqP; rewrite -spLp0 -[_ == _]negbK; case/negP.
    apply: move_on_toplDr sMsp _ _; first by rewrite sLp1 spLp0.
    by rewrite /= /bump [n <= j]leqNgt ltn_ord add0n ltnW.
  rewrite ffunE trshift_lift /=.
  move/eqP; rewrite -sLp1 -[_ == _]negbK; case/negP.
  apply: move_on_toplDl sMsp _ _; first by rewrite sLp1 spLp0.
  by rewrite /= /bump [n <= j]leqNgt ltn_ord add0n.
have vIcs2 : v \in cs2.
  move: vIcs; rewrite csE !(inE, mem_cat) => /or3P[|/eqP vEs|] //.
    by move=> /spH; rewrite /= -topredE negbK eq_sym (negPf p1Dp3).
  by case/eqP : p3Dp0; rewrite /p3 vEs.
case: (@split_last _ (sp :: cs2) (fun c => c ldisk != p3)) => 
     [|/= [[t cs3] cs4]/=].
  apply/negP=> /allP /(_ _ (mem_head _ _)).
  by rewrite /= -topredE /= negbK spLp0 eq_sym (negPf p3Dp0).
case=> // tLE tH scs2E.
have vIcs4 : v \in cs4.
  have := gpath_last csH; rewrite csE scs2E !last_cat /=.
  case: (cs4) => /= [tEv|c1 cs5 <-]; last by apply: mem_last.
  by case/eqP: tLE; rewrite tEv.
  case: cs4 tH scs2E vIcs4 => // tp cs4 /allP tH scs2E vItpcs4.
have tMtp : t `--> tp.
  by have := gpath_path csH; rewrite csE scs2E !cat_path /= => /and5P[].
have tpLp3 : tp ldisk = p3.
  by move: (tH _ (mem_head _ _)); rewrite /= -topredE negbK => /eqP.
have tLp0 : t ldisk = p0.
  apply/eqP.
  have /(_ ldisk) := move_diskr tMtp.
  rewrite tpLp3 => /(_ tLE) /andP[].
  case: (_ =P p0) => // /val_eqP /=.
  have /eqP/val_eqP/= := p3Dp0.
  by case: (p3 : nat) => // k; case: (t _ : nat).
have tCd : codom (cunliftr t) \subset [:: p1; p2].
  apply/subsetP=> i; rewrite !inE => /codomP[j] ->.
  case: (pE (cunliftr t j)) => [|->|->|]; rewrite ?eqxx ?orbT //.
    rewrite ffunE trshift_lift /=.
    move/eqP; rewrite -tLp0 -[_ == _]negbK; case/negP.
    apply: move_on_toplDl tMtp _ _; first by rewrite tpLp3 tLp0 eq_sym.
    by rewrite /= /bump [n <= j]leqNgt ltn_ord add0n.
  rewrite ffunE trshift_lift /=.
  move/eqP; rewrite -tpLp3 -[_ == _]negbK; case/negP.
  apply: move_on_toplDr tMtp _ _; first by rewrite tpLp3 tLp0 eq_sym.
  by rewrite /= /bump [n <= j]leqNgt ltn_ord add0n ltnW.
exists (cunliftr s, cunliftr t); split => //=.
rewrite addn0.
move: csH; rewrite csE => csH.
rewrite (gdist_cat csH) -[@move _ _ _]/smove -/s.
move: csH => /gpath_catr; rewrite -/s => csH.
rewrite gdist_cunlift_eq //; last by apply: shanoi_connect.
rewrite -!addnS.
congr (_ + _).
have ->: cunliftr s = cunliftr sp.
  have sLDspL : s ldisk != sp ldisk by rewrite sLp1 spLp0.
  apply/ffunP => i; rewrite !ffunE.
  apply: move_disk1 sMsp sLDspL _.
  by apply/negP => /eqP/val_eqP /=; rewrite eqn_leq leqNgt ltn_ord.
rewrite (gdist_cons csH) addnS; congr (_).+1.
move: csH => /gpath_consr csH.
have ctEctp : cunliftr t = cunliftr tp.
  have tLDtpL : t ldisk != tp ldisk by rewrite tLp0 tpLp3 eq_sym.
  apply/ffunP => i; rewrite !ffunE.
  apply: move_disk1 tMtp tLDtpL _.
  by apply/negP => /eqP/val_eqP /=; rewrite eqn_leq leqNgt ltn_ord.
case: cs3 scs2E => [[spEt cs2E]|c3 cs3 /= [spE cs2E]].
  move: csH; rewrite spEt cs2E => csH.
  rewrite gdist0 add0n (gdist_cons csH) ctEctp.
  move: csH => /gpath_consr csH.
  rewrite gdist_cunlift_eq //.
  by apply: shanoi_connect.
move: csH; rewrite cs2E -cat_rcons => csH.
rewrite (gdist_cat csH) last_rcons.
rewrite gdist_cunlift_eq //; last 2 first.
- by apply: shanoi_connect.
- by rewrite tLp0.
congr (_ + _).
move: csH => /gpath_catr; rewrite last_rcons => csH.
rewrite (gdist_cons csH); congr (_).+1.
move: csH => /gpath_consr csH.
rewrite ctEctp gdist_cunlift_eq //.
by apply: shanoi_connect.
Qed.

Definition beta n l k := 
  if ((1 < l) && (k == n.-1)) then α_[l] k else (α k).*2.

Lemma leq_beta n l k : α_[l] k <= beta n l k.
Proof.
rewrite /beta; case: (_ < _) => /=; last by apply: bound_alphaL.
by case: (_ == _) => //=; apply: bound_alphaL.
Qed.

Lemma geq_beta n l k : beta n l k <= (α k).*2.
Proof.
rewrite /beta; case: (_ < _) => //=.
by case: (_ == _) => //=; apply: bound_alphaL.
Qed.

Lemma S0E n : S_[0] n = 0.
Proof.
rewrite /dsum_alphaL /conv.
elim: n => /= [|n ->]; first by rewrite dsum_alpha_0.
by rewrite minn0.
Qed.

Let d0 {n}:= (ord0 : disk n.+1).

Lemma disk1_all (d : disk 1) : d = d0.
Proof. by apply/val_eqP; case: d => [] []. Qed.

Lemma configuration1_eq k (c1 c2 : configuration k 1) : 
  (c1 == c2) = (c1 d0 == c2 d0).
Proof.
apply/eqP/eqP; first by move=> /ffunP/(_ d0).
by move=> H; apply/ffunP=> i; rewrite [i]disk1_all.
Qed.

Lemma Ival_eq n (x y : 'I_n) : (x == y) = (val x == val y).
Proof. by apply/eqP/val_eqP. Qed.

Lemma dsum_alphaL_S l n : S_[l] n.+1 = S_[l] n + α_[l] n.
Proof. by rewrite addnC subnK //; case: (convex_dsum_alphaL l). Qed.

Lemma alphaL_0 l : α_[l] 0 = minn 2 l.
Proof.
rewrite /alphaL /delta /dsum_alphaL /conv /= dsum_alpha_1 dsum_alpha_0.
by rewrite muln0 addn0 add0n subn0 muln1.
Qed.

(* This corresponds to 4.1 *)
Section Case1.

Variable m : nat.
Hypothesis IH: forall n : nat,
     n <= m ->
     forall (l : nat) (p1 p2 p3 : ordinal_eqType 4)
       (u : {ffun 'I_l.+1 -> configuration 4 n}),
     p1 != p2 ->
     p1 != p3 ->
     p2 != p3 ->
     p1 != p0 ->
     p2 != p0 ->
     p3 != p0 ->
     (forall k : 'I_l.+1,
      0 < k < l -> codom (u k) \subset [:: p2; apeg k p1 p3]) ->
     (S_[l] n).*2 <=
     \sum_(i < l)  d[u (inord i), u (inord i.+1)] +
     \sum_(k < n) (u ord0 k != apeg 0 p1 p3) * beta n l k +
     \sum_(k < n) (u ord_max k != apeg l p1 p3) * beta n l k.

Lemma sum_beta_S n l a : 1 < l ->
  \sum_(k < n.+1) a k * beta n.+1 l k =
   \sum_(k < n) (a (widen_ord (leqnSn n) k) * (α k).*2) + a ord_max * α_[l] n.
Proof.
move=> l_gt1.
rewrite big_ord_recr /= /beta l_gt1 eqxx /=; congr (_ + _).
apply: eq_bigr => i _; congr (_ * _).
by rewrite eqn_leq [_ <= i]leqNgt ltn_ord andbF.
Qed.

Lemma leq_sum_beta n l a : 
  \sum_(k < n) a k * beta n l k <= \sum_(k < n) a k * (α k).*2.
Proof.
by apply: leq_sum => i _; rewrite leq_mul2l geq_beta orbT.
Qed.

Variable n : nat.
Hypothesis nLm : n.+1 < m.+1.
Variable l : nat.
Variables p1 p2 p3: peg 4.
Variable u : {ffun 'I_l.+2 -> configuration 4 n.+2}.
Hypothesis p1Dp2 : p1 != p2.
Hypothesis p1Dp3 : p1 != p3.
Hypothesis p2Dp3 : p2 != p3.
Hypothesis p1Dp0 : p1 != p0.
Hypothesis p2Dp0 : p2 != p0.
Hypothesis p3Dp0 : p3 != p0.
Hypothesis cH : forall k : 'I_l.+2,
     0 < k < l.+1 -> codom (u k) \subset [:: p2; apeg k p1 p3].

Let u':= ([ffun i => ↓[u i]] : {ffun 'I_l.+2 -> configuration 4 n.+1})
 : {ffun 'I_l.+2 -> configuration 4 n.+1}.

Let H: forall k : 'I_l.+2,
    0 < k < l.+1 -> codom (u' k) \subset [:: p2; apeg k p1 p3].
Proof. by move=> k kH; rewrite ffunE; apply/codom_liftr/cH. Qed.

Hypothesis KH1 : u ord0 ord_max = apeg 0 p1 p3.
Hypothesis KH2 : u ord_max ord_max != apeg l.+1 p1 p3.
Hypothesis l_gt0 : l != 0.

Lemma case1 :
  (S_[l.+1] n.+2).*2 <= 
  \sum_(i < l.+1)  d[u (inord i), u (inord i.+1)] +
  \sum_(k < n.+2) (u ord0 k != apeg 0 p1 p3) * beta n.+2 l.+1 k +
  \sum_(k < n.+2) (u ord_max k != apeg l.+1 p1 p3) * beta n.+2 l.+1 k.
Proof.
have il1E : inord l.+1 = ord_max :> 'I_l.+2
  by apply/val_eqP; rewrite /= inordK.
have iE : exists i, u (inord i) ord_max != apeg i p1 p3.
  by exists l.+1; rewrite il1E.
case: (@ex_minnP _ iE) => a aH aMin.
have aMin1 i : i < a -> u (inord i) ord_max = apeg i p1 p3.
  by case: (u (inord i) ord_max =P apeg i p1 p3) => // /eqP /aMin; case: leqP.
have aLld1 : a <= l.+1 by apply: aMin; rewrite il1E.
pose ai : 'I_l.+2 := inord a.
have aiE : ai = a :> nat by rewrite inordK.
pose b := l.+1 - a.
pose bi : 'I_l.+2 := inord b.
have biE : bi = b :> nat by rewrite inordK // /b ltn_subLR // leq_addl.
have [/andP[a_gt1 aLlm1]|] := boolP (2 <= a <= l.-1).
  have aLl : a <= l by rewrite (leq_trans aLlm1) // -subn1 leq_subr.
  have a_gt0 : 0 < a by rewrite (leq_trans _ a_gt1).
  have l_ggt0 : 0 < l by rewrite (leq_trans _ aLl) //.
  have b_gt1 : 1 < b by rewrite leq_subRL // addn2 ltnS -[l]prednK.
  have uaiLEp2 : u ai ldisk = p2.
    have /cH/subsetP/(_ (u ai ldisk) (codom_f _ _)) : 0 < ai < l.+1.
      by rewrite aiE (leq_trans _ a_gt1) //= ltnS (leq_trans aLl1)
                 // ssrnat.leq_pred.
    by rewrite !inE aiE (negPf aH) orbF => /eqP.
  have F (i : 'I_a.-2.+1) : 
   let u1 := u (inord i) in let u2 := u (inord i.+1) in
   {st : (configuration 4 n.+1 * configuration 4 n.+1) |
     [/\ codom st.1 \subset [:: p2; u2 ldisk ], 
         codom st.2 \subset [:: u1 ldisk; p2] & 
         d[u1, u2] = 
           D[[:: cunliftr u1; st.1; st.2; cunliftr u2]].+2]}.
    have iLa : i < a.-1.
      by have := ltn_ord i; rewrite {2}[a.-2.+1]prednK // -ltnS prednK.
    have iLa1 : i < a by rewrite (leq_trans iLa) // ssrnat.leq_pred.
    apply: sgdist_simple => //.
    - by rewrite aMin1 // /apeg; case odd; rewrite // eq_sym.
    - rewrite !aMin1 //; last by rewrite -{2}[a]prednK.
      by rewrite /apeg /=; case: odd; rewrite // eq_sym.
    - rewrite aMin1; last by rewrite -{2}[a]prednK.
      by rewrite /apeg /=; case: odd; rewrite // eq_sym.
    - by rewrite aMin1 // /apeg /=; case: odd; rewrite // eq_sym.
    rewrite aMin1; last by rewrite -{2}[a]prednK.
    by rewrite /apeg /=; case: odd; rewrite // eq_sym.
  pose si i : configuration 4 n.+1 := let: (exist (x, _) _) := F i in x.
  pose ti i : configuration 4 n.+1 := let: (exist (_, x) _) := F i in x.  
  have [[sam1 tam1] /= [sam1C tam1E duam1ua1E]] : 
   let u1 := u (inord a.-1) in let u2 := u ai in
   {st : (configuration 4 n.+1 * configuration 4 n.+1) |
     [/\ codom st.1 \subset [:: apeg a p1 p3; u2 ldisk ], 
         codom st.2 \subset [:: u1 ldisk; apeg a p1 p3] & 
         d[u1, u2] = 
           D[[:: cunliftr u1; st.1; st.2; cunliftr u2]].+2]}.
    apply: sgdist_simple => //.
    - rewrite aMin1 ?prednK // /apeg -{2}[a]prednK //=.
      by case: odd; rewrite // eq_sym.
    - by rewrite uaiLEp2 aMin1 ?prednK // /apeg; case: odd; rewrite // eq_sym.
    - by rewrite uaiLEp2 /apeg; case: odd; rewrite // eq_sym.
    - by rewrite aMin1 ?prednK // /apeg; case: odd; rewrite // eq_sym.
    - by rewrite /apeg; case: odd.
    by rewrite uaiLEp2. 
  pose u1 := 
    [ffun i =>
    if ((i : 'I_(3 * a).-2.+1) == 3 * a.-1 :>nat) then ↓[u (inord a.-1)] 
    else if (i == (3 * a.-1).+1 :>nat) then sam1
    else if (i %% 3) == 0 then ↓[u (inord (i %/ 3))]
    else if (i %% 3) == 1 then si (inord (i %/ 3))
    else ti (inord (i %/ 3))].
  have u10E : u1 ord0 = cunliftr (u ord0).
    rewrite ffunE /= ifN.
      by rewrite (_ : inord 0 = ord0); last by apply/val_eqP; rewrite /= inordK.
    by rewrite neq_ltn muln_gt0 /= -ltnS prednK //= a_gt1.
  have uiME : u1 ord_max = sam1.
    rewrite ffunE /= eqn_leq leqNgt -{2}[a]prednK // mulnS.
    rewrite addSn add2n ltnS leqnn /=.
    by rewrite -{1}[a]prednK // mulnS eqxx.
  pose u2 := 
    [ffun i =>  
    if (i : 'I_3) == 0 :> nat then sam1 else
    if i == 1 :> nat then tam1 else ↓[u ai]].
  pose u3 := [ffun i => ↓[u (inord ((i : 'I_b.+1) + a))]].
  have P1 : 
    a.*2 +
    \sum_(i < (3 * a).-2) 
        d[u1 (inord i), u1 (inord i.+1)] +
    \sum_(i < 2) 
        d[u2 (inord i), u2 (inord i.+1)] +
    \sum_(i < b)  d[u3 (inord i), u3 (inord i.+1)] 
    <= 
    \sum_(i < l.+1) d[u (inord i), u (inord i.+1)].
    have G b1 : b1 = a ->  
      \sum_(i < (3 * b1).-2) d[u1 (inord i), u1 (inord i.+1)] =
      \sum_(i < (3 * a.-1)) d[u1 (inord i), u1 (inord i.+1)] +
      d[↓[u (inord a.-1)], sam1].
      move=> b1Ea.
      have ta2E : (3 * b1).-2 = (3 * a.-1).+1.
        by rewrite b1Ea -{1}[a]prednK // mulnS.
      rewrite ta2E big_ord_recr /=; congr (_ + d[_,_]).
        by rewrite ffunE ifT// inordK // -{2}b1Ea ?ta2E.
      rewrite ffunE inordK; last by rewrite -{2}b1Ea ?ta2E.
      by rewrite eqn_leq ltnn /= eqxx.
    rewrite {}G //.
    have -> := @sum3E _ (fun i => d[u1 (inord i), u1 (inord i.+1)]).
    have -> : a.*2 = 2 + \sum_(i < a.-1) 2.
      rewrite sum_nat_const /= cardT size_enum_ord.
      by rewrite muln2 -(doubleD 1) add1n prednK.
    rewrite !addnA -[2 + _ + _]addnA -big_split /=.
    rewrite [2 + _]addnC -!addnA 2![X in _ + X <= _]addnA addnA.
    have -> : \sum_(i < l.+1)  d[u (inord i), u (inord i.+1)] =
      \sum_(i < a.-1) (d[u (inord i), u (inord i.+1)]) + 
      d[u (inord a.-1), u ai] +
      \sum_(i < b) d[u (inord (a +i)), u (inord (a + i.+1))].
      have <- := big_mkord xpredT (fun i => d[u (inord i), u (inord i.+1)]).
      rewrite (big_cat_nat _ _ _ (_ : _ <= (a.-1).+1)) //=; last first.
         by rewrite prednK.
      rewrite big_mkord big_ord_recr /= prednK //.
      rewrite -{9}[a]add0n big_addn -/b big_mkord.
      congr (_ + _ + _).
      by apply: eq_bigr => i; rewrite addnC addnS.
    apply: leq_add; first apply: leq_add.
    - rewrite leq_eqVlt; apply/orP; left; apply/eqP.
      apply: eq_bigr => i _.
      have -> : u1 (inord (3 * i)) = ↓[u (inord i)].
        rewrite ffunE inordK; last first.
          rewrite ltnS (leq_trans (_ : _ <= 3 * (a.-1))) //.
            by rewrite leq_mul2l /= ltnW.
          by rewrite -{2}[a]prednK // mulnS addSn add2n /= ltnW.
        rewrite eqn_mul2l /= eqn_leq [_ <= i]leqNgt ltn_ord andbF.
        rewrite eqn_leq ltn_mul2l /= ltnNge [i <= _]ltnW // andbF.
        by rewrite modnMr eqxx mulKn.
      have -> : u1 (inord (3 * i).+1) = si (inord i).
        rewrite ffunE inordK; last first.
          rewrite ltnS (leq_trans (_ : _ <= 3 * (a.-1))) //.
            by rewrite ltn_mul2l /=.
          by rewrite -{2}[a]prednK // mulnS addSn add2n /= ltnW.
        rewrite eqn_leq [_ <= _.+1]leqNgt.
        rewrite (leq_trans (_ : (3 * i).+2 <= (3 * i.+1))) ?andbF //;
               last 2 first.
        - by rewrite mulnS addSn add2n.
        - by rewrite leq_mul2l /=.
        rewrite eqn_leq !ltnS [_ <= 3 * i]leq_mul2l.
        rewrite [_ <= i]leqNgt ltn_ord andbF.
        have ->: (3 * i).+1 %% 3 = 1.
          rewrite -addn1 mulnC modnMDl //.
        suff ->: (3 * i).+1 %/ 3 = i by [].
        rewrite -addn1 mulnC divnDl //.
          by rewrite mulnK // divn_small // addn0.
        by rewrite dvdn_mull // dvdnn.
      have -> : u1 (inord (3 * i).+2) = ti (inord i).
        rewrite ffunE inordK; last first.
          rewrite ltnS (leq_trans (_ : _ <= 3 * (a.-1))) //.
            rewrite (leq_trans (_ : _ <= 3 * (i.+1))) //.
              by rewrite mulnS addSn add2n.
            by rewrite leq_mul2l /=.
          by rewrite -{2}[a]prednK // mulnS addSn add2n /= ltnW.
        rewrite eqn_leq [_ <= _.+1]leqNgt.
        rewrite -[(3 * i).+3](mulnDr 3 1 i) leq_mul2l ltn_ord andbF.
        rewrite eqn_leq !ltnS [_ <= _.+1]leqNgt.
        rewrite (leq_trans (_ : (3 * i).+1 < 3 * (i.+1))) ?andbF //;
             last 2 first.
        - by rewrite mulnS addSn add2n.
        - by rewrite leq_mul2l /=.
        have ->: (3 * i).+2 %% 3 = 2.
          rewrite -addn2 mulnC modnMDl //.
        suff ->: (3 * i).+2 %/ 3 = i by [].
        rewrite -addn2 mulnC divnDl //.
          by rewrite mulnK // divn_small // addn0.
        by rewrite dvdn_mull // dvdnn.
      have -> : u1 (inord (3 * i).+3) = ↓[u (inord i.+1)].
        have -> : (3 * i).+3 = 3 * (i.+1) by rewrite mulnS addSn add2n.
        rewrite ffunE inordK; last first.
          rewrite ltnS (leq_trans (_ : _ <= 3 * (a.-1))) //.
            by rewrite leq_mul2l /=.
          by rewrite -{2}[a]prednK // mulnS addSn add2n /= ltnW.
        rewrite eqn_mul2l /=; case: eqP => [->//|_].
        rewrite eqn_leq [_ <= 3 * i.+1]leqNgt ltnS leq_mul2l /= ltn_ord andbF.
        by rewrite modnMr mulKn.
      rewrite /si /ti; case: (F) => [] [s t] [_ _].
      rewrite inordK => [->|]; last by rewrite prednK // -ltnS prednK.
      by rewrite add2n /= addn0 !addnA.
    - rewrite leq_eqVlt; apply/orP; left; apply/eqP.
      rewrite !big_ord_recr big_ord0 //= add0n !addnA.
      have -> : u2 (inord 0) = sam1 by rewrite ffunE /= inordK.
      have -> : u2 (inord 1) = tam1 by rewrite ffunE /= inordK.
      have -> : u2 (inord 2) = ↓[u ai] by rewrite ffunE /= inordK.
      by move: duam1ua1E; rewrite addn0 add2n !addnA !addSn.
    apply: leq_sum => i _.
    rewrite ffunE inordK; last by rewrite ltnS ltnW.
    rewrite ffunE inordK; last by rewrite ltnS.
    rewrite addSn [i + _]addnC addnS.
    by apply/gdist_cunlift/shanoi_connect.
  set x1P1 := \sum_(_ < _) _ in P1.
  set x2P1 := \sum_(_ < _) _ in P1.
  set x3P1 := \sum_(_ < _) _ in P1.
  set xP1 := \sum_(_ < _) _ in P1.
  rewrite -/xP1.
  have cH2 (k : 'I_(3 * a).-2.+1) : 
      0 < k < (3 * a).-2 -> codom (u1 k) \subset [:: p2; apeg k p1 p3].
    move=> /andP[k_gt0 k_lt].
    have kL3a1 : k <= (3 * a.-1).
      by rewrite -ltnS (leq_trans k_lt) // -{1}[a]prednK // mulnS.
    have kLa1 : k %/ 3 <= a.-1.
      by rewrite -(mulKn a.-1 (isT : 0 < 3)) leq_div2r.
    rewrite ffunE; case: eqP => [kH|/eqP kH].
      rewrite kH; rewrite /apeg odd_mul /=.
      have := @H (inord a.-1); rewrite inordK //.
        rewrite ffunE; apply.
        by rewrite -ltnS prednK // a_gt1.
      by rewrite prednK // (leq_trans aLld1).
    have k3La2 : k %/ 3 <= a.-2.
      rewrite -ltnS [a.-2.+1]prednK //; last first.
        by rewrite -subn1 ltn_subRL.
      rewrite ltn_divLR // [_ * 3]mulnC.
      by move: kL3a1 kH; case: ltngtP.
    rewrite eqn_leq [_ <= k]leqNgt (leq_trans k_lt) ?andbF //; last first.
      by rewrite -{1}[a]prednK // mulnS addSn add2n.
    have k3La : k %/ 3 <= a.
      by rewrite (leq_trans kLa1) // -subn1 leq_subr.
    case: eqP => k3mH.
      apply: codom_liftr.
      rewrite {2}(divn_eq k 3) k3mH addn0 /apeg odd_mul andbT.
      have := @cH (inord (k %/3)); rewrite inordK; last first.
        by rewrite (leq_ltn_trans k3La).
      apply.
      rewrite (leq_ltn_trans k3La) ?ltnS //.
      move: k_gt0; rewrite andbT {1}(divn_eq k 3) k3mH addn0 muln_gt0.
      by case/andP.
    case: eqP => k3mH1.
      rewrite /si; case: (F) => [] [s t] /= [H1 _ _]; move: H1.
      set pp := u _ _; (suff <- : pp = apeg k p1 p3 by []); rewrite {}/pp.
      set i := inord _; have <- : apeg i p1 p3 = apeg k p1 p3.
        rewrite (divn_eq k 3) k3mH1 addn1 /apeg /= odd_mul andbT.
        by rewrite /i !inordK //= !ltnS (leq_trans k3La).
      have H2 : (k %/ 3).+1 < l.+2 by rewrite !ltnS (leq_trans k3La).
      rewrite -(@aMin1 i); last first.
        rewrite !inordK // -{2}[a]prednK // ltnS // -[a.-1]prednK // .
        by rewrite -subn1 subn_gt0.
      congr (u _ _).
      by apply/val_eqP; rewrite /= !inordK.
    suff : codom (ti (inord (k %/ 3))) \subset [:: apeg k p1 p3; p2].
      move=> /subsetP H2; apply/subsetP => i /H2.
      by rewrite !inE orbC.
    rewrite /ti; case: (F) => [] [s t] /= [_ H1 _]; move: H1.
    set pp := u _ _; (suff <- : pp = apeg k p1 p3 by []); rewrite {}/pp.
    set i := inord _; have <- : apeg i p1 p3 = apeg k p1 p3.
      have k3mH2 : k %% 3 = 2.
        have := ltn_mod k 3; move: k3mH k3mH1.
        by case: modn => // [] [|[]].
      rewrite (divn_eq k 3) k3mH2 addn2 /apeg /= odd_mul andbT negbK.
        by rewrite /i !inordK //= !ltnS (leq_trans k3La).
      have H2 : (k %/ 3) < l.+2 by rewrite !ltnS (leq_trans k3La).
      rewrite -(@aMin1 i); last by rewrite !inordK // -{2}[a]prednK .
      congr (u _ _).
      by apply/val_eqP; rewrite /= !inordK.
  have {cH2}P2 := IH (nLm : n < m) p1Dp2 p1Dp3 p2Dp3 p1Dp0 p2Dp0 p3Dp0 cH2.
  rewrite [X in _ <= _ + X]sum_beta_S /= in P2; last first.
    rewrite -subn2 leq_subRL.
      by rewrite (leq_trans (_ : 4 <= 3 * 2)) // leq_mul2l.
    by rewrite (leq_trans (_ : 2 <= 3 * 2)) // leq_mul2l.
  rewrite u10E uiME in P2.
  have {}P2 := leq_trans P2 (leq_add (leq_add (leqnn _) (leq_sum_beta _ _))
                          (leqnn _)).
  have cH3 (k : 'I_3) :  
    0 < k < 2 -> codom (u2 k) \subset 
                  [:: apeg a.+1 p1 p3; apeg k p2 (apeg a p1 p3)].
    case: k => [] [|[|]] //= iH _.
    rewrite ffunE /= /apeg /=.
    have := tam1E.
    rewrite aMin1; first by rewrite /apeg -subn1 odd_sub //= addbT.
    by rewrite -{2}[a]prednK.
  rewrite -/x1P1 in P2.
  have {cH3}P3 : 
    (S_[2] n.+1).*2 <=
     \sum_(i < 2)  d[u2 (inord i), u2 (inord i.+1)] +
     \sum_(k < n.+1) (u2 ord0 k != apeg 0 p2 (apeg a p1 p3)) *
                         beta n.+1 2 k +
     \sum_(k < n.+1)
        (u2 ord_max k != apeg 2 p2 (apeg a p1 p3)) * beta n.+1 2 k.
    apply: IH cH3 => //.
    - by rewrite /apeg; case: odd; rewrite // eq_sym.
    - by rewrite /apeg; case: odd; rewrite // eq_sym.
    - by rewrite /apeg /=; case: odd; rewrite //= eq_sym.
    - by rewrite /apeg; case: odd; rewrite // eq_sym.
    by rewrite /apeg; case: odd; rewrite // eq_sym. 
  rewrite !sum_beta_S // /apeg /= !ffunE /= in P3.
  rewrite -/x2P1 in P3.
  have cH4 (k : 'I_b.+1) :
      0 < k < b -> codom (u3 k) \subset 
                  [:: p2; apeg k (apeg a p1 p3) (apeg (b + l) p1 p3)].
    move=> /andP[k_gt0 kLb].
    have kBound : 0 < k + a < l.+1.
      rewrite (leq_trans a_gt0) ?leq_addl //=.
      by move: kLb; rewrite /b ltn_subRL addnC.
    rewrite ffunE codom_liftr //.
    have := @cH (inord (k + a)).
    rewrite /apeg /= inordK //.
      rewrite /b !odd_add // odd_sub //=.
      by do 3 case: odd => //=; apply.
    by rewrite ltnW // ltnS; case/andP: kBound.
  have {cH4}P4 : 
   (S_[b] n.+1).*2 <=
     \sum_(i5 < b)  d[u3 (inord i5), u3 (inord i5.+1)] +
     \sum_(k < n.+1)
        (u3 ord0 k != apeg 0 (apeg a p1 p3) (apeg (b + l) p1 p3)) *
        beta n.+1 b k +
     \sum_(k < n.+1)
        (u3 ord_max k != apeg b (apeg a p1 p3) (apeg (b + l) p1 p3)) *
        beta n.+1 b k.
    apply: IH cH4 => //.
    - by rewrite /apeg; case: odd; rewrite // eq_sym.
    - rewrite /apeg /b odd_add odd_sub //=.
      by do 2 case: odd; rewrite // eq_sym.
    - by rewrite /apeg /=; case: odd; rewrite //= eq_sym.
    - by rewrite /apeg; case: odd; rewrite // eq_sym.
    by rewrite /apeg; case: odd; rewrite // eq_sym.
  have {}P4 := leq_trans P4 (leq_add (leqnn _) (leq_sum_beta _ _)).
  rewrite {1}/apeg /= (_ : apeg b _ _ = apeg l.+1 p1 p3)  in P4; last first.
    rewrite /apeg /b odd_add odd_sub //=.
    by do 2 case: odd; rewrite // eq_sym.
  rewrite [X in _ <= _ + X + _]sum_beta_S // !ffunE /= add0n -/ai in P4.
  rewrite -/x3P1 in P4.
  rewrite [X in _ <= _ + X + _]sum_beta_S //=.
  set xS := \sum_(i < n.+1) _ in P2.
  rewrite [X in _ <= _ + (X + _) + _](_ : _ =  xS); last first.
    apply: eq_bigr => i _; congr ((_ != _) * _).
    rewrite !ffunE; congr (u _ _).
    by apply/val_eqP; rewrite /=.
  rewrite [X in _ <= _ + _ + X]sum_beta_S //= KH2 mul1n.
  set yS := \sum_(i < n.+1) _ in P4.
  rewrite [X in _ <= _ + _ + (X + _)](_ : _ = yS); last first. 
    apply: eq_bigr => i _; congr ((_ != _) * _).
    rewrite !ffunE; congr (u _ _).
      by apply/val_eqP; rewrite /= /b subnK // inordK.
    by apply/val_eqP.
  set x1S := \sum_(i < n) _ in P2.
  set y1S := \sum_(i < n) _ in P3.
  have x1Sy1SE : x1S + y1S = (S1 n).*2.
    rewrite -addnn -!big_split /=; apply: eq_bigr => i _.
    set v := widen_ord _ _.
    have /subsetP := sam1C => /(_ (sam1 v) (codom_f _ _)).
    rewrite !inE -uiME uaiLEp2 addnn.
    have -> : apeg a p1 p3 = apeg (3 * a).-2 p1 p3.
      rewrite /apeg -subn2 odd_sub //.
        by rewrite odd_mul /=; case: odd.
      by rewrite (leq_trans (_ : 2 <= 3 * 1)) // leq_mul2l.
    case: eqP => /= v1; case: eqP => /= v2; rewrite ?(mul1n, add0n, addn0) //.
    move/eqP: v2; rewrite v1 /apeg; case: odd.
      by rewrite eq_sym (negPf p2Dp3).
    by rewrite (negPf p1Dp2). 
  set x2S := \sum_(i < n) _ in P3.
  set y2S := \sum_(i < n) _ in P4.
  have xSy2SE : x2S + y2S = (S1 n).*2.
    rewrite -addnn -!big_split /=; apply: eq_bigr => i _.
    rewrite /ai.
    set v := cunliftr _ _.
    have /H : 0 < (inord a : 'I_l.+2) < l.+1 by rewrite inordK // a_gt0.
    rewrite ffunE => /subsetP /(_ v (codom_f _ _)).
    rewrite !inE addnn inordK //.
    case: eqP => /= v1; case: eqP => /= v2; rewrite ?(mul1n, add0n, addn0) //.
    move/eqP: v2; rewrite v1 /apeg; case: odd.
      by rewrite (negPf p2Dp3).
    by rewrite eq_sym (negPf p1Dp2). 
  rewrite KH1 eqxx mul0n addn0.
  set v1 := (_ != _) * _ in P2.
  set v2 := (_ != _) * _ in P3.
  set v3 := (_ != _) * _ in P3.
  set v4 := (_ != _) * _ in P4.
  have v1v2 : v1 + v2 <= α_[(3 * a).-2] n.
    rewrite /v1 /v2.
    have /subsetP := sam1C => /(_ (sam1 ord_max) (codom_f _ _)).
    rewrite !inE uaiLEp2.
    have -> : apeg a p1 p3 = apeg (3 * a).-2 p1 p3.
      rewrite /apeg -subn2 odd_sub //.
        by rewrite odd_mul /=; case: odd.
      by rewrite (leq_trans (_ : 2 <= 3 * 1)) // leq_mul2l.
    case: eqP => /= x1; case: eqP => /= x2 // _; rewrite ?(mul1n, add0n, addn0) //.
    apply: (increasingE (increasing_alphaL_l _)).
    by rewrite -subn2 ltn_subRL (ltn_mul2l 3 1 a).
  have v3v4 : v3 + v4 <= α_[b] n.
    rewrite /v3 /v4.
    have /H : 0 < (inord a : 'I_l.+2) < l.+1 by rewrite inordK // a_gt0.
    rewrite ffunE => /subsetP /(_ (cunliftr (u ai) ord_max) (codom_f _ _)).
    rewrite ffunE !inE inordK //.
    case: eqP => /= x1; case: eqP => /= x2 // _; rewrite ?(mul1n, add0n, addn0) //.
    by apply: (increasingE (increasing_alphaL_l _)).
  rewrite -addnn {1}dsum_alphaL_S in P2.
  rewrite -addnn {1}dsum_alphaL_S in P3.
  rewrite -addnn {1}dsum_alphaL_S.
Admitted.

End Case1.

Lemma main p1 p2 p3 n l (u : {ffun 'I_l.+1 -> configuration 4 n}) :
   p1 != p2 -> p1 != p3 -> p2 != p3 -> 
   p1 != p0 -> p2 != p0 -> p3 != p0 ->
  (forall k : 'I_l.+1, 0 < k < l -> 
                       codom (u k) \subset [:: p2; apeg k p1 p3]) ->
  (S_[l] n).*2 <=  \sum_(i < l) d[u (inord i), u (inord i.+1)] + 
                    \sum_(k < n) (u ord0 k != apeg 0 p1 p3) * beta n l k +  
                    \sum_(k < n) (u ord_max k != apeg l p1 p3) * beta n l k.
Proof.
elim: {n}_.+1 {-2}n (leqnSn n) l p1 p2 p3 u => [[]// _ l p1 p2 p3 u|
                                                m IH [|[|n]] nLm l p1 p2 p3 u]
  p1Dp2 p1Dp3 p2Dp3 p1Dp0 p2Dp0 p3Dp0 cH.
- by rewrite /dsum_alphaL /conv /= dsum_alpha_0 muln0.
- by rewrite /dsum_alphaL /conv /= dsum_alpha_0 muln0.
- rewrite /dsum_alphaL /conv /= dsum_alpha_1 dsum_alpha_0 
          muln0 addn0 add0n muln1.
  rewrite [X in _ <= _ + X + _]big_ord_recl big_ord0  /= addn0.
  rewrite [X in _ <= _ + X]big_ord_recl big_ord0  /= addn0.
  have d0fE (c1 c2 : configuration 4 1) : 
    c1 != `c[p0] -> c2 != `c[p0] -> d[c1, c2] = (c1 != c2).*2.
    move=> c1Dp0 c2Dp0.
    case: (gpath_connect (shanoi_connect c1 c2)) 
              => [] [/gpath_dist H |a [|b p]].
    - by rewrite H; move/eqP: H; rewrite gdist_eq0 => ->.
    - case/gpathP; rewrite /= andbT => /moveP[z].
      rewrite [z]disk1_all => [] [zH _ _ _] aE.
      case/andP: zH => _; rewrite aE.
      move: c1Dp0 c2Dp0; rewrite !configuration1_eq !Ival_eq /= !ffunE /=.
      by do 2 case: val.
    move=> /gpath_dist; case: eqP => [<-|/eqP c1Dc2]; first by rewrite gdist0.
    move=> H; apply/eqP; rewrite eqn_leq {2}H /= andbT.
    have pH : path smove c1 [::`c[p0]; c2].
      rewrite /=; apply/and3P; split => //.
        apply/moveP; exists ord0; split => //=.
        - rewrite !ffunE; apply/andP; split; last by rewrite muln0.
          by move: c1Dp0; rewrite configuration1_eq ffunE.
        - by move=> i; rewrite [i]disk1_all.
        - by apply/on_topP => j; rewrite [j]disk1_all.
        by apply/on_topP => j; rewrite [j]disk1_all.
      apply/moveP; exists ord0; split => //=.
      - rewrite !ffunE; apply/andP; split=> //.
        by move: c2Dp0; rewrite configuration1_eq ffunE eq_sym.
      - by move=> i; rewrite [i]disk1_all.
      - by apply/on_topP => j; rewrite [j]disk1_all.
      by apply/on_topP => j; rewrite [j]disk1_all.
    rewrite -[1.*2]/(size [:: `c[p0]; c2]).
    by apply: gdist_path_le pH _.
  case: l u cH => [|l] u cH; first by rewrite (minn_idPr _).
  case: l u cH => [|l] u cH.
    rewrite (minn_idPr _) //.
    rewrite big_ord_recl big_ord0 addn0.
    rewrite (_ : inord 0 = ord0); last by apply/val_eqP; rewrite /= inordK.
    rewrite (_ : inord 1 = ord_max); last by apply/val_eqP; rewrite /= inordK.
    rewrite /beta /apeg /= -[a 0]/1; do 2 case: eqP; rewrite /= ?addn0;
        try by move=> *; rewrite leq_addl.
    move=> u1E u0E.
    rewrite d0fE //.
    - by rewrite configuration1_eq u1E u0E p1Dp3.
    - by rewrite configuration1_eq ffunE u0E.
    by rewrite configuration1_eq ffunE u1E.
  rewrite (minn_idPl _) // -[_.*2]/4.
  rewrite big_ord_recl big_ord_recr /=.
  rewrite -!addnA addnC -!addnA (leq_trans _ (leq_addl _ _)) //.
  rewrite {1}/apeg /= /beta /= alphaL_0 (minn_idPl _) /bump /= ?add1n //.
  rewrite addnCA addnC !addnA -addnA -[4]/(2 + 2).
  apply: leq_add.
    case: eqP => /= [umE|umD]; last by rewrite leq_addl.
    rewrite addn0 d0fE.
    - case: eqP => // H.
      have /cH :  0 < (inord l.+1 : 'I_l.+3) < l.+2 by rewrite inordK /=.
      move=> /subsetP/(_ _ (codom_f _ d0)).
      rewrite H (_ : inord l.+2 = ord_max).
        rewrite umE inordK // /apeg /=; case: odd => /=.
          by rewrite !inE eq_sym (negPf p2Dp3) eq_sym (negPf p1Dp3).
        by rewrite !inE (negPf p1Dp2) (negPf p1Dp3).
      by apply/val_eqP; rewrite /= inordK.
    - rewrite configuration1_eq ffunE.
      case: (_ =P _) => // H.
      have /cH :  0 < (inord l.+1 : 'I_l.+3) < l.+2 by rewrite inordK /=.
      move=> /subsetP/(_ _ (codom_f _ d0)).
      rewrite H !inE eq_sym (negPf p2Dp0) /apeg /=; case: odd => /=.
        by rewrite eq_sym (negPf p3Dp0).
      by rewrite eq_sym (negPf p1Dp0).
    rewrite configuration1_eq ffunE.
    rewrite (_ : inord l.+2 = ord_max).
      by rewrite umE /apeg /=; case: odd.
    by apply/val_eqP; rewrite /= inordK.
  case: eqP => /= [u0E|u0D]; last by rewrite leq_addl.
  rewrite addn0 d0fE.
  - case: eqP => // H.
    have /cH :  0 < (inord 1 : 'I_l.+3) < l.+2 by rewrite inordK /=.
    move=> /subsetP/(_ _ (codom_f _ d0)).
    rewrite -H (_ : inord 0 = ord0).
      rewrite u0E /apeg /= inordK //=.
      by rewrite !inE (negPf p1Dp2) (negPf p1Dp3).
    by apply/val_eqP; rewrite /= inordK.
  - rewrite configuration1_eq ffunE (_ : inord 0 = ord0) ?u0E //.
    by apply/val_eqP; rewrite /= inordK.
  rewrite configuration1_eq ffunE.
  case: eqP => // H.
  have /cH :  0 < (inord 1 : 'I_l.+3) < l.+2 by rewrite inordK /=.
  move=> /subsetP/(_ _ (codom_f _ d0)).
  rewrite H !inE eq_sym (negPf p2Dp0) /apeg /=; case: odd => /=.
    by rewrite eq_sym (negPf p3Dp0).
  by rewrite eq_sym (negPf p1Dp0).
case: l u cH => [|l] u cH; first by rewrite S0E.
pose u' : {ffun 'I_l.+2 -> configuration 4 n.+1} :=
     [ffun i : 'I_l.+2 => cunliftr (u i)].
have H (k : 'I_l.+2) : 
  0 < k < l.+1 -> codom (u' k) \subset [:: p2; apeg k p1 p3].
  by move=> k1; rewrite ffunE; apply/codom_liftr/cH. 
pose K := (u ord0 ord_max != apeg 0 p1 p3) + 
          (u ord_max ord_max != apeg l.+1 p1 p3).
have [HK|] := boolP ((K == 2) || ((K == 1) && (l == 0))).
  rewrite dsum_alphaL_S doubleD.
  have IH' := IH _ (nLm : n.+1 <= m) _ p1 p2 p3 u'
              p1Dp2 p1Dp3 p2Dp3 p1Dp0 p2Dp0 p3Dp0 H.
  rewrite ![\sum_(_ < _.+2) _]big_ord_recr /=.
  set u1 := \sum_ (_ < _) _; set u2 := \sum_ (_ < _) _; set u3 := \sum_ (_ < _) _.
  rewrite -!addnA [_ + (u3 + _)]addnCA 2!addnA.
  apply: leq_add.
    apply: leq_trans IH' _.
    apply: leq_add; last first.
      apply: leq_sum => i _.
      apply: leq_mul.
        rewrite leq_eqVlt; apply/orP; left; apply/eqP.
        by rewrite !ffunE; congr (u _ _ != _); apply/val_eqP.
      rewrite {2}/beta eqn_leq [_ <= i]leqNgt ltn_ord !andbF /=.
    apply: geq_beta.
    apply: leq_add; last first.
      apply: leq_sum => i _.
      apply: leq_mul.
        rewrite leq_eqVlt; apply/orP; left; apply/eqP.
        by rewrite !ffunE; congr (u _ _ != _); apply/val_eqP.
      rewrite {2}/beta eqn_leq [_ <= i]leqNgt ltn_ord !andbF /=.
      apply: geq_beta.
    apply: leq_sum => i _.
    rewrite !ffunE.
    by apply/gdist_cunlift/shanoi_connect.
  rewrite -mulnDl -/K.
  case/orP: HK => [/eqP->|/andP[/eqP-> /eqP->]].
    by rewrite mul2n leq_double leq_beta.
  by rewrite mul1n /beta /= /alphaL /delta !S1E -delta_S1.
rewrite negb_or negb_and.
have: K <= 2 by rewrite /K; do 2 case: (_ != _).
case: ltngtP; rewrite // ltnS.
case: ltngtP => //= KE _ _ l_gt0; last first.
  have {}l_gt0 : 0 < l by case: l l_gt0.
  move: KE; rewrite /K.
  (case: eqP => [KH1|/eqP KH1] /=; case: eqP) => // [/eqP KH2|KH2] _.
    by apply: (@case1 _ IH) cH KH1 KH2 l_gt0.
  pose u1 : {ffun 'I_l.+2 -> configuration 4 n.+2} := 
     [ffun i : 'I_l.+2 => u (inord (l.+1 - i))].
  have -> : \sum_(i < l.+1)  d[u (inord i), u (inord i.+1)] =
            \sum_(i < l.+1)  d[u1 (inord i), u1 (inord i.+1)].
    have F : injective (fun i : 'I_l.+1 => (inord (l - i) : 'I_l.+1)).
      move=> i j /val_eqP.
        have lBiLl (i1 : 'I_l.+1) : l - i1 < l.+1 by rewrite ltn_subLR ?leq_addl // -ltnS.
      rewrite /= !inordK // => /eqP liE; apply/val_eqP => /=.
      rewrite -(subKn (_ : i <= l)); last by rewrite -ltnS.
      by rewrite liE subKn // -ltnS.
    rewrite (reindex_inj F) /=.
    apply: eq_bigr => i _; rewrite !ffunE.
    have iLl2 : i < l.+2 by apply: leq_trans (ltn_ord _) _.
    have lBiLl : l - i < l.+1 by rewrite ltn_subLR ?leq_addl // -ltnS.
    have iLl : i <= l by rewrite -ltnS.
    rewrite gdistC //; congr (d[u _,u _]).
      by apply/val_eqP; rewrite /= !inordK ?subSn.
    by apply/val_eqP; rewrite /= !inordK // ?subSS ltnS // ltnW.
  pose p1' := if odd l.+1 then p3 else p1.
  pose p3' := if odd l.+1 then p1 else p3. 
  have -> : \sum_(k < n.+2) (u ord0 k != apeg 0 p1 p3) * beta n.+2 l.+1 k =
            \sum_(k < n.+2) (u1 ord_max k != apeg l.+1 p1' p3') * 
                            beta n.+2 l.+1 k.
    apply: eq_bigr => i _; congr (_ * _).
    rewrite ffunE subnn.
    have -> : inord 0 = ord0 :> 'I_l.+2 by apply/val_eqP; rewrite /= inordK.
    by rewrite /apeg /p3' /p1' /=; case: odd.
  have -> : \sum_(k < n.+2) (u ord_max k != apeg l.+1 p1 p3) * beta n.+2 l.+1 k =
            \sum_(k < n.+2) (u1 ord0 k != apeg 0 p1' p3') * beta n.+2 l.+1 k.
    apply: eq_bigr => i _; congr (_ * _).
    rewrite ffunE subn0.
    suff -> : inord l.+1 = ord_max :> 'I_l.+2 by []. 
    by apply/val_eqP; rewrite /= inordK.
  have cH1 (k : 'I_l.+2) : 
     0 < k < l.+1 -> codom (u1 k) \subset [:: p2; apeg k p1' p3'].
    move=> /andP[kH1 kH2]; rewrite ffunE.
    have F1 : k <= l.+1 by apply: ltnW.
    have F2 : l.+1 - k < l.+2.
      by rewrite ltn_subLR // addnS ltnS leq_addl.
    have -> :  apeg k p1' p3' = apeg (inord (l.+1 - k) : 'I_l.+2) p1 p3.
      rewrite /apeg /p1' /p3' inordK // odd_sub; last by apply: ltnW.
      by case: odd; case: odd.
    apply: cH; rewrite inordK // subn_gt0 // ltn_subLR // kH2 //=.
    by rewrite addnS ltnS -{1}[l.+1]add1n leq_add2r.
  rewrite -addnA [X in _ <= _ + X]addnC addnA.
  apply: (@case1 _ IH) cH1 _  _ _ => //.
  - by rewrite /p3' /p1'; case: odd => //; rewrite eq_sym.
  - by rewrite /p3' /p1'; case: odd => //; rewrite eq_sym.
  - by rewrite /p3' /p1'; case: odd => //; rewrite eq_sym.
  - by rewrite /p3' /p1'; case: odd => //; rewrite eq_sym.
  - by rewrite /p3' /p1'; case: odd => //; rewrite eq_sym.
  - rewrite ffunE subn0.
    have:= KH2; rewrite /apeg /p3' /p1' /=.
    suff -> : inord l.+1 = ord_max :> 'I_l.+2 by [].
    by apply/val_eqP; rewrite /= inordK.
  rewrite ffunE subnn.
  have:= KH1; rewrite /apeg /p3' /p1' /=.
  have -> : inord 0 = ord0 :> 'I_l.+2 
    by apply/val_eqP; rewrite /= inordK.
  by case: odd.
Admitted.    

End sHanoi4.


