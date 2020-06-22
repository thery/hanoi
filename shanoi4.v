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

Lemma concaveEk1 (f : nat -> nat) (i k1 k2 : nat) :
  concave f -> f (i + k1 + k2) + f i <= f (i + k2) + f (i + k1).
Proof.
move=> fC; have [fI dfD] := fC.
elim: k2 k1 i => [k1 i|k2 IHH k1 i]; first by rewrite !addn0 addnC.
rewrite !addnS -(subnK (fI _)) -[X in _ <= X + _](subnK (fI _)).
rewrite -addnA -[X in _ <= X]addnA leq_add //.
by apply: (decreasingE dfD); rewrite addnAC leq_addr.
Qed.

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

Lemma alphaL_3E n : α_[3] n = α_[1] n.+1.
Proof.
by rewrite /alphaL /delta -subSS -!dsum_alpha3_S.
Qed.

Lemma alphaL1E k : α_[1] k = α k.
Proof. by rewrite /alphaL /delta !S1E -delta_S1. Qed.

Lemma alphaL_1_2 n : α_[1] (n.+1) <= (α_[1] n).*2.
Proof. 
rewrite !alphaL1E.
case: n => // [] [|[|[|]]] // k.
rewrite -(leq_pmul2l (_ : 0 < 3)) //.
apply: leq_trans (alpha_4_3 _) _ => //.
by rewrite -mul2n mulnA leq_mul2r orbT.
Qed.

Lemma alphaL_4_5 n : α_[1] (n.+2) <= (α_[1] n).*2.+1.
Proof. 
rewrite !alphaL1E.
case: n => // [] [|[|[|]]] // k.
apply: leq_trans (leqnSn _).
rewrite -(leq_pmul2l (_ : 0 < 3)) //.
apply: leq_trans (alpha_4_3 _) _ => //.
rewrite -(leq_pmul2l (_ : 0 < 3)) //.
rewrite mulnCA (leq_trans (_ : _ <= 4 * (4 *  α k.+4))) //.
  by rewrite leq_mul2l /= alpha_4_3.
by rewrite -mul2n !mulnA leq_mul2r orbT.
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

Lemma apeg32E a p1 p2 :apeg (3 * a).-2 p1 p2 = apeg a p1 p2.
Proof.
case: a => // a.
rewrite /apeg -subn2 odd_sub; last by rewrite mulnS.
by rewrite odd_mul /=; case: odd.
Qed.

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
apply/connectP; exists (rm_rep (↓[c1]) ([seq ↓[i] | i <- p])) => //.
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
Lemma sgdist_pair n (p2 : peg 4) (u v : configuration 4 n.+1) 
    (p1 := u ldisk) (p3 := v ldisk): 
   {st : (configuration 4 n * configuration 4 n) |
    p1 != p2 -> p1 != p3 -> p2 != p3 -> 
    p1 != p0 -> p2 != p0 -> p3 != p0 ->
     [/\ codom st.1 \subset [:: p2; p3], codom st.2 \subset [:: p1; p2] & 
         d[u, v] = D[[:: ↓[u]; st.1; st.2; ↓[v]]].+2]}.
Proof.
case: eqP => [_|/eqP p1Dp2]; first by exists (↓[u], ↓[v]).
case: eqP => [_|/eqP p1Dp3]; first by exists (↓[u], ↓[v]).
case: eqP => [_|/eqP p2Dp3]; first by exists (↓[u], ↓[v]).
case: eqP => [_|/eqP p1Dp0]; first by exists (↓[u], ↓[v]).
case: eqP => [_|/eqP p2Dp0]; first by exists (↓[u], ↓[v]).
case: eqP => [_|/eqP p3Dp0]; first by exists (↓[u], ↓[v]).
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
have sCd : codom (↓[s]) \subset [:: p2; p3].
  apply/subsetP=> i; rewrite !inE => /codomP[j] ->.
  case: (pE (↓[s] j)) => [||->|->]; rewrite ?eqxx ?orbT //.
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
have tCd : codom (↓[t]) \subset [:: p1; p2].
  apply/subsetP=> i; rewrite !inE => /codomP[j] ->.
  case: (pE (↓[t] j)) => [|->|->|]; rewrite ?eqxx ?orbT //.
    rewrite ffunE trshift_lift /=.
    move/eqP; rewrite -tLp0 -[_ == _]negbK; case/negP.
    apply: move_on_toplDl tMtp _ _; first by rewrite tpLp3 tLp0 eq_sym.
    by rewrite /= /bump [n <= j]leqNgt ltn_ord add0n.
  rewrite ffunE trshift_lift /=.
  move/eqP; rewrite -tpLp3 -[_ == _]negbK; case/negP.
  apply: move_on_toplDr tMtp _ _; first by rewrite tpLp3 tLp0 eq_sym.
  by rewrite /= /bump [n <= j]leqNgt ltn_ord add0n ltnW.
exists (↓[s], ↓[t]); split => //=.
rewrite addn0.
move: csH; rewrite csE => csH.
rewrite (gdist_cat csH) -[@move _ _ _]/smove -/s.
move: csH => /gpath_catr; rewrite -/s => csH.
rewrite gdist_cunlift_eq //; last by apply: shanoi_connect.
rewrite -!addnS.
congr (_ + _).
have ->: ↓[s] = ↓[sp].
  have sLDspL : s ldisk != sp ldisk by rewrite sLp1 spLp0.
  apply/ffunP => i; rewrite !ffunE.
  apply: move_disk1 sMsp sLDspL _.
  by apply/negP => /eqP/val_eqP /=; rewrite eqn_leq leqNgt ltn_ord.
rewrite (gdist_cons csH) addnS; congr (_).+1.
move: csH => /gpath_consr csH.
have ctEctp : ↓[t] = ↓[tp].
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

Definition sgdist1 n (p2 : peg 4) (u v : configuration 4 n.+1) :=
 let: (exist (x, _) _) := sgdist_pair p2 u v in x.

Definition sgdist2 n (p2 : peg 4) (u v : configuration 4 n.+1) :=
 let: (exist (_, x) _) := sgdist_pair p2 u v in x.

Lemma sgdistE n (p2 : peg 4) (u v : configuration 4 n.+1) 
    (p1 := u ldisk) (p3 := v ldisk): 
    p1 != p2 -> p1 != p3 -> p2 != p3 -> 
    p1 != p0 -> p2 != p0 -> p3 != p0 -> 
   [/\ codom (sgdist1 p2 u v) \subset [:: p2; p3], 
       codom (sgdist2 p2 u v) \subset [:: p1; p2] & 
       d[u, v] = D[[:: ↓[u]; sgdist1 p2 u v; sgdist2 p2 u v; ↓[v]]].+2].
Proof.
move=> p1Dp2 p1Dp3 p2Dp3 p1Dp0 p2Dp0 p3Dp0.
by rewrite /sgdist1 /sgdist2; case: sgdist_pair  => [] [x y] [].
Qed.

Definition beta n l k := 
  if ((1 < l) && (k == n.-1)) then α_[l] k else (α_[1] k).*2.

Lemma leq_beta n l k : α_[l] k <= beta n l k.
Proof.
rewrite /beta; case: (_ < _) => /=; last first.
  by rewrite alphaL1E; apply: bound_alphaL.
by case: (_ == _) => //=; rewrite alphaL1E; apply: bound_alphaL.
Qed.

Lemma geq_beta n l k : beta n l k <= (α_[1] k).*2.
Proof.
rewrite /beta; case: (_ < _) => //=.
by case: (_ == _) => //=; rewrite alphaL1E; apply: bound_alphaL.
Qed.

Lemma alphaL_diffE m n (f : configuration 4 n.+1) (p1 p2 : peg 4) i v1 v2 :
  p1 != p2 -> codom f \subset [:: p1; p2] ->
 (f i != p1) * α_[v1] m + (f i != p2) * α_[v2] m <= α_[maxn v1 v2] m.
Proof.
move=> p1Dp2 cH.      
have /subsetP/(_ (f i) (codom_f _ _)) := cH.
rewrite !inE.
case: eqP => /= x1; case: eqP => /= x2 // _; rewrite ?(mul1n, add0n, addn0) //;
     apply: (increasingE (increasing_alphaL_l _)).
  by apply: leq_maxr.
by apply: leq_maxl.
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

Lemma alphaL_0 l : α_[l] 0 = minn 2 l.
Proof.
rewrite /alphaL /delta /dsum_alphaL /conv /= dsum_alpha_1 dsum_alpha_0.
by rewrite muln0 addn0 add0n subn0 muln1.
Qed.


Lemma beta1E n k : beta n 1 k = (α_[1] k).*2.
Proof. by rewrite /beta ltnn. Qed.

Lemma sum_beta_S n l (a : configuration 4 n.+1) p : 1 < l ->
  \sum_(k < n.+1) (a k != p) * beta n.+1 l k =
  \sum_(k < n) ((↓[a] k  != p) * (α_[1] k).*2) + (a ord_max != p) * α_[l] n.
Proof.
move=> l_gt1.
rewrite big_ord_recr /= /beta l_gt1 eqxx /=; congr (_ + _).
apply: eq_bigr => i _; rewrite !ffunE; congr ((a _ != _) * _).
  by apply: val_inj.
by rewrite eqn_leq [_ <= i]leqNgt ltn_ord andbF.
Qed.

Lemma leq_sum_beta n l a : 
  \sum_(k < n) a k * beta n l k <= \sum_(k < n) a k * (α_[1] k).*2.
Proof.
by apply: leq_sum => i _; rewrite leq_mul2l geq_beta orbT.
Qed.

Lemma sum_alpha_diffE n (f : configuration 4 n.+1) (p1 p2 : peg 4) v1 v2 :
  1 < v1 -> 1 < v2 -> p1 != p2 -> codom f \subset [:: p1; p2] ->
  \sum_(i < n.+1) (f i != p1) * beta n.+1 v1 i +
  \sum_(i < n.+1) (f i != p2) * beta n.+1 v2 i <=
  (S_[1] n).*2 + α_[maxn v1 v2] n.
Proof.
move=> v1_gt1 v2_gt1 p1Dp2 cH.
rewrite !sum_beta_S //.
rewrite -addnA -addnCA addnC !addnA -addnA leq_add //.
  rewrite leq_eqVlt; apply/orP; left; apply/eqP.
  rewrite -addnn !dsum_alphaLE -!big_split /=; apply: eq_bigr => i _.
  rewrite !ffunE; set v := trshift _ _.
  have /subsetP := cH => /(_ (f v) (codom_f _ _)).
  rewrite !inE addnn.
  case: eqP => /= x1; case: eqP => /= x2; rewrite ?(mul1n, add0n, addn0) //.
  by move/eqP: x2; rewrite x1 (negPf p1Dp2).
  have /subsetP/(_ (f ord_max) (codom_f _ _)) := cH.
rewrite !inE.
case: eqP => /= x1; case: eqP => /= x2 // _; rewrite ?(mul1n, add0n, addn0) //;
     apply: (increasingE (increasing_alphaL_l _)).
  by apply: leq_maxr.
by apply: leq_maxl.
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

Let apeg13D2 a : apeg a p1 p3 != p2.
Proof. by rewrite /apeg; case: odd; rewrite // eq_sym. Qed.

Let apeg13D0 a : apeg a p1 p3 != p0.
Proof. by rewrite /apeg; case: odd; rewrite // eq_sym. Qed.

Hypothesis KH1 : u ord0 ord_max = p1.
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
have a_gt0 : 0 < a.
  by case: (a) aH; rewrite /apeg //= -KH1 inord_eq0 //= eqxx.
pose ai : 'I_l.+2 := inord a.
have aiE : ai = a :> nat by rewrite inordK.
pose b := l.+1 - a.
pose bi : 'I_l.+2 := inord b.
have biE : bi = b :> nat by rewrite inordK // /b ltn_subLR // leq_addl.
have l_ggt0 : 0 < l by case: l l_gt0.
have [/andP[a_gt1 aLlm1]|] := boolP (2 <= a <= l.-1).
  have aLl : a <= l by rewrite (leq_trans aLlm1) // -subn1 leq_subr.
  have b_gt1 : 1 < b by rewrite leq_subRL // addn2 ltnS -[l]prednK.
  have uaiLEp2 : u ai ldisk = p2.
    have /cH/subsetP/(_ (u ai ldisk) (codom_f _ _)) : 0 < ai < l.+1.
      by rewrite aiE (leq_trans _ a_gt1) //= ltnS (leq_trans aLl1)
                 // ssrnat.leq_pred.
    by rewrite !inE aiE (negPf aH) orbF => /eqP.
  pose si i : configuration 4 n.+1 := 
     sgdist1 p2 (u (inord i)) (u (inord i.+1)).
  pose ti i : configuration 4 n.+1 := 
     sgdist2 p2 (u (inord i)) (u (inord i.+1)).
  have sitiH i : i < a.-1 ->
     [/\ codom (si i) \subset [:: p2; u (inord i.+1) ldisk ], 
         codom (ti i) \subset [:: u (inord i) ldisk; p2] & 
         d[u (inord i), u (inord i.+1)] = 
           D[[:: ↓[u (inord i)]; si i; ti i; ↓[u (inord i.+1)]]].+2].
    move=> iLa.
    have iLa1 : i < a by rewrite (leq_trans iLa) // ssrnat.leq_pred.
    apply: sgdistE => //.
    - by rewrite aMin1.
    - rewrite !aMin1 //; last by rewrite -[a]prednK.
      by rewrite /apeg /=; case: odd; rewrite // eq_sym.
    - by rewrite aMin1 1?eq_sym // -[a]prednK.
    - by rewrite aMin1.
    by rewrite aMin1 // -[a]prednK.
  pose sam1 : configuration 4 n.+1 := 
     sgdist1 (apeg a p1 p3) (u (inord a.-1)) (u (inord a)).
  pose tam1 : configuration 4 n.+1 := 
     sgdist2 (apeg a p1 p3) (u (inord a.-1)) (u (inord a)).
  have [sam1C tam1C duam1ua1E] : 
     [/\ codom sam1 \subset [:: apeg a p1 p3; u (inord a) ldisk ], 
         codom tam1 \subset [:: u (inord a.-1) ldisk; apeg a p1 p3] & 
         d[u (inord a.-1), u (inord a)] = 
           D[[:: ↓[u (inord a.-1)]; sam1; tam1; ↓[u (inord a)]]].+2].
    apply: sgdistE => //.
    - rewrite aMin1 ?prednK // /apeg -{2}[a]prednK //=.
      by case: odd; rewrite // eq_sym.
    - by rewrite uaiLEp2 aMin1 ?prednK.
    - by rewrite uaiLEp2.
    - by rewrite aMin1 ?prednK.
    by rewrite uaiLEp2. 
  have {}tam1C : codom tam1 \subset [:: p1; p3].
    move: tam1C; rewrite aMin1; last by rewrite -{2}[a]prednK.
    rewrite -subn1 /apeg /= odd_sub; case: odd => //=.
    by apply: codom_subC.
  pose u1 := 
    [ffun i =>
    if ((i : 'I_(3 * a).-2.+1) == 3 * a.-1 :>nat) then ↓[u (inord a.-1)] 
    else if (i == (3 * a.-1).+1 :>nat) then sam1
    else if (i %% 3) == 0 then ↓[u (inord (i %/ 3))]
    else if (i %% 3) == 1 then si (i %/ 3)
    else ti (i %/ 3)].
  have u10E : u1 ord0 = ↓[u ord0].
    rewrite ffunE /= ifN ?inord_eq0 //.
    by rewrite neq_ltn muln_gt0 /= -ltnS prednK //= a_gt1.
  have uiME : u1 ord_max = sam1.
    rewrite ffunE /= eqn_leq leqNgt -{2}[a]prednK // mulnS.
    rewrite addSn add2n ltnS leqnn /=.
    by rewrite -{1}[a]prednK // mulnS eqxx.
  pose u2 :=  [ffun i  : 'I_3 =>  
    if i == 0 :> nat then sam1 else
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
        by rewrite mod3E eqxx mulKn.
      have -> : u1 (inord (3 * i).+1) = si i.
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
        by rewrite [_ <= i]leqNgt ltn_ord andbF mod3E /= div3E.
      have -> : u1 (inord (3 * i).+2) = ti i.
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
        by rewrite mod3E /= div3E.
      have -> : u1 (inord (3 * i).+3) = ↓[u (inord i.+1)].
        have -> : (3 * i).+3 = 3 * (i.+1) by rewrite mulnS addSn add2n.
        rewrite ffunE inordK; last first.
          rewrite ltnS (leq_trans (_ : _ <= 3 * (a.-1))) //.
            by rewrite leq_mul2l /=.
          by rewrite -{2}[a]prednK // mulnS addSn add2n /= ltnW.
        rewrite eqn_mul2l /=; case: eqP => [->//|_].
        rewrite eqn_leq [_ <= 3 * i.+1]leqNgt ltnS leq_mul2l /= ltn_ord andbF.
        by rewrite mod3E /= div3E.
      case: (sitiH i) => // _ _ ->.
      by rewrite add2n /= addnA addn0.
    - rewrite leq_eqVlt; apply/orP; left; apply/eqP.
      rewrite !big_ord_recr big_ord0 //= add0n !addnA.
      have -> : u2 (inord 0) = sam1 by rewrite ffunE /= inordK.
      have -> : u2 (inord 1) = tam1 by rewrite ffunE /= inordK.
      have -> : u2 (inord 2) = ↓[u ai] by rewrite ffunE /= inordK.
      by move: duam1ua1E; rewrite /= addn0 add2n !addnA !addSn.
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
      case: (sitiH ((k %/ 3))) => /=.
        by rewrite -[a.-1]prednK // -ltnS prednK.
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
    apply: codom_subC.
    case: (sitiH ((k %/ 3))) => /= [|_].
      by rewrite -[a.-1]prednK // -ltnS prednK.
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
  have a3B2_gt1 : 1 < (3 * a).-2.
    rewrite -subn2 leq_subRL.
      by rewrite (leq_trans (_ : 4 <= 3 * 2)) // leq_mul2l.
    by rewrite (leq_trans (_ : 2 <= 3 * 2)) // leq_mul2l.
  rewrite u10E uiME [apeg 0]/apeg /= in P2.
  have {}P2 := leq_trans P2 (leq_add (leq_add (leqnn _) (leq_sum_beta _ _))
                          (leqnn _)).
  pose pa := apeg a p1 p3; pose paS := apeg a.+1 p1 p3.
  have cH3 (k : 'I_3) : 
    0 < k < 2 -> codom (u2 k) \subset [:: paS; apeg k p2 pa].
    case: k => [] [|[|]] //= iH _.
    rewrite ffunE /pa /paS /apeg /=; case: odd => //=.
    by apply: codom_subC.
  rewrite -/x1P1 in P2.
  have {cH3}P3 : 
    (S_[2] n.+1).*2 <=
     \sum_(i < 2)  d[u2 (inord i), u2 (inord i.+1)] +
     \sum_(k < n.+1) (u2 ord0 k != apeg 0 p2 pa) * beta n.+1 2 k +
     \sum_(k < n.+1) (u2 ord_max k != apeg 2 p2 pa) * beta n.+1 2 k.
    apply: IH cH3 => //; try by rewrite /pa /paS // eq_sym.
    by rewrite /pa /paS /apeg /=; case: odd; rewrite // eq_sym. 
  rewrite /apeg /= !ffunE /= in P3.
  rewrite -/x2P1 in P3.
  have cH4 (k : 'I_b.+1) :
      0 < k < b -> codom (u3 k) \subset [:: p2; apeg k pa paS].
      rewrite /b .
    move=> /andP[k_gt0 kLb].
    have kBound : 0 < k + a < l.+1.
      rewrite (leq_trans a_gt0) ?leq_addl //=.
      by move: kLb; rewrite /b ltn_subRL addnC.
    rewrite ffunE codom_liftr //.
    have := @cH (inord (k + a)).
    rewrite /pa /paS /apeg /= inordK //.
      by rewrite !odd_add; do 2 case: odd => //=; apply.
    by rewrite ltnW // ltnS; case/andP: kBound.
  have {cH4}P4 : 
   (S_[b] n.+1).*2 <=
     \sum_(i5 < b)  d[u3 (inord i5), u3 (inord i5.+1)] +
     \sum_(k < n.+1) (u3 ord0 k != apeg 0 pa paS) * beta n.+1 b k +
     \sum_(k < n.+1) (u3 ord_max k != apeg b pa paS) * beta n.+1 b k.
    apply: IH cH4 => //; try by rewrite /pa /paS // eq_sym.
    rewrite /pa /paS /apeg //=.
    by case: odd; rewrite // eq_sym.
  have {}P4 := leq_trans P4 (leq_add (leqnn _) (leq_sum_beta _ _)).
  rewrite [apeg 0]/apeg /= (_ : apeg b _ _ = apeg l.+1 p1 p3) in P4; last first.
    rewrite /pa /paS /apeg /b odd_sub //=.
    by do 2 case: odd; rewrite // eq_sym.
  rewrite !ffunE /= add0n -/ai in P4.
  rewrite -/x3P1 subnK // (_ : inord l.+1 = ord_max) in P4; last first.
    by apply/val_eqP; rewrite /= inordK.
  rewrite [X in _ <= _ + X + _]sum_beta_S //= KH1 eqxx addn0.
  set xS := \sum_(i < n.+1) _ in P2; rewrite -/xS.
  rewrite [X in _ <= _ + _ + X]sum_beta_S //= KH2 mul1n.
  set yS := \sum_(i < n.+1) _ * _.*2 in P4; rewrite -/yS.
  set x1S := \sum_(i < _) _ in P2.
  set y1S := \sum_(i < _) _ in P3.
  have x1Sy1SE : x1S + y1S <= (S_[1] n).*2 + α_[maxn (3 * a).-2 2] n.
    apply: sum_alpha_diffE => //.
    rewrite apeg32E //.
    by move: sam1C; rewrite -uiME uaiLEp2.
  rewrite (maxn_idPl _) // in x1Sy1SE.
  set x2S := \sum_(i < _) _ in P3.
  set y2S := \sum_(i < _) _ in P4.
  have x2y2SE : x2S + y2S <= (S_[1] n).*2 + α_[maxn 2 b] n.
    apply: sum_alpha_diffE => //; first by rewrite /pa eq_sym.
    have /H : 0 < (inord a : 'I_l.+2) < l.+1 by rewrite inordK // a_gt0.
    by rewrite ffunE inordK.
  rewrite -addnn {1}dsum_alphaL_S in P2.
  rewrite -addnn {1}dsum_alphaL_S in P3.
  rewrite -addnn {1}dsum_alphaL_S.
  have F4 k : S_[a.-1] k.+1 <= S_[(3 *a).-2] k + a.-1.
    apply: leq_trans (dsum_alpha3l _ _) _.
    rewrite leq_add2r.
    apply: (increasingE (increasing_dsum_alphaL_l _)).
    by rewrite -{2}[a]prednK // mulnS addSn add2n /=.
  have F4n := F4 n.
  have {F4}F4n1 := F4 n.+1.
  have F5 k :
    S_[l.+1] k.+1 + S_[1] k.+1 + S_[b.+1] k.+1 <=
    S_[a.-1] k.+1 + S_[b.+2] k.+1 + S_[b] k + (α_[1] k).*2.
    have <- : a + b = l.+1 by rewrite addnC subnK.
    rewrite alphaL1E.
    rewrite -[X in _ <= X]addnA (leq_add _ (dsum_alphaL_alpha k b_gt1)) //.
    have := concaveEk1 1 a.-2 b.+1 (concave_dsum_alphaL_l k.+1).
    rewrite add1n prednK; last by rewrite -subn1 ltn_subRL addn0.
    by rewrite -addSnnS prednK // add1n [X in _ <= X]addnC.
  have F5n := F5 n.
  have {F5}F5n1 := F5 n.+1.
  have F6 k : S_[b.+2] k + S_[1] k <= S_[b.+1] k + S_[2] k.
    by have := concaveEk1 1 1 b (concave_dsum_alphaL_l k).
  have F6n := F6 n.+1.
  have {F6}F6n1 := F6 n.+2.
  have F72 := dsum_alphaL_S 2 n.+1.
  have F721 := dsum_alphaL_S 2 n.
  have F711 := dsum_alphaL_S 1 n.+1.
  have F71 := dsum_alphaL_S 1 n.
  have F73 := dsum_alphaL_S b n.  
  have F8 : α_[2] n.+1 <= α_[1] n.+2.
    have ->: α_[1] n.+2 = α_[3] n.+1 by rewrite alphaL_3E.
    by apply: increasing_alphaL_l.
  have F9 : α_[1] (n.+2) <= (α_[1] n).*2.+2.
    apply: leq_trans (leqnSn _).
    by apply: alphaL_4_5.
(* Lia should work now *)
  rewrite [_ +  α_[_] _]addnC -!addnA addnC !addnA leq_add2r.
  rewrite -[X in _ <= X]addnA.
  apply: leq_trans (leq_add P1 (leqnn _)).
  rewrite -(leq_add2r x1S).
  rewrite [X in _ <= X](_ : _ =
            a.*2 + x2P1 + x3P1 + yS + (x1P1 + xS + x1S)); last by ring.
  apply: leq_trans (leq_add (leqnn _) P2).
  rewrite {P2}!addnA.
  rewrite -(leq_add2r (y1S + x2S)).
  rewrite [X in _ <= X](_ : _ =
    a.*2 + x3P1 + yS + S_[(3 * a).-2] n + α_[(3 * a).-2] n +
    S_[(3 * a).-2] n.+1 + (x2P1 + y1S + x2S)); last by ring.
  apply: leq_trans (leq_add (leqnn _) P3).
  rewrite {P3}!addnA.
  rewrite -(leq_add2r y2S).
  rewrite [X in _ <= X](_ : _ =
            a.*2 + S_[(3 * a).-2] n + α_[(3 * a).-2] n + S_[(3 * a).-2] n.+1 +
            S_[2] n + α_[2] n + S_[2] n.+1 + (x3P1 + y2S + yS));
    last by ring.
  apply: leq_trans (leq_add (leqnn _) P4).
  rewrite [X in X <= _](_ : _ =
            S_[l.+1] n.+1 + S_[l.+1] n.+2 + (x1S + y1S) +
            (x2S + y2S)); last by ring.
  apply: leq_trans (leq_add (leqnn _) x2y2SE) _.
  rewrite addnC !addnA -addnA.
  apply: leq_trans (leq_add (leqnn _) x1Sy1SE) _.
  rewrite [X in _ <= X](_ : _ =
    a.*2 + S_[(3 * a).-2] n + S_[(3 * a).-2] n.+1 + S_[2] n +
    α_[2] n + S_[2] n.+1 + (S_[b] n.+1).*2 + α_[(3 * a).-2] n); last by ring.
  rewrite !addnA leq_add2r.    
  rewrite [X in _ <= X](_ : _ =
    2 + a.-1 + S_[(3 * a).-2] n.+1 + S_[2] n +
    α_[2] n + S_[2] n.+1 + (S_[b] n.+1).*2 + (S_[(3 * a).-2] n + a.-1)); 
      last first.
    suff ->: a.*2 =  2 + a.-1 + a.-1 by ring.
    by rewrite -mul2n -{1}[a]prednK //; ring.
  apply: leq_trans (leq_add (leqnn _) F4n).
  rewrite [X in _ <= X](_ : _ =
    2 + S_[2] n + α_[2] n +
    S_[2] n.+1 + (S_[b] n.+1).*2 + S_[a.-1] n.+1 + (S_[(3 * a).-2] n.+1 + a.-1)
    ); last by ring.
  apply: leq_trans (leq_add (leqnn _) F4n1).
  rewrite -(leq_add2r (S_[1] n.+1 + S_[b.+1] n.+1)).
  rewrite (maxn_idPr _) //.
  rewrite [X in X <= _](_ : _ =
    α_[b] n + S_[l.+1] n.+2 + (S_[1] n).*2 + (S_[1] n).*2 +
    (S_[l.+1] n.+1 + S_[1] n.+1 + S_[b.+1] n.+1)); last by ring.
  apply: leq_trans (leq_add (leqnn _) F5n) _.
  rewrite -(leq_add2r (S_[1] n.+2 + S_[b.+1] n.+2)).
  rewrite [X in X <= _](_ : _ =
    α_[b] n + (S_[1] n).*2 + (S_[1] n).*2 +
   (S_[a.-1] n.+1 + S_[b.+2] n.+1 + S_[b] n + (α_[1] n).*2) +
   (S_[l.+1] n.+2 + S_[1] n.+2 + S_[b.+1] n.+2)); last by ring.
  apply: leq_trans (leq_add (leqnn _) F5n1) _.
  rewrite [X in X <= _](_ : _ =
    α_[b] n + (S_[1] n).*2 + (S_[1] n).*2 +
    (S_[b.+2] n.+1 + S_[b] n + (α_[1] n).*2) +
    (S_[b.+2] n.+2 + S_[b] n.+1 + (α_[1] n.+1).*2)
    + (S_[a.-1] n.+1 + S_[a.-1] n.+2)); last by ring.
  rewrite [X in _ <= X](_ : _ =
    2 + S_[2] n + α_[2] n + S_[2] n.+1 + (S_[b] n.+1).*2
    + (S_[1] n.+1 + S_[b.+1] n.+1) + (S_[1] n.+2 + S_[b.+1] n.+2)
    + (S_[a.-1] n.+1 + S_[a.-1] n.+2)); last by ring.
  rewrite leq_add2r.
  rewrite -(leq_add2r (S_[1] n.+1)).
  rewrite [X in X <= _](_ : _ =
    α_[b] n + (S_[1] n).*2 + (S_[1] n).*2 + (S_[b] n + (α_[1] n).*2) +
    (S_[b.+2] n.+2 + S_[b] n.+1 + (α_[1] n.+1).*2) + 
    (S_[b.+2] n.+1 +  S_[1] n.+1)); last by ring.
  rewrite [X in _ <= X](_ : _ =
     2 + S_[2] n + α_[2] n + (S_[b] n.+1).*2 + S_[1] n.+1 + (S_[1] n.+2 + 
    S_[b.+1] n.+2) + S_[1] n.+1 + (S_[b.+1] n.+1 + S_[2] n.+1));
    last by ring.
  apply: leq_add F6n.
  rewrite [X in X <= _](_ : _ =
    α_[b] n + (S_[1] n).*2 + S_[b] n + 
   (S_[b.+2] n.+2 + (α_[1] n.+1).*2) +
   (S_[b] n.+1 + (S_[1] n + α_[1] n).*2)); last by rewrite -!mul2n; ring.
  rewrite [X in _ <= X](_ : _ =
    2 + S_[2] n + α_[2] n + (S_[b] n.+1) + 
     (S_[1] n.+2 + S_[b.+1] n.+2) + (S_[b] n.+1 + (S_[1] n.+1).*2));
    last by rewrite -!mul2n; ring.
  rewrite F71 leq_add2r.
  rewrite [X in X <= _](_ : _ =
     (S_[1] n).*2 + (S_[b.+2] n.+2 + (α_[1] n.+1).*2) +
     (S_[b] n + α_[b] n)); last by ring.
  rewrite [X in _ <= X](_ : _ =
    2 + S_[2] n + α_[2] n + (S_[1] n.+2 + S_[b.+1] n.+2) + S_[b] n.+1);
    last by ring.
  rewrite -F73 leq_add2r.
  rewrite -(leq_add2r (S_[1] n.+2 + S_[2] n.+2)).
  rewrite [X in X <= _](_ : _ =
    (S_[1] n).*2 + (S_[2] n.+2 + (α_[1] n.+1).*2) + (S_[b.+2] n.+2 + 
     S_[1] n.+2)); last by ring.
  rewrite [X in _ <= X](_ : _ =
    2 + S_[2] n + α_[2] n + (S_[1] n.+2 + S_[1] n.+2 ) +
   (S_[b.+1] n.+2 + S_[2] n.+2)); last by ring.
  apply: leq_add F6n1.
  rewrite F72 F721 F711 F71.
  rewrite [X in X <= _](_ : _ =
  ((α_[2] n.+1 +
  ((S_[1] n).*2 + S_[2] n + α_[2] n + (α_[1] n.+1).*2)))); last by ring.
  rewrite [X in _ <= X](_ : _ =
    2 +
    (α_[1] n + (α_[1] n)) +
    ((S_[1] n).*2 + S_[2] n + α_[2] n + (α_[1] n.+1).*2));
    last by rewrite -!mul2n; ring.
  rewrite leq_add2r.
  apply: leq_trans F8 _.
  rewrite addnn add2n.
  by apply: F9.
rewrite negb_and -leqNgt -ltnNge => oH.
have [/andP[a_gt1 /eqP bE1]|] := boolP ((1 < a) && (b == 1)).
(* 2 <= a and b = 1 *)
  have am1_gt0 : 0 < a.-1 by rewrite -subn1 subn_gt0.
  have lEa : l = a.
    have : a + b = l.+1 by rewrite addnC subnK //.
    by rewrite bE1 addn1 => [] [].
  have uaiLEp2 : u ai ldisk = p2.
    have /cH/subsetP/(_ (u ai ldisk) (codom_f _ _)) : 0 < ai < l.+1.
      by rewrite aiE a_gt0 lEa /=.
    by rewrite !inE aiE (negPf aH) orbF => /eqP.
  pose si i : configuration 4 n.+1 := 
     sgdist1 p2 (u (inord i)) (u (inord i.+1)).
  pose ti i : configuration 4 n.+1 := 
     sgdist2 p2 (u (inord i)) (u (inord i.+1)).
  have sitiH i : i < a.-1 ->
     [/\ codom (si i) \subset [:: p2; u (inord i.+1) ldisk ], 
         codom (ti i) \subset [:: u (inord i) ldisk; p2] & 
         d[u (inord i), u (inord i.+1)] = 
           D[[:: ↓[u (inord i)]; si i; ti i; ↓[u (inord i.+1)]]].+2].
    move=> iLa.
    have iLa1 : i < a by rewrite (leq_trans iLa) // ssrnat.leq_pred.
    apply: sgdistE => //.
    - by rewrite aMin1.
    - rewrite !aMin1 //; last by rewrite -[a]prednK.
      by rewrite /apeg /=; case: odd; rewrite // eq_sym.
    - by rewrite aMin1 1?eq_sym // -[a]prednK.
    - by rewrite aMin1.
    by rewrite aMin1 // -[a]prednK.
  pose pa := apeg a p1 p3.
  pose sam1 : configuration 4 n.+1 := sgdist1 pa (u (inord a.-1)) (u (inord a)).
  pose tam1 : configuration 4 n.+1 := sgdist2 pa (u (inord a.-1)) (u (inord a)).
  have [sam1C tam1C duam1ua1E] : 
     [/\ codom sam1 \subset [:: pa; u (inord a) ldisk ], 
         codom tam1 \subset [:: u (inord a.-1) ldisk; pa] & 
         d[u (inord a.-1), u (inord a)] = 
           D[[:: ↓[u (inord a.-1)]; sam1; tam1; ↓[u (inord a)]]].+2].
    apply: sgdistE; rewrite /pa //.
    - rewrite aMin1 ?prednK // /apeg -{2}[a]prednK //=.
      by case: odd; rewrite // eq_sym.
    - by rewrite uaiLEp2 aMin1 // prednK.
    - by rewrite uaiLEp2.
    - by rewrite aMin1 // prednK.
    by rewrite uaiLEp2.
  have {}tam1C : codom tam1 \subset [:: p1; p3].
    move: tam1C; rewrite aMin1; last by rewrite -{2}[a]prednK.
    rewrite -subn1 /pa /apeg /= odd_sub; case: odd => //=.
    by apply: codom_subC.
  pose u1 := 
    [ffun i =>
    if ((i : 'I_(3 * a).-2.+1) == 3 * a.-1 :>nat) then ↓[u (inord a.-1)] 
    else if (i == (3 * a.-1).+1 :>nat) then sam1
    else if (i %% 3) == 0 then ↓[u (inord (i %/ 3))]
    else if (i %% 3) == 1 then si (i %/ 3)
    else ti (i %/ 3)].
  have u10E : u1 ord0 = ↓[u ord0].
    rewrite ffunE /= ifN ?inord_eq0 //.
    by rewrite neq_ltn muln_gt0 /= -ltnS prednK //= a_gt1.
  have uiME : u1 ord_max = sam1.
    rewrite ffunE /= eqn_leq leqNgt -{2}[a]prednK // mulnS.
    rewrite addSn add2n ltnS leqnn /=.
    by rewrite -{1}[a]prednK // mulnS eqxx.
  pose u2 := 
    [ffun i : 'I_4 =>  
    if i == 0 :> nat then sam1 else
    if i == 1 :> nat then tam1 else
    if i == 2 :> nat then ↓[u ai] else ↓[u (inord (l.+1))]].
  have P1 : 
    a.*2 +
    \sum_(i < (3 * a).-2) 
        d[u1 (inord i), u1 (inord i.+1)] +
    \sum_(i < 3) 
        d[u2 (inord i), u2 (inord i.+1)] 
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
    rewrite big_ord_recr /=.
    rewrite [u2 (inord 2)]ffunE inordK //=.
    rewrite [u2 (inord 3)]ffunE inordK //=.
    rewrite [2 + _]addnC -!addnA 2![X in _ + X <= _]addnA addnA.
    have -> : \sum_(i < l.+1)  d[u (inord i), u (inord i.+1)] =
      \sum_(i < a.-1) (d[u (inord i), u (inord i.+1)]) + 
      d[u (inord a.-1), u ai] +
      d[u ai, u (inord ai.+1)].
      rewrite -lEa (_ : ai = inord l); last first.
        by apply/val_eqP; rewrite /= aiE inordK // lEa.
      case: l l_gt0 u => //= l1 _ f.
      rewrite 2!big_ord_recr //=; congr (_ + _ + d[f _, f _]).
      by apply/val_eqP; rewrite /= !inordK.
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
        by rewrite mod3E /= div3E.
      have -> : u1 (inord (3 * i).+1) = si i.
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
        by rewrite [_ <= i]leqNgt ltn_ord andbF mod3E /= div3E.
      have -> : u1 (inord (3 * i).+2) = ti i.
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
        by rewrite mod3E /= div3E.
      have -> : u1 (inord (3 * i).+3) = ↓[u (inord i.+1)].
        have -> : (3 * i).+3 = 3 * (i.+1) by rewrite mulnS addSn add2n.
        rewrite ffunE inordK; last first.
          rewrite ltnS (leq_trans (_ : _ <= 3 * (a.-1))) //.
            by rewrite leq_mul2l /=.
          by rewrite -{2}[a]prednK // mulnS addSn add2n /= ltnW.
        rewrite eqn_mul2l /=; case: eqP => [->//|_].
        rewrite eqn_leq [_ <= 3 * i.+1]leqNgt ltnS leq_mul2l /= ltn_ord andbF.
        by rewrite mod3E /= div3E.
      case: (sitiH i) => //= _ _.
      by rewrite !addnA addn0 add2n.
    - rewrite leq_eqVlt; apply/orP; left; apply/eqP.
      rewrite !big_ord_recr big_ord0 //= add0n !addnA.
      have -> : u2 (inord 0) = sam1 by rewrite ffunE /= inordK.
      have -> : u2 (inord 1) = tam1 by rewrite ffunE /= inordK.
      have -> : u2 (inord 2) = ↓[u ai] by rewrite ffunE /= inordK.
      by move: duam1ua1E; rewrite /= addn0 add2n !addnA !addSn.
    rewrite (_ : inord l.+1 = inord ai.+1); last first.
      by apply/val_eqP; rewrite /= !inordK // lEa.
    by apply/gdist_cunlift/shanoi_connect.
  set x1P1 := \sum_(_ < _) _ in P1.
  set x2P1 := \sum_(_ < _) _ in P1.
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
      rewrite -ltnS [a.-2.+1]prednK //.
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
      rewrite (leq_ltn_trans k3La) ?ltnS ?lEa //.
      move: k_gt0; rewrite andbT {1}(divn_eq k 3) k3mH addn0 muln_gt0.
      by case/andP.
    case: eqP => k3mH1.
      case: (sitiH (k %/ 3)); first by rewrite -[a.-1]prednK.
      set pp := u _ _; (suff <- : pp = apeg k p1 p3 by []); rewrite {}/pp.
      set i := inord _; have <- : apeg i p1 p3 = apeg k p1 p3.
        rewrite (divn_eq k 3) k3mH1 addn1 /apeg /= odd_mul andbT.
        by rewrite /i !inordK //= !ltnS lEa.  
      have H2 : (k %/ 3).+1 < l.+2 by rewrite !ltnS lEa (leq_trans k3La).
      rewrite -(@aMin1 i); last first.
        by rewrite !inordK // -{2}[a]prednK // ltnS // -[a.-1]prednK.
      congr (u _ _).
      by apply/val_eqP; rewrite /= !inordK.
    apply: codom_subC.
    case: (sitiH (k %/ 3)) => [|_]; first by rewrite -[a.-1]prednK.
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
  have a3B2_gt1 : 1 < (3 * a).-2.
    rewrite -subn2 leq_subRL.
      by rewrite (leq_trans (_ : 4 <= 3 * 2)) // leq_mul2l.
    by rewrite (leq_trans (_ : 2 <= 3 * 2)) // leq_mul2l.
  rewrite u10E uiME [apeg 0]/apeg /= in P2.
  have {}P2 := leq_trans P2 (leq_add (leq_add (leqnn _) (leq_sum_beta _ _))
                          (leqnn _)).
  rewrite -/x1P1 in P2.
  pose paS := apeg a.+1 p1 p3.
  have cH3 (k : 'I_4) :
    0 < k < 3 -> codom (u2 k) \subset [:: pa; apeg k p2 paS].
    case: k => [] [|[|[|]]] //= iH _; rewrite ffunE /=.
      apply: codom_subC.
      have := tam1C; rewrite /pa /paS /apeg /=; case: odd => //=.
      by apply: codom_subC.
    apply: codom_liftr.
    have /cH : 0 < ai < l.+1 by rewrite aiE a_gt0 // lEa /=.
    by rewrite /pa /paS {3}/apeg /= aiE; apply: codom_subC.
  have {cH3}P3 : 
    (S_[3] n.+1).*2 <=
     \sum_(i < 3)  d[u2 (inord i), u2 (inord i.+1)] +
     \sum_(k < n.+1) (u2 ord0 k != apeg 0 p2 paS) * beta n.+1 3 k +
     \sum_(k < n.+1) (u2 ord_max k != apeg 3 p2 paS) * beta n.+1 3 k.
    apply: IH cH3 => //; try by rewrite /pa /paS // eq_sym.
    by rewrite /pa /paS /apeg /=; case: odd; rewrite //= eq_sym.
  have {}P3 := leq_trans P3 (leq_add (leqnn _) (leq_sum_beta _ _)).
  rewrite /pa /paS {1 3}/apeg /= -lEa in P3.
  rewrite !ffunE /= -/x2P1 (_ : inord l.+1 = ord_max) in P3; last first.
    by apply/val_eqP; rewrite /= inordK.
  rewrite [X in _ <= _ + X + _]sum_beta_S //= KH1 eqxx addn0.
  set xS := \sum_(i < n.+1) _ in P2; rewrite -/xS.
  rewrite [X in _ <= _ + _ + X]sum_beta_S //= KH2 mul1n.
  set yS := \sum_(i < _) _ * _.*2 in P3; rewrite -/yS.
  set x1S := \sum_(i < _) _ in P2.
  set y1S := \sum_(i < _) _ in P3.
  have x1Sy1SE : x1S + y1S <= (S_[1] n).*2 + α_[maxn (3 * a).-2 3] n.
    apply: sum_alpha_diffE => //.
    by move: sam1C; rewrite -uiME uaiLEp2 /pa apeg32E.
  rewrite (maxn_idPl _) // in x1Sy1SE; last first.
    by rewrite -subn2 ltn_subRL ltnW // (leq_mul2l 3 2).
  rewrite -addnn {1}dsum_alphaL_S in P2.
  rewrite -addnn {1}dsum_alphaL_S.
  have F4 k : S_[a.-1] k.+1 <= S_[(3 *a).-2] k + a.-1.
    apply: leq_trans (dsum_alpha3l _ _) _.
    rewrite leq_add2r.
    apply: (increasingE (increasing_dsum_alphaL_l _)).
    by rewrite -{2}[a]prednK // mulnS addSn add2n /=.
  have F4n := F4 n.
  have {F4}F4n1 := F4 n.+1.
  have F6 k : S_[a.+1] k + S_[1] k <= S_[a.-1] k + S_[3] k.
    have := concaveEk1 1 a.-2 2 (concave_dsum_alphaL_l k).
    by rewrite add1n addn2 !prednK // [_ + S_[3] _]addnC.
  have F6n := F6 n.+1.
  have {F6}F6n1 := F6 n.+2.
  have F72 := dsum_alphaL_S 3 n.+1.
  have F721 := dsum_alphaL_S 3 n.
  have F711 := dsum_alphaL_S 1 n.+1.
  have F71 := dsum_alphaL_S 1 n. 
  have F8 : α_[1] n.+2 = α_[3] n.+1 by rewrite alphaL_3E.
  have F9 : α_[1] (n.+2) <= (α_[1] n).*2.+2.
    apply: leq_trans (leqnSn _).
    by apply: alphaL_4_5.
(* Lia should work now *)
  rewrite [_ +  α_[_] _]addnC -!addnA addnC !addnA leq_add2r.
  rewrite -[X in _ <= X]addnA.
  apply: leq_trans (leq_add P1 (leqnn _)).
  rewrite -(leq_add2r x1S).
  rewrite [X in _ <= X](_ : _ =
            a.*2 + x2P1 + yS + (x1P1 + xS + x1S)); last by ring.
  apply: leq_trans (leq_add (leqnn _) P2).
  rewrite {P2}!addnA.
  rewrite -(leq_add2r y1S).
  rewrite [X in _ <= X](_ : _ =
     a.*2 + S_[(3 * a).-2] n + α_[(3 * a).-2] n + S_[(3 * a).-2] n.+1 +
     (x2P1 + y1S + yS)); last by ring.
  apply: leq_trans (leq_add (leqnn _) P3).
  rewrite {P3}//.
  rewrite [X in X <= _](_ : _ =
            S_[l.+1] n.+1 + S_[l.+1] n.+2 + (x1S + y1S));
           last by ring.
  apply: leq_trans (leq_add (leqnn _) x1Sy1SE) _; rewrite {x1Sy1SE}//.
  rewrite [X in _ <= X](_ : _ =
    a.*2 + S_[(3 * a).-2] n + S_[(3 * a).-2] n.+1 +
    (S_[3] n.+1).*2 + α_[(3 * a).-2] n); last by ring.
  rewrite !addnA leq_add2r.    
  rewrite -(leq_add2r (S_[a.-1] n.+1)).
  rewrite [X in _ <= X](_ : _ =
     2 + a.-1 + S_[(3 * a).-2] n.+1 + (S_[3] n.+1).*2 +
     S_[a.-1] n.+1 + (S_[(3 * a).-2] n + a.-1)); last first.
    suff ->: a.*2 =  2 + a.-1 + a.-1 by ring.
    by rewrite -mul2n -{1}[a]prednK //; ring.
  apply: leq_add F4n.
  rewrite -(leq_add2r (S_[a.-1] n.+2)).
  rewrite [X in _ <= X](_ : _ =
    2 + (S_[3] n.+1).*2 + S_[a.-1] n.+1 +
    S_[a.-1] n.+2 + (S_[(3 * a).-2] n.+1 + a.-1)); last by ring.
  apply: leq_add  F4n1.
  rewrite -(leq_add2r (S_[1] n.+1)).
  rewrite lEa.
  rewrite [X in X <= _](_ : _ =
     S_[a.+1] n.+2 + (S_[1] n).*2 + (S_[a.+1] n.+1  + S_[1] n.+1)); last ring.
  rewrite [X in _ <= X](_ : _ =
     2 + S_[3] n.+1 + S_[a.-1] n.+2 + S_[1] n.+1 +
     (S_[a.-1] n.+1 + S_[3] n.+1)); last by rewrite -addnn; ring.
  apply: leq_add _ F6n.
  rewrite -(leq_add2r (S_[1] n.+2 + S_[3] n.+2)).
  rewrite [X in X <= _](_ : _ =
     (S_[1] n).*2 + S_[3] n.+2 + (S_[a.+1] n.+2 +  S_[1] n.+2)); last by ring.
  rewrite [X in _ <= X](_ : _ =
     2 + S_[3] n.+1 + S_[1] n.+2 + S_[1] n.+1 + (S_[a.-1] n.+2 + S_[3] n.+2));
        last by ring.
  apply: leq_add _ F6n1.
  rewrite F72 F711 F71.
  rewrite [X in X <= _](_ : _ =
      α_[3] n.+1 + (S_[1] n + S_[1] n+ (S_[3] n.+1))); 
        last by rewrite -addnn; ring.
  rewrite [X in _ <= X](_ : _ =
    2 + (α_[1] n).*2  + α_[1] n.+1 + (S_[1] n + S_[1] n + (S_[3] n.+1)));
     last by rewrite -addnn; ring_simplify.
  by rewrite leq_add2r -F8 add2n (leq_trans F9) // leq_addr.
rewrite negb_and -leqNgt => o1H.
have [/eqP aE1| aD1] := boolP (a == 1).
  have b_gt0 : 0 < b by rewrite /b aE1 subn1.
  have bE : b = l by rewrite /b aE1 subn1.
  move: b_gt0; rewrite leq_eqVlt => /orP[/eqP bE1 | b_gt1]; last first.
    have u1C : u (inord 1) ldisk = p2.
      move: aH; rewrite aE1 /apeg /=.
      have /cH : 0 < (inord 1 : 'I_l.+2) < l.+1 by rewrite inordK.
      move=> /subsetP/(_ (u (inord 1) ldisk) (codom_f _ _)).
      by rewrite !inE => /orP[] /eqP-> //; rewrite /apeg inordK //= eqxx.
    pose s0 : configuration 4 n.+1 :=  sgdist1 p3 (u ord0) (u (inord 1)).
    pose t0 : configuration 4 n.+1 :=  sgdist2 p3 (u ord0) (u (inord 1)).
    have [s0C t0C ds0t0E] :
        [/\ codom s0 \subset [:: p3; u (inord 1) ldisk ], 
         codom t0 \subset [:: u ord0 ldisk; p3] & 
         d[u ord0, u (inord 1)] = 
           D[[:: ↓[u ord0]; s0; t0; ↓[u (inord 1)]]].+2].
      apply: sgdistE => //.
      - by rewrite  /= KH1.
      - by rewrite KH1 u1C.
      - by rewrite u1C eq_sym.
      - by rewrite KH1.
      by rewrite u1C.
    pose u1 := 
      [ffun i : 'I_4 =>  
      if i == 0 :> nat then ↓[u ord0] else
      if i == 1 :> nat then s0 else
      if i == 2 :> nat then t0 else ↓[u (inord 1)]].
    pose u2 := [ffun i => ↓[u (inord ((i : 'I_b.+1) + 1))]].
    have P1 : 
       2 +
       \sum_(i < 3) 
         d[u1 (inord i), u1 (inord i.+1)] +
       \sum_(i < b)  d[u2 (inord i), u2 (inord i.+1)] 
      <= 
       \sum_(i < l.+1) d[u (inord i), u (inord i.+1)].
      have -> : \sum_(i < l.+1)  d[u (inord i), u (inord i.+1)] =
        d[u ord0, u (inord 1)] +
        \sum_(i < b) d[u (inord (a +i)), u (inord (a + i.+1))].
        rewrite big_ord_recl /= bE.
        congr (d[u _,u _] + _); first by apply/val_eqP; rewrite /= inordK.
        apply: eq_bigr => i _.
        congr (d[u _,u _]); apply/val_eqP; rewrite aE1 /= inordK //=.
          by rewrite /bump add1n !ltnS ltnW.
        by rewrite /bump add1n !ltnS.
      apply: leq_add.
        rewrite leq_eqVlt; apply/orP; left; apply/eqP.
        rewrite !big_ord_recr /= big_ord0 add0n.
        rewrite !ffunE !inordK //= add2n.
        by rewrite ds0t0E /= addn0 !addnA.
      apply: leq_sum => i _.
      rewrite ffunE inordK; last by rewrite ltnS ltnW.
      rewrite ffunE inordK; last by rewrite ltnS.
      rewrite aE1 addSn [i + _]addnC addnS.
      by apply/gdist_cunlift/shanoi_connect.
    set x1P1 := \sum_(_ < _) _ in P1.
    set x2P1 := \sum_(_ < _) _ in P1.
    set xP1 := \sum_(_ < _) _ in P1.
    rewrite -/xP1.
    have cH2 (k : 'I_4) :
      0 < k < 3 -> codom (u1 k) \subset [:: p3; apeg k p1 p2]. 
      case: k => [] [|[|[|]]] //= iH _; rewrite ffunE /= /apeg /=.
        by have := s0C; rewrite u1C.
      by apply: codom_subC; rewrite -KH1.
    have {cH2}P2 : 
      (S_[3] n.+1).*2 <=
        \sum_(i < 3)  d[u1 (inord i), u1 (inord i.+1)] +
        \sum_(k < n.+1) (↓[u (inord 0)] k != apeg 0 p1 p2) *
                         beta n.+1 3 k +
        \sum_(k < n.+1)
          (↓[u (inord 1)] k != apeg 3 p1 p2) * beta n.+1 3 k.
      apply: leq_trans (IH _ _ _ _ _ _ _ cH2) _ => //.
        by rewrite eq_sym.
      repeat apply: leq_add => //; rewrite leq_eqVlt;
             apply/orP; left; apply/eqP.
        by apply: eq_bigr => i _; rewrite !ffunE inord_eq0.
      by apply: eq_bigr => i _; rewrite !ffunE.
    have {}P2 := leq_trans P2 
               (leq_add (leq_add (leqnn _) (leq_sum_beta _ _)) (leqnn _)).
    rewrite -/x2P1 (inord_eq0) // -[in inord 1]aE1 /apeg /= in P2.
    have cH3 (k : 'I_b.+1) :
      0 < k < b -> codom (u2 k) \subset [:: p2; apeg k p3 p1].
      rewrite [X in k < X]bE => /andP[k_gt0 kLb].
      rewrite ffunE addn1; apply: codom_liftr.
      rewrite (_ : apeg _ _ _ = apeg k.+1 p1 p3); last first.
        by rewrite /apeg /=; case: odd.
      have := @cH (inord k.+1).
      rewrite inordK //=; first by apply.
      by rewrite ltnS (leq_trans kLb).
    have {cH3}P3 : 
     (S_[b] n.+1).*2 <=
       \sum_(i < b)  d[u2 (inord i), u2 (inord i.+1)] +
       \sum_(k < n.+1) (↓[u (inord 1)] k != p3) * beta n.+1 b k +
       \sum_(k < n.+1) (↓[u ord_max] k != apeg b p3 p1) * beta n.+1 b k.
      apply: leq_trans (IH _ _ _ _ _ _ _ cH3) _ => //; try by rewrite eq_sym.
      repeat apply: leq_add => //; rewrite leq_eqVlt; 
         apply/orP; left; apply/eqP; apply: eq_bigr => i _.
        by rewrite !ffunE.
      rewrite !ffunE /= addn1 bE; congr ((u _ _ != _) * _).
      by apply/val_eqP; rewrite /= inordK.
    have {}P3 := leq_trans P3 (leq_add (leqnn _) (leq_sum_beta _ _)).
    rewrite -/x2P1 (_ : apeg b p3 p1 = apeg l.+1 p1 p3) in P3; last first.
      by rewrite bE /apeg /= if_neg.
    rewrite -[in inord 1]aE1 in P3.
    rewrite !sum_beta_S // KH1 eqxx mul0n addn0 KH2 mul1n.
    set xS := \sum_(i < _) _ * _.*2 in P2; rewrite -/xS.
    set yS := \sum_(i < _) _ * _.*2 in P3; rewrite -/yS.
    set x1S := \sum_(i < _) _ * _ in P2.
    set y1S := \sum_(i < _) _ * _ in P3.
    have x1Sy1SE : x1S + y1S <= (S_[1] n).*2 + α_[maxn 3 b] n.
      rewrite /x1S /y1S. 
      apply: sum_alpha_diffE => //.
      apply: codom_liftr.
      have /cH : 0 < (inord a : 'I_l.+2) < l.+1 by rewrite aE1 inordK.
      by rewrite inordK aE1.
    rewrite -/x1P1 in P2.
    rewrite -addnn {1}dsum_alphaL_S -bE.
    (* Fix here *)
    rewrite [_ +  α_[_] _]addnC -!addnA addnC !addnA leq_add2r.
    apply: leq_trans (leq_add (leq_add P1 (leqnn _)) (leqnn _)).
    rewrite -(leq_add2r x1S).
    rewrite [X in _ <= X](_ : _ =
            2 + x2P1 + yS + (x1P1 + xS + x1S)); last by ring.
    apply: leq_trans (leq_add (leqnn _) P2); rewrite {P2}//.
    rewrite -(leq_add2r y1S).
    rewrite [X in _ <= X](_ : _ =
       2 + (S_[3] n.+1).*2 + (x2P1 + y1S + yS)); 
        last by ring.   
    apply: leq_trans (leq_add (leqnn _) P3).
    rewrite [X in X <= _](_ : _ =
      S_[b.+1] n.+1 + S_[b.+1] n.+2 + (x1S + y1S)); last by ring.
    apply: leq_trans (leq_add (leqnn _) x1Sy1SE) _; rewrite {x1Sy1SE}//.
    move: b_gt1; rewrite leq_eqVlt => /orP[/eqP bE2|b_gt2].
      rewrite -bE2 (maxn_idPl _) //.
      rewrite [S_[3] n.+2]dsum_alphaL_S.
      rewrite [X in X <= _](_ : _ =
         α_[3] n.+1 + (S_[1] n).*2 + α_[3] n + (S_[3] n.+1).*2); 
          last by rewrite -!addnn; ring.
      rewrite [X in _ <= X]addnAC leq_add2r.
      rewrite !alphaL_3E.
      rewrite add2n -[_.*2.+2]add1n.
      apply: leq_trans (leq_add (leqnn _) (leq_dsum_alpha_2l_1 _)) .
      rewrite !dsum_alphaL_S.
      rewrite [X in _ <= X](_ : _ =
        1 + (α_[1] n).*2 +  (S_[1] n).*2 + α_[1] n.+1);
          last by rewrite -!addnn; ring.
      by rewrite !leq_add2r add1n alphaL_4_5.
    rewrite (maxn_idPr _) // -[2 + _](doubleD 1) add1n.
    rewrite -dsum_alpha3_S addnA.
    rewrite -[X in _ <= _ + X]addnn addnA [X in _ <= _ + X] dsum_alphaL_S.
    rewrite !addnA leq_add2r.
    rewrite ![in X in _ <= X.*2 + _ + _]dsum_alphaL_S.
    rewrite !doubleD -!addnA [X in _ <= X]addnC !addnA leq_add2r.
    rewrite [X in _ <= X](_ : _ =
      (S_[b] n + (α_[1] n).*2) + (S_[b] n.+1 + (α_[1] n.+1).*2)); last by ring.
    rewrite !alphaL1E.
    by apply: leq_add; apply: dsum_alphaL_alpha; apply: ltnW.
  have /cH : 0 < (inord 1 : 'I_l.+2) < l.+1 by rewrite inordK.
  move=> /subsetP /(_ (u (inord 1) ldisk) (codom_f _ _)).
  rewrite !inE {1 2}/apeg inordK //=.
  have := aH; rewrite (_ : inord a = inord 1); last first.
    by apply/val_eqP; rewrite /= !inordK // aE1.
  rewrite aE1 {1}/apeg /= => /negPf->; rewrite orbF => /eqP u1LE. 
  case: (@sgdistE _ p3 (u ord0) (u (inord 1))) => //.
  - by rewrite KH1.
  - by rewrite KH1 u1LE.
  - by rewrite u1LE eq_sym.
  - by rewrite KH1.
  by rewrite u1LE.
  set s0 := sgdist1 _ _ _; set t0 := sgdist2 _ _ _.
  move=> s0C t0C du0u1; rewrite /= !addnA addn0 in du0u1.
  pose u1 := 
    [ffun i =>  
      if (i : 'I_5) == 0 :> nat then ↓[u ord0] else
      if i == 1 :> nat then s0 else
      if i == 2 :> nat then t0 else 
      if i == 3 :> nat then ↓[u (inord 1)] else ↓[u (inord 2)]].
  have P1 : 
    2 + \sum_(i < 4)  d[u1 (inord i), u1 (inord i.+1)] <=
    \sum_(i < l.+1) d[u (inord i), u (inord i.+1)].
    rewrite 2![in X in X <= _]big_ord_recr [X in _ <= X]big_ord_recr /= !addnA.
    apply: leq_add; last first.
      apply: leq_trans (gdist_cunlift _); last by apply: shanoi_connect.
      rewrite leq_eqVlt; apply/orP; left; apply/eqP.
      rewrite !ffunE ![in LHS]inordK //=.
      by congr(d[↓[u _],↓[u _]]); apply/val_eqP; rewrite /= !inordK //= -bE bE1.
    rewrite leq_eqVlt; apply/orP; left; apply/eqP.
    rewrite !big_ord_recr big_ord0 /= !ffunE !inordK //= add0n.
    rewrite -addnA add2n -du0u1.
    move: bE; rewrite -bE1.
    case: (l) u => // [] [] // uu _; rewrite big_ord_recl big_ord0 addn0 /=.
    by congr(d[uu _, uu _]); apply/val_eqP; rewrite /= !inordK.
  have cH1 (k : 'I_5) : 
    0 < k < 4 -> codom (u1 k) \subset [:: p3; apeg k p1 p2].
    case: k => [] [|[|[|[|]]]] //= iH _; rewrite !ffunE /apeg /=.
    - by have := s0C; rewrite u1LE.
    - by apply: codom_subC; rewrite -KH1.
    apply/codom_subC/subsetP=> i /codomP[x ->]; rewrite !ffunE.
    have /cH: 0 < (inord 1 : 'I_l.+2) < l.+1 by rewrite inordK //.
    by rewrite inordK // => 
        /subsetP /(_ (u (inord 1) (trshift 1 x)) (codom_f _ _)).
  have {cH1}P2 :
     (S_[4] n.+1).*2 <=
     \sum_(i < 4)  d[u1 (inord i), u1 (inord i.+1)] +
     \sum_(k < n.+1) (u1 ord0 k != apeg 0 p1 p2) * beta n.+1 4 k +
     \sum_(k < n.+1) (u1 ord_max k != apeg 4 p1 p2) * beta n.+1 4 k.
    by apply: IH cH1 => //; rewrite eq_sym.
  set xP := \sum_(_ < _) _; rewrite -/xP in P1.
  have {}P2 := 
    leq_trans P2 (leq_add (leq_add (leqnn _ ) (leq_sum_beta _ _))
                          (leq_sum_beta _ _)).
  set x1P := \sum_(_ < _) _ in P1; rewrite -/x1P in P2.
  rewrite !ffunE /= (_ : inord 2 = ord_max) in P2; last first.
    by apply: val_inj; rewrite /= inordK // -bE bE1.
  rewrite (_ : apeg 4 p1 p2 = apeg l.+1 p1 p3) in P2; last first.
    by rewrite -bE -bE1.
  set x1S := \sum_(_ < _) _ in P2; set x2S := \sum_(_ < _) _ in P2.
  rewrite !sum_beta_S //= KH1 KH2 !eqxx !addn0 mul1n.
  rewrite -/x1S -/x2S -!addnA.
  apply: leq_trans (leq_add P1 (leqnn _)).
  rewrite -!addnA addnC !addnA -addnA.
  apply: leq_trans (leq_add P2 (leqnn _)).
  rewrite -bE -bE1 -addnn {2}dsum_alphaL_S addnA.
  rewrite [_ + 2]addnC !addnA leq_add2r addnC.
  by apply: leq_dsum_alpha_2l_l 2 n.+1.
have aEl : a = l.+1.
  apply/eqP; rewrite eqn_leq aLld1 /=.
  case/orP: oH; first by case: (a) aD1 a_gt0 => [|[|]].
  case/orP: o1H; first by case: (a) aD1 a_gt0 => [|[|]].
  rewrite /b prednK // => H1 lLa; move: lLa H1.
  by rewrite leq_eqVlt => /orP[] // /eqP ->; rewrite subSn // subnn eqxx.
have bE0 : b = 0 by rewrite /b aEl subnn.
pose si i : configuration 4 n.+1 := 
  sgdist1 p2 (u (inord i)) (u (inord i.+1)).
pose ti i : configuration 4 n.+1 := 
   sgdist2 p2 (u (inord i)) (u (inord i.+1)).
have sitiH i : i < l ->
   [/\ codom (si i) \subset [:: p2; u (inord i.+1) ldisk ], 
       codom (ti i) \subset [:: u (inord i) ldisk; p2] & 
       d[u (inord i), u (inord i.+1)] = 
         D[[:: ↓[u (inord i)]; si i; ti i; ↓[u (inord i.+1)]]].+2].
  move=> iLl.
  have iLl1 : i < l.+1 by rewrite (leq_trans iLl).
  apply: sgdistE => //.
  - by rewrite aMin1 // aEl.
  - rewrite !aMin1 ?aEl //.
    by rewrite /apeg /=; case: odd; rewrite // eq_sym.
  - by rewrite aMin1 ?aEl // eq_sym.
  - by rewrite aMin1 // aEl.
  by rewrite aMin1 // aEl.
pose u1 := 
  [ffun i =>
    if ((i : 'I_(3 * l).+2) == (3 * l).+1 :>nat) then ↓[u ai] 
    else if (i %% 3) == 0 then ↓[u (inord (i %/ 3))]
    else if (i %% 3) == 1 then si (i %/ 3)
    else ti (i %/ 3)].
have u10E : u1 ord0 = ↓[u ord0].
  rewrite ffunE /=.
  by congr (↓[u _]); apply/val_eqP; rewrite /= inordK.
have u1mE : u1 ord_max = ↓[u ord_max].
  rewrite ffunE eqxx.
  by congr (↓[u _]); apply/val_eqP/eqP; rewrite /= inordK.
have P1 : 
    l.*2 + \sum_(i < (3 * l).+1) d[u1 (inord i), u1 (inord i.+1)]
    <= 
    \sum_(i < l.+1) d[u (inord i), u (inord i.+1)].
  rewrite !big_ord_recr /=.
  rewrite addnA; apply: leq_add; last first. 
    apply: leq_trans (gdist_cunlift _); last by apply: shanoi_connect.
    rewrite leq_eqVlt; apply/orP; left; apply/eqP.
    rewrite !ffunE !inordK ?eqxx //.
    rewrite eqn_leq [_ <= _ * _]leqNgt leqnn andbF mod3E /= div3E.
    congr (d[↓[u _], ↓[u _]]); apply/val_eqP; rewrite /= ?mulKn //.
    by rewrite inordK // aiE aEl.
  rewrite leq_eqVlt; apply/orP; left; apply/eqP.
  have -> := @sum3E _ (fun i => d[u1 (inord i), u1 (inord i.+1)]).
  have -> : l.*2 = \sum_(i < l) 2.
    by rewrite sum_nat_const /= cardT size_enum_ord muln2.
  rewrite -big_split /=; apply: eq_bigr => i _.
  rewrite ffunE !inordK //; last first.
    by rewrite ltnS ltnW // ltnS leq_mul2l /= ltnW.
  rewrite eqn_leq [_ <= _ * _]leqNgt ltnS leq_mul2l //=.
  rewrite (ltnW (ltn_ord _)) andbF mod3E /= div3E.
  rewrite ffunE !inordK //; last first.
    by rewrite !ltnS leq_mul2l /= ltnW.
  rewrite eqn_leq [_.+1 <= _]leqNgt !ltnS leq_mul2l /= [_ <= i]leqNgt.
  rewrite ltn_ord andbF mod3E /= div3E -[(_ * _).+3](mulnDr 3 1 i) add1n.
  rewrite ffunE !inordK //; last first.
    by rewrite!ltnS ltn_mul2l /=.
  rewrite !mod3E /= !div3E ifN; last first.
    case: eqP => // eH.
    have : (3 * i).+2 %% 3 = (3 * l).+1 %% 3 by rewrite eH.
    by rewrite !mod3E.
  rewrite ffunE inordK; last first.
    by rewrite ltnS ltnW // ltnS leq_mul2l /=.
  rewrite mod3E /= div3E ifN.
    case: (sitiH i) => //= _ _ ->.
    by rewrite /= !addnA addn0.
  case: eqP => // eH.
  have : (3 * i.+1) %% 3 = (3 * l).+1 %% 3 by rewrite eH.
  by rewrite !mod3E.
have cH1 (k : 'I_(3 * l).+2) : 
    0 < k < (3 * l).+1 -> codom (u1 k) \subset [:: p2; apeg k p1 p3].
  rewrite !ffunE.
  case: eqP => [->|/eqP kD3l1]; first by rewrite ltnn andbF.
  case: eqP => [km3E0|/eqP km3D0].
    rewrite {1 2 4}(divn_eq k 3) km3E0 addn0.
    rewrite ltnS mulnC muln_gt0 leq_mul2l /= => /andP[k3_gt0 k3Ll].
    rewrite /apeg odd_mul /=.
    have:= @H (inord (k %/ 3)); rewrite ffunE inordK //; last first.
      by apply: leq_trans k3Ll _.
    by apply; rewrite k3_gt0.
  case: eqP => [km3E1|/eqP km3D1].
    rewrite {1 2 4}(divn_eq k 3) km3E1 addn1 !ltnS /= mulnC ltn_mul2l /= => H1.
    case: (sitiH (k %/ 3)) => //.
    rewrite /apeg /= odd_mul /=.
    by rewrite aMin1 // aEl ltnS.
  have km3E2 : k %% 3 = 2.
    by case: (_ %% _) (ltn_mod k 3) km3D0 km3D1 => // [] [|[|]].
  rewrite {1 2 4}(divn_eq k 3) km3E2 addn2 /= ltnS => H1.
  have {}H1 : k %/ 3 < l.
    by rewrite -[_ < _](ltn_mul2r 3) [l * 3]mulnC (leq_ltn_trans _ H1).
  apply: codom_subC.
  case: (sitiH (k %/ 3)) => // _.
  rewrite /apeg /= odd_mul /= negbK andbT.
  by rewrite aMin1 // (leq_trans H1) // aEl.
have {cH1}P2 : 
   (S_[(3 * l).+1] n.+1).*2 <=
     \sum_(i < (3 * l).+1)  d[u1 (inord i), u1 (inord i.+1)] +
     \sum_(k < n.+1) (u1 ord0 k != apeg 0 p1 p3) * beta n.+1 (3 * l).+1 k +
    \sum_(k < n.+1)
       (u1 ord_max k != apeg (3 * l).+1 p1 p3) * beta n.+1 (3 * l).+1 k.
  by apply: IH cH1.
 have {}P2 := leq_trans P2 (leq_add (leq_add (leqnn _) (leq_sum_beta _ _))
                          (leq_sum_beta _ _)).
set xP := \sum_(_ < _) _; rewrite -/xP in P1.
set x1P := \sum_(_ < _) _ in P1.
rewrite -/x1P [apeg 0]/apeg /= (_ : apeg (3 * l).+1 = apeg l.+1) in P2
   ; last first.
  by rewrite /apeg /= odd_mul.
rewrite !sum_beta_S // KH1 KH2 [apeg 0]/apeg /= !eqxx addn0 mul1n.
rewrite !ffunE /= eqxx inord_eq0 // (_ : ai = ord_max) in P2; last first.
  by apply: val_inj; rewrite /= inordK.
set x1S := \sum_(_ < _) _ in P2; set x2S := \sum_(_ < _) _ in P2.
rewrite -/x1S -/x2S .
rewrite -addnn {1}dsum_alphaL_S addnAC !addnA leq_add2r.
rewrite -[X in _ <= X]addnA.
apply: leq_trans (leq_add P1 (leqnn _)).
rewrite -[X in _ <= X]addnA [x1P + _]addnA.
apply: leq_trans (leq_add (leqnn _) P2).
apply: leq_trans (leq_dsum_alpha_2l_l _ _) _.
rewrite addnC; apply: leq_add.
  by rewrite -addnn -addn1 leq_add.
rewrite leq_double.
apply: (increasingE (increasing_dsum_alphaL_l _)).
by rewrite doubleS ltnS -mul2n ltn_mul2r l_ggt0.
Qed.

End Case1.

(* This corresponds to the subcase of 4.2 when E is empty *)
Section Case2.

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


Variable n : nat.

Hypothesis nLm : n < m.

Lemma case2 l (u :  {ffun 'I_l.+2 -> configuration 4 n.+2}) 
              (p1 p2 p3: peg 4) :
   p1 != p2 -> p1 != p3 -> p2 != p3 ->
   p1 != p0 -> p2 != p0 -> p3 != p0 ->
  (forall k : 'I_l.+2,
     0 < k < l.+1 -> codom (u k) \subset [:: p2; apeg k p1 p3]) ->
  (u ord0 ord_max = p1) ->
  (u ord_max ord_max = apeg l.+1 p1 p3) ->
  (forall k, u k ldisk = apeg k p1 p3) ->
  (S_[l.+1] n.+2).*2 <= 
  \sum_(i < l.+1)  d[u (inord i), u (inord i.+1)] +
  \sum_(k < n.+2) (u ord0 k != apeg 0 p1 p3) * beta n.+2 l.+1 k +
  \sum_(k < n.+2) (u ord_max k != apeg l.+1 p1 p3) * beta n.+2 l.+1 k.
Proof.
move=> p1Dp2 p1Dp3 p2Dp3 p1Dp0 p2Dp0 p3Dp0.
move=> /= cH KH1 KH2 ukLE.
pose u':= ([ffun i => ↓[u i]] : {ffun 'I_l.+2 -> configuration 4 n.+1})
 : {ffun 'I_l.+2 -> configuration 4 n.+1}.
have H: forall k : 'I_l.+2,
    0 < k < l.+1 -> codom (u' k) \subset [:: p2; apeg k p1 p3].
  by move=> k kH; rewrite ffunE; apply/codom_liftr/cH.
have apegpaD2 a : apeg a p1 p3 != p2.
  by rewrite /apeg; case: odd; rewrite // eq_sym.
have apegpaD0 a : apeg a p1 p3 != p0.
  by rewrite /apeg; case: odd; rewrite // eq_sym.
pose si i : configuration 4 n.+1 := 
    sgdist1 p2 (u (inord i)) (u (inord i.+1)).
pose ti i : configuration 4 n.+1 := 
    sgdist2 p2 (u (inord i)) (u (inord i.+1)).
have sitiH i : i < l.+1 ->
    [/\ codom (si i) \subset [:: p2; u (inord i.+1) ldisk ], 
        codom (ti i) \subset [:: u (inord i) ldisk; p2] & 
        d[u (inord i), u (inord i.+1)] = 
          D[[:: ↓[u (inord i)]; si i; ti i; ↓[u (inord i.+1)]]].+2].
  move=> iLl.
  have i1Ll1 : i <= l by [].
  apply: sgdistE; rewrite ?ukLE //.
    rewrite /apeg /= !inordK //=; last first.
      by rewrite ltnS ltnW // ltnS.
    by case: odd; rewrite //= eq_sym.
  by rewrite eq_sym.
pose u1 := 
  [ffun i =>
  if ((i : 'I_(3 * l.+1).+1) %% 3) == 0 then ↓[u (inord (i %/ 3))]
  else if (i %% 3) == 1 then si (i %/ 3)
  else ti (i %/ 3)].
have u10E : u1 ord0 = ↓[u ord0].
  rewrite ffunE /=.
  by congr (↓[u _]); apply/val_eqP; rewrite /= inordK.
have u1ME : u1 ord_max = ↓[u ord_max].
  rewrite ffunE /= mod3E /= div3E.
  by congr (↓[u _]); apply/val_eqP; rewrite /= inordK.
have P1 : 
  l.+1.*2 + \sum_(i < (3 * (l.+1))) d[u1 (inord i), u1 (inord i.+1)]
  = 
  \sum_(i < l.+1) d[u (inord i), u (inord i.+1)].
  have -> := @sum3E _ (fun i => d[u1 (inord i), u1 (inord i.+1)]).
  have -> : l.+1.*2 = \sum_(i < l.+1) 2.
    by rewrite sum_nat_const /= cardT size_enum_ord muln2.
  rewrite -big_split /=; apply: eq_bigr => i _.
  rewrite ffunE !inordK //; last first.
    by rewrite ltnS leq_mul2l ltnW.
  rewrite mod3E /= div3E.
  rewrite ffunE inordK; last first.
    by rewrite ltnS ltn_mul2l /=.
  rewrite mod3E /= div3E.
  rewrite ffunE inordK; last first.
    by rewrite -[_.+3](mulnDr 3 1) ltnW // ltnS leq_mul2l /= add1n.
  rewrite mod3E /= div3E.
  rewrite ffunE inordK; last first.
    by rewrite -[(_ * _).+3](mulnDr 3 1) ltnS leq_mul2l /=.
  rewrite -[(_ * _).+3](mulnDr 3 1) mod3E /= div3E.
  case: (sitiH i) => // _ _.
  by rewrite /= add2n addn0 !addnA add1n.
have cH1 (k : 'I_(3 * l.+1).+1) : 
  0 < k < 3 * l.+1 -> codom (u1 k) \subset [:: p2; apeg k p1 p3].
  rewrite !ffunE.
  case: eqP => [km3E0|/eqP km3D0].
    rewrite {1 2 4}(divn_eq k 3) km3E0 addn0.
    rewrite muln_gt0 andbT [_ * 3]mulnC ltn_mul2l /= => /andP[k3_gt0 k3Ll].
    rewrite /apeg odd_mul /=.
    have:= @H (inord (k %/ 3)); rewrite ffunE inordK //; last first.
      by apply: leq_trans k3Ll _.
    by apply; rewrite k3_gt0.
  case: eqP => [km3E1|/eqP km3D1].
    rewrite {1 2 4}(divn_eq k 3) km3E1 addn1 /= => H1.
    have : 3 * (k %/ 3)  < 3 * l.+1.
      apply: leq_trans H1; first by rewrite mulnC ltnW.
      rewrite ltn_mul2l /= => k3Ll1.
    case: (sitiH (k %/ 3)) => //.
    by rewrite /apeg /= odd_mul /= ukLE // /apeg inordK //= andbT.
  have km3E2 : k %% 3 = 2.
    by case: (_ %% _) (ltn_mod k 3) km3D0 km3D1 => // [] [|[|]].
  rewrite {1 2 4}(divn_eq k 3) km3E2 addn2 /= -[_.+3](mulnDl 1 _ 3).
  rewrite mulnC leq_mul2l /= add1n => H1.
  apply: codom_subC.
  case: (sitiH (k %/ 3)) => // _ sH _; move: sH.
  rewrite ukLE // inordK ?(leq_trans H1) //.
  by rewrite /apeg /= odd_mul andbT negbK.
have {cH1}P2 : 
    (S_[3 * l.+1] n.+1).*2 <=
    \sum_(i < 3 * l.+1)  d[u1 (inord i), u1 (inord i.+1)] +
    \sum_(k < n.+1) (u1 ord0 k != apeg 0 p1 p3) * beta n.+1 (3 * l.+1) k +
    \sum_(k < n.+1)
      (u1 ord_max k != apeg (3 * l.+1) p1 p3) * beta n.+1 (3 * l.+1) k.
  by apply: IH cH1.
have {}P2 := leq_trans P2 (leq_add (leq_add (leqnn _) (leq_sum_beta _ _))
                        (leq_sum_beta _ _)).
rewrite [X in _ <= _ + X + _]big_ord_recr /= ukLE eqxx addn0.
rewrite [X in _ <= _ + X]big_ord_recr /= ukLE eqxx addn0.
set x1S := \sum_(_ < n.+1) _ in P2; set x2S := \sum_(_ < n.+1) _ in P2.
rewrite [X in _ <= _ + X + _](_ : _ = x1S); last first.
  apply: eq_bigr => i _.
  rewrite u10E ffunE /beta ifF; last first.
    by rewrite eqn_leq [_ <= i]leqNgt ltn_ord !andbF.
  by congr ((u _ _ != _) * _); apply/val_eqP; rewrite /=.
rewrite [X in _ <= _ + X](_ : _ = x2S); last first.
  apply: eq_bigr => i _.
  rewrite u1ME ffunE /beta ifF; last first.
    by rewrite eqn_leq [_ <= i]leqNgt ltn_ord !andbF.
  congr ((u _ _ != _) * _); first by apply/val_eqP.
  by rewrite /apeg odd_mul.
rewrite -P1 -!addnA addnC !addnA.
apply: leq_trans (leq_add P2 (leqnn _)).
by rewrite -doubleD leq_double dsum_alpha3l.
Qed.

End Case2.

(* This corresponds to 4.2 *)
Section Case3.

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


Variable n : nat.

Hypothesis nLm : n < m.

Lemma case3 l (u :  {ffun 'I_l.+2 -> configuration 4 n.+2}) 
              (p1 p2 p3: peg 4) :
   p1 != p2 -> p1 != p3 -> p2 != p3 ->
   p1 != p0 -> p2 != p0 -> p3 != p0 ->
  (forall k : 'I_l.+2,
     0 < k < l.+1 -> codom (u k) \subset [:: p2; apeg k p1 p3]) ->
  (u ord0 ord_max = p1) ->
  (u ord_max ord_max = apeg l.+1 p1 p3) ->
  (S_[l.+1] n.+2).*2 <= 
  \sum_(i < l.+1)  d[u (inord i), u (inord i.+1)] +
  \sum_(k < n.+2) (u ord0 k != apeg 0 p1 p3) * beta n.+2 l.+1 k +
  \sum_(k < n.+2) (u ord_max k != apeg l.+1 p1 p3) * beta n.+2 l.+1 k.
Proof.
move=> p1Dp2 p1Dp3 p2Dp3 p1Dp0 p2Dp0 p3Dp0.
move=> cH KH1 KH2.
pose u':= ([ffun i => ↓[u i]] : {ffun 'I_l.+2 -> configuration 4 n.+1})
 : {ffun 'I_l.+2 -> configuration 4 n.+1}.
have H: forall k : 'I_l.+2,
    0 < k < l.+1 -> codom (u' k) \subset [:: p2; apeg k p1 p3].
  by move=> k kH; rewrite ffunE; apply/codom_liftr/cH.
have apegpaD2 a : apeg a p1 p3 != p2.
  by rewrite /apeg; case: odd; rewrite // eq_sym.
have apegpaD0 a : apeg a p1 p3 != p0.
  by rewrite /apeg; case: odd; rewrite // eq_sym.
case: (pickP (fun i => u i ldisk != apeg i p1 p3)) => [x xH|pH]; last first.
  have {pH}ukLE k : u k ldisk = apeg k p1 p3 by have := pH k; case: eqP.
  have := case2 _ nLm _ _ _ _ _ _ cH KH1 KH2 ukLE.
  by apply.
have exH : exists x, u (inord x) ldisk != apeg x p1 p3.
  exists x; rewrite (_ : inord x = x) //.
  by apply/val_eqP; rewrite /= inordK.
case: (@ex_minnP _ exH) => a aH {exH}aMin.
have exL : exists x, (x <= l) && (u (inord x) ord_max != apeg x p1 p3).
  exists x; apply/andP; split => //.
    have := ltn_ord x; rewrite ltnS leq_eqVlt => /orP[] // /eqP xEl1.
    by case/eqP: xH; rewrite (_ : x = ord_max) //; apply/val_eqP/eqP => /=.
  by rewrite (_ : inord x = x) //; apply/val_eqP; rewrite /= inordK.
have exL1 y : (y <= l) && (u (inord y) ord_max != apeg y p1 p3) -> y <= l.
  by case/andP.
pose a1 := ex_maxn exL exL1.
have a1H: u (inord a1) ldisk != apeg a1 p1 p3.
  by rewrite /a1; case: ex_maxnP => i /andP[].
have a1Ll : a1 <= l by rewrite /a1; case: ex_maxnP => i /andP[].
have a1Max i : a1 < i < l.+2 -> u (inord i) ord_max = apeg i p1 p3.
  case/andP=> a1Li; rewrite ltnS leq_eqVlt => /orP[/eqP iEl1|iLl].
    by rewrite iEl1 (_ : inord l.+1 = ldisk) //;
       apply/val_eqP; rewrite /= inordK.
  move: a1Li; rewrite /a1; case: ex_maxnP => j _ /(_ i).
  by case: eqP; rewrite // andbT => _ /(_ iLl); rewrite ltnNge => ->.
have aLld1 : a <= l.+1.
  rewrite -ltnS; apply: leq_trans (ltn_ord x).
  rewrite ltnS; apply: aMin;rewrite (_ : inord x = x) //.
  by apply/val_eqP; rewrite /= inordK.
(* Showing the symmetry of the problem *)
wlog aLl1Ba1 : u p1 p3 p1Dp3 p2Dp3 p3Dp0 apegpaD2 apegpaD0 p1Dp2 p1Dp0 
   {u' H xH exL exL1}cH KH1 KH2 a a1 aH aLld1 aMin a1H a1Ll a1Max / a <= l.+1 - a1.
  move=> wH.
  case: (leqP a (l.+1 -a1)) => [aLl1Ba1|l1Ba1La].
    by apply: wH aLl1Ba1.
  have a_gt0 : 0 < a by apply: leq_ltn_trans l1Ba1La.
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
    by rewrite inord_eq0 // /apeg /p3' /p1' /=; case: odd.
  have -> : \sum_(k < n.+2) 
               (u ord_max k != apeg l.+1 p1 p3) * beta n.+2 l.+1 k =
            \sum_(k < n.+2) 
               (u1 ord0 k != apeg 0 p1' p3') * beta n.+2 l.+1 k.
    apply: eq_bigr => i _; congr (_ * _).
    rewrite ffunE subn0.
    suff -> : inord l.+1 = ord_max :> 'I_l.+2 by []. 
    by apply/val_eqP; rewrite /= inordK.
  rewrite addnAC.
  have FF : (l.+1 - a1) <= l.+1 - (l.+1 - a).
    by rewrite leq_sub2l // leq_subLR addnC -leq_subLR ltnW.
  have a1Ll1 : a1 <= l.+1 by rewrite (leq_trans a1Ll).
  apply: wH FF => //.
  - by rewrite /p1' /p3' /=; case: odd => //=; rewrite eq_sym.
  - by rewrite /p1' /p3' /=; case: odd => //=; rewrite eq_sym.
  - by rewrite /p1' /p3' /=; case: odd => //=; rewrite eq_sym.
  - by move=> b; rewrite /p1' /p3' /apeg /=; 
      do 2 case: odd => //=; rewrite eq_sym.
  - by move=> b; rewrite /p1' /p3' /apeg /=;
      do 2 case: odd => //=; rewrite eq_sym.
  - by rewrite /p1' /p3' /=; case: odd => //=; rewrite eq_sym.
  - by rewrite /p1' /p3' /=; case: odd => //=; rewrite eq_sym.
  - move=> k /andP[kH1 kH2]; rewrite ffunE.
    have F1 : k <= l.+1 by apply: ltnW.
    have F2 : l.+1 - k < l.+2.
      by rewrite ltn_subLR // addnS ltnS leq_addl.
    have -> :  apeg k p1' p3' = apeg (inord (l.+1 - k) : 'I_l.+2) p1 p3.
      rewrite /apeg /p1' /p3' inordK // odd_sub; last by apply: ltnW.
      by case: odd; case: odd.
    apply: cH; rewrite inordK // subn_gt0 // ltn_subLR // kH2 //=.
    by rewrite addnS ltnS -{1}[l.+1]add1n leq_add2r.
  - rewrite !ffunE /p1' subn0 -[RHS]KH2; congr (u _ _); apply/val_eqP.
    by rewrite /= inordK.
  - by rewrite !ffunE /p1' subnn inord_eq0 // KH1 /p3' /apeg; case: odd.
  - rewrite ffunE inordK /=; last by rewrite ltnS leq_subr.
    rewrite subKn ?(leq_trans a1Ll) //.
    have := a1H; rewrite /apeg /p1' /p3' odd_sub; do 2 case: odd => //=.
    by rewrite leq_subr.
  - move=> k; rewrite ffunE.
    case: leqP => //; rewrite ltn_subRL addnC -ltn_subRL => kH.
    have kLl1 : k < l.+1 by rewrite -subn_gt0 (leq_ltn_trans _ kH).
      rewrite inordK; last by rewrite ltnS ltnW.
      have /a1Max-> : a1 < l.+1 - k < l.+2 by rewrite kH /= ltnS leq_subr.
    rewrite /p1' /p3' /apeg odd_sub; last by apply: ltnW.
    by do 2 case: odd => //=; rewrite ?eqxx.
  - rewrite ffunE inordK ?ltnS ?leq_subr //.
    rewrite subKn //.
    have := aH; rewrite /apeg /p1' /p3' odd_sub; do 2 case: odd => //=.
    by rewrite -[a]prednK // subSS leq_subr.
  move=> k /andP[l1BaLk kLl2]; rewrite ffunE.
  rewrite inordK //; apply/eqP; case: eqP => // /eqP.
  suff -> : apeg k p1' p3' = apeg (l.+1 - k) p1 p3.
    by move=> /aMin; rewrite leqNgt ltn_subLR // addnC -ltn_subLR // l1BaLk.
  by rewrite /apeg /p1' /p3' odd_sub; do 2 case: odd.
pose u':= ([ffun i => ↓[u i]] : {ffun 'I_l.+2 -> configuration 4 n.+1})
 : {ffun 'I_l.+2 -> configuration 4 n.+1}.
have H: forall k : 'I_l.+2,
    0 < k < l.+1 -> codom (u' k) \subset [:: p2; apeg k p1 p3].
  by move=> k kH; rewrite ffunE; apply/codom_liftr/cH.
have aMin1 i : i < a -> u (inord i) ord_max = apeg i p1 p3.
  by case: (u (inord i) ord_max =P apeg i p1 p3) => // /eqP /aMin; case: leqP.
have a_gt0 : 0 < a.
  have : 0 <= a by [].
  rewrite leq_eqVlt => /orP[/eqP aE0|] //.
  by case/eqP: aH; rewrite inord_eq0 // -aE0.
pose ai : 'I_l.+2 := inord a.
have aiE : ai = a :> nat by rewrite inordK.
have aLa1 : a <= a1.
  case: leqP => // => a1La.
  by case/eqP: aH; apply: a1Max; rewrite a1La.
have uaLEp2 : u (inord a) ldisk = p2.
  have /cH : 0 < (inord a : 'I_l.+2) < l.+1.
    by rewrite inordK // a_gt0 /= (leq_ltn_trans _ (_ : a1 < l.+1)).
  move=> /subsetP/(_ (u (inord a) ldisk) (codom_f _ _)).
  by rewrite !inE inordK // (negPf aH) orbF => /eqP.
have ua1LEp2 : u (inord a1) ldisk = p2.
  have /cH : 0 < (inord a1 : 'I_l.+2) < l.+1.
    by rewrite inordK // !ltnS (leq_trans a1Ll) // (leq_trans a_gt0).
  move=> /subsetP/(_ (u (inord a1) ldisk) (codom_f _ _)).
  by rewrite !inE inordK ?ltnS ?(leq_trans a1Ll) // (negPf a1H) orbF => /eqP.
have a1_gt0 : 0 < a1 by apply: leq_trans a_gt0 _.
pose b := a1 - a.
pose c := l.+1 - a1.
have c_gt0 : 0 < c by rewrite subn_gt0.
have l1E : l.+1 = a + b + c.
  by rewrite /b /c [a + _]addnC subnK // addnC subnK // ltnW.
pose si i : configuration 4 n.+1 := 
   sgdist1 p2 (u (inord i)) (u (inord i.+1)).
pose ti i : configuration 4 n.+1 := 
   sgdist2 p2 (u (inord i)) (u (inord i.+1)).
have sitiH i : i < a.-1 ->
   [/\ codom (si i) \subset [:: p2; u (inord i.+1) ldisk ], 
       codom (ti i) \subset [:: u (inord i) ldisk; p2] & 
       d[u (inord i), u (inord i.+1)] = 
         D[[:: ↓[u (inord i)]; si i; ti i; ↓[u (inord i.+1)]]].+2].
  move=> iLa.
  have iLa1 : i < a by rewrite (leq_trans iLa) // ssrnat.leq_pred.
  apply: sgdistE; rewrite ?aMin1 // -1?[a]prednK //.
    by rewrite /apeg /=; case: odd; rewrite // eq_sym.
  by rewrite eq_sym.
pose pa := apeg a p1 p3.
pose sam1 : configuration 4 n.+1 := sgdist1 pa (u (inord a.-1)) (u (inord a)).
pose tam1 : configuration 4 n.+1 := sgdist2 pa (u (inord a.-1)) (u (inord a)).
have [sam1C tam1C duam1ua1E] : 
   [/\ codom sam1 \subset [:: pa; u (inord a) ldisk ], 
       codom tam1 \subset [:: u (inord a.-1) ldisk; pa] & 
       d[u (inord a.-1), u (inord a)] = 
         D[[:: ↓[u (inord a.-1)]; sam1; tam1; ↓[u (inord a)]]].+2].
  apply: sgdistE; rewrite /pa ?uaLEp2 ?aMin1  ?prednK //.
  by rewrite /apeg -subn1 odd_sub //; case: odd; rewrite // eq_sym.
rewrite uaLEp2 in sam1C.
have {}tam1C : codom tam1 \subset [:: p1; p3].
  move: tam1C; rewrite aMin1; last by rewrite -{2}[a]prednK.
  rewrite -subn1 /pa /apeg /= odd_sub; case: odd => //=.
  by apply: codom_subC.
pose u1 := 
  [ffun i : 'I_(3 * a).+1 =>
  if (i %% 3) == 0 then ↓[u (inord (i %/ 3))]
  else if (i %% 3) == 1 then 
     (if i == (3 * a.-1).+1 :> nat then sam1 else si (i %/ 3))
  else 
     (if i == (3 * a.-1).+2 :> nat then tam1 else ti (i %/ 3))].
have u10E : u1 ord0 = ↓[u ord0] by rewrite ffunE /= inord_eq0.
have uiME : u1 ord_max = ↓[u (inord a)] by rewrite ffunE /= mod3E /= div3E.
have P1 : 
  a.*2 +
  \sum_(i < 3 * a)  d[u1 (inord i), u1 (inord i.+1)] =
  \sum_(i < a) d[u (inord i), u (inord i.+1)].
  have -> := @sum3E _ (fun i => d[u1 (inord i), u1 (inord i.+1)]).
  have -> : a.*2 = \sum_(i < a) 2.
    by rewrite sum_nat_const /= cardT size_enum_ord muln2.
  rewrite -big_split /=.
  apply: eq_bigr => i _.
  have -> : u1 (inord (3 * i)) = ↓[u (inord i)].
    rewrite ffunE inordK; last by rewrite ltnS leq_mul2l /= ltnW.
    by rewrite mod3E /= div3E.
  have -> : u1 (inord (3 * i).+3) = ↓[u (inord i.+1)].
    rewrite -[(_ * _).+3](mulnDr 3 1).
    rewrite ffunE inordK; last by rewrite ltnS leq_mul2l /=.
    by rewrite mod3E /= div3E.
  have [/eqP iEa| iDa] := boolP (i == a.-1 :> nat).
    have -> : u1 (inord (3 * i).+1) = sam1.
      rewrite ffunE inordK; last by rewrite ltnS ltn_mul2l /=.
      rewrite mod3E /= div3E.
      by rewrite iEa eqxx.
    have -> : u1 (inord (3 * i).+2) = tam1.
      rewrite ffunE inordK; last first.
        by rewrite -[_.+3](mulnDr 3 1) ltnW // add1n ltnS leq_mul2l /=.
      rewrite mod3E /= div3E.
      by rewrite iEa eqxx.
    by rewrite iEa prednK // duam1ua1E /= -!addnA add2n !addnA addn0.
  have -> : u1 (inord (3 * i).+1) = si i.
    rewrite ffunE inordK; last by rewrite ltnS ltn_mul2l /=.
    rewrite mod3E /= div3E.
    by rewrite [_.+1 == _.+1]eqn_mul2l /= (negPf iDa).
  have -> : u1 (inord (3 * i).+2) = ti i.
    rewrite ffunE inordK; last first.
      by rewrite -[_.+3](mulnDr 3 1) ltnW // ltnS add1n leq_mul2l /=.
    rewrite mod3E /= div3E.
    by rewrite [_.+1 == _.+1]eqn_mul2l /= (negPf iDa).
  case: (sitiH i) => // [|_ _ ->].
    rewrite -ltnS prednK //.
    have := ltn_ord i; rewrite leq_eqVlt => /orP[] //.
    by rewrite -{2}[a]prednK // [_ == _](negPf iDa).
  by rewrite /= -!addnA add2n addn0.
have sitiHb i : a1 < i < l.+1 ->
   [/\ codom (si i) \subset [:: p2; u (inord i.+1) ldisk ], 
       codom (ti i) \subset [:: u (inord i) ldisk; p2] & 
       d[u (inord i), u (inord i.+1)] = 
         D[[:: ↓[u (inord i)]; si i; ti i; ↓[u (inord i.+1)]]].+2].
  move=> /andP[a1Li iLl].
  apply: sgdistE => //; 
    rewrite !a1Max ?a1Li ?(leq_trans a1Li) // ?(leq_trans iLl) //.
    by rewrite /apeg /=; case odd; rewrite // eq_sym.
  by rewrite eq_sym.
pose sa1 : configuration 4 n.+1 := 
  sgdist1 (apeg a1 p1 p3) (u (inord a1)) (u (inord a1.+1)).
pose ta1 : configuration 4 n.+1 := 
  sgdist2 (apeg a1 p1 p3) (u (inord a1)) (u (inord a1.+1)).
have [sa1C ta1C dua1uad1E] : 
   [/\ codom sa1 \subset [:: apeg a1 p1 p3; u (inord a1.+1) ldisk ], 
       codom ta1 \subset [:: u (inord a1) ldisk; apeg a1 p1 p3] & 
       d[u (inord a1), u (inord a1.+1)] = 
         D[[:: ↓[u (inord a1)]; sa1 ; ta1; ↓[u (inord a1.+1)]]].+2].
  apply: sgdistE; rewrite ?ua1LEp2 ?a1Max ?leqnn // 1?eq_sym //.
  by rewrite /apeg /=; case: odd; rewrite // eq_sym.
rewrite ua1LEp2 in ta1C.
have {}sa1C : codom sa1 \subset [:: p1; p3].
  move: sa1C; rewrite a1Max //; last by rewrite leqnn.
  by rewrite /apeg /=; case: odd => //=; apply: codom_subC.
pose u2 := 
  [ffun i : 'I_(3 * c).+1 =>
  if (i %% 3) == 0 then ↓[u (inord (a1 +(i %/ 3)))]
  else if (i %% 3) == 1 then 
     (if i == 1 :> nat then sa1 else si (a1 + (i %/ 3)))
  else 
     (if i == 2 :> nat then ta1 else ti (a1 + (i %/ 3)))].
have u20E : u2 ord0 = ↓[u (inord a1)] by rewrite ffunE /= addn0.
have u2ME : u2 ord_max = ↓[u ord_max].
  rewrite ffunE /= mod3E /= div3E addnC subnK //.
    by rewrite (_ : inord _ = ord_max) //; apply/val_eqP; rewrite /= inordK.
  by rewrite ltnW // ltnS.
have P2 : 
  c.*2 +
  \sum_(i < 3 * c)  d[u2 (inord i), u2 (inord i.+1)] =
  \sum_(a1 <= i < l.+1)  d[u (inord i), u (inord i.+1)].
  have -> : \sum_(a1 <= i < l.+1)  d[u (inord i), u (inord i.+1)] =
            \sum_(i < c)  d[u (inord (a1 + i)), u (inord (a1 + i).+1)].
    rewrite -{1}[a1]add0n big_addn big_mkord.
    by apply: eq_bigr => i _; rewrite addnC.
  have -> := @sum3E _ (fun i => d[u2 (inord i), u2 (inord i.+1)]).
  have -> : c.*2 = \sum_(i < c) 2.
    by rewrite sum_nat_const /= cardT size_enum_ord muln2.
  rewrite -big_split /=.
  apply: eq_bigr => i _.
  have -> : u2 (inord (3 * i)) = ↓[u (inord (a1 + i))].
    rewrite ffunE inordK; last by rewrite ltnS leq_mul2l /= ltnW.
    by rewrite mod3E /= div3E.
  have -> : u2 (inord (3 * i).+3) = ↓[u (inord (a1 + i).+1)].
    rewrite -[(_ * _).+3](mulnDr 3 1).
    rewrite ffunE inordK; last by rewrite ltnS leq_mul2l /=.
    by rewrite mod3E /= div3E // add1n addnS.
  have [/eqP iEa| iDa] := boolP (i == 0 :> nat).
    have -> : u2 (inord (3 * i).+1) = sa1.
      rewrite ffunE inordK; last by rewrite ltnS ltn_mul2l /=.
      rewrite mod3E /=.
      by rewrite iEa eqxx.
    have -> : u2 (inord (3 * i).+2) = ta1.
      rewrite ffunE inordK; last first.
        by rewrite -[_.+3](mulnDr 3 1) ltnW // add1n ltnS leq_mul2l /=.
      rewrite mod3E /=.
      by rewrite iEa eqxx.
    by rewrite iEa !addn0 // dua1uad1E /= -!addnA add2n !addnA addn0.
  have -> : u2 (inord (3 * i).+1) = si (a1 + i).
    rewrite ffunE inordK; last by rewrite ltnS ltn_mul2l /=.
    rewrite mod3E /= div3E.
    by rewrite [_.+1 == _.+1](eqn_mul2l 3 _ 0) /= (negPf iDa).
  have -> : u2 (inord (3 * i).+2) = ti (a1 + i).
    rewrite ffunE inordK; last first.
      by rewrite -[_.+3](mulnDr 3 1) ltnW // ltnS add1n leq_mul2l /=.
    rewrite mod3E /= div3E.
    by rewrite [_.+1 == _.+1](eqn_mul2l 3 _ 0) /= (negPf iDa).
  case: (sitiHb (a1 + i)) => // [|_ _ ->].
    rewrite -addn1 leq_add2l lt0n iDa /= -[l.+1](subnK (_ : a1 <= l.+1)).
      by rewrite addnC ltn_add2r.
    by rewrite ltnW.
  by rewrite /= -!addnA add2n addn0.
have P3 : 
     \sum_(a <= i < a1)  d[↓[u (inord i)], ↓[u (inord i.+1)]] <=
     \sum_(a <= i < a1)  d[u (inord i), u (inord i.+1)].
  apply: leq_sum => i _.
  by apply: gdist_cunlift; apply: shanoi_connect.
have SH : 2 <= l -> 
  (S_[l.+1] n.+2).*2  <= S_[l.+1] n.+2 + S_[l] n.+1 + (α_[1] n.+1).*2.
  move=> l_gt2.
  rewrite -addnn -!addnA leq_add2l alphaL1E.
  by apply: dsum_alphaL_alpha.
have [/andP[a_gt1 c_gt1]|] := boolP ((1 < a) && (1 < c)).
(* This is 4.2.1 *)
  have l_gt0 : 0 < l by rewrite -ltnS l1E (leq_trans c_gt1) // leq_addl.
  rewrite !sum_beta_S //= KH1 KH2 !eqxx !addn0. 
  pose u1l := [ffun i : 'I_(3 * a).-2.+1 => u1 (inord i)].
  have a3_gt1 : 1 < (3 * a).-2 by rewrite -(subnK a_gt1) addn2 !mulnS.
  have c3_gt1 : 1 < (3 * c).-2 by rewrite -(subnK c_gt1) addn2 !mulnS.
  have cH1 (k : 'I_(3 * a).-2.+1) : 
    0 < k < (3 * a).-2 -> codom (u1l k) \subset [:: p2; apeg k p1 p3].
    move=> /andP[k_gt0 k3L3a].
    have k3La1 : k %/ 3 <= a.-1.
      have kL3a : k <= 3 * (a.-1).
        rewrite -[a.-1]subn1 mulnBr -ltnS -[3 *1]/(2.+1) subnSK.
          by rewrite subn2.
        by rewrite (leq_mul2l 3 1).
      by rewrite -[a.-1](mulKn _ (_ : 0 < 3)) // leq_div2r.
    have k3Ll : k %/ 3 < l.
      rewrite -ltnS l1E (leq_trans (_ : _ < a.-1.+3)) //; last first.
        rewrite prednK // addnAC -addn2 (leq_trans (_ : _ <= a + c)) //.
          by rewrite leq_add2l.
        by rewrite leq_addr.
      by rewrite !ltnS ltnW // ltnS.
    rewrite !ffunE inordK //; last first.
      rewrite (leq_trans (ltn_ord _)) // -subn2 ltn_subLR.
        by rewrite add2n ltnS // ltnW.
      by rewrite (leq_trans (_ : _ < 3 * 1)) // leq_mul2l.
    rewrite {8}(divn_eq k 3) /apeg odd_add odd_mul andbT.
    case: eqP => [km3E0 /= |/eqP km3D0].
      have k3_gt0 : 0 < k %/ 3.
        case: (k: nat) k_gt0 km3E0  => // [] [|[|k1 _ _]] //.
        by rewrite (divnMDl 1 k1 (_ : 0 < 3)).
      rewrite km3E0 addbF -[if _ then _ else _]/(apeg (k %/ 3) p1 p3).
      have /H : 0 < (inord (k %/ 3) : 'I_l.+2) < l.+1.
        rewrite inordK //.
          by rewrite k3_gt0 /= (leq_trans k3Ll).
        by rewrite (leq_trans k3Ll) // ltnW.
      by rewrite ffunE inordK // (leq_trans k3Ll) // ltnW .
    case: eqP => [km3E1|/eqP km3D1].
      rewrite km3E1 addbT; case: eqP => [->|kE3a1].
        rewrite (_ : (3 * a.-1).+1 = a.-1 * 3 + 1); last by rewrite addn1 mulnC.
        rewrite divnMDl // divn_small // addn0.
        by apply: codom_subC; have := sam1C; rewrite /pa -[a]prednK.
      move: k3La1; rewrite leq_eqVlt => /orP[/eqP k3Ea1| k3La].
        case: kE3a1.
        by rewrite (divn_eq k 3) km3E1 k3Ea1 mulnC addn1.
      case: (sitiH (k %/ 3)) => // siH _ _; move: siH.
      by rewrite aMin1 // -{2}[a]prednK.
    have km3E2 : k %% 3 = 2.
      by case: (_ %% _) (ltn_mod k 3) km3D0 km3D1 => // [] [|[|]].
    rewrite km3E2 addbF; case: eqP => [kE3a1|kD3a1].
      rewrite ltnNge in k3L3a; case/negP: k3L3a.
      by rewrite kE3a1 -{1}[a]prednK // mulnS.
    move: k3La1; rewrite leq_eqVlt => /orP[/eqP k3Ea1| k3La].
      case: kD3a1.
      by rewrite (divn_eq k 3) km3E2 k3Ea1 mulnC addn2.
    apply: codom_subC.
    case: (sitiH (k %/ 3)) => // _ tiH _; move: tiH.
    by rewrite aMin1 // -{2}[a]prednK // ltnS ltnW.
    have {cH1}P4 : 
      (S_[(3 * a).-2] n.+1).*2 <=
      \sum_(i < (3 * a).-2)  d[u1 (inord i), u1 (inord i.+1)] +
      \sum_(k < n.+1) (↓[u ord0] k != p1) * beta n.+1 (3 * a).-2 k +
      \sum_(k < n.+1) (sam1 k != pa) * beta n.+1 (3 * a).-2 k.
    apply: leq_trans (IH _ _ _ _ _ _ _ cH1) _ => //.
    rewrite leq_eqVlt; apply/orP; left; apply/eqP.
    congr (_ + _ + _); apply: eq_bigr => i _.
    - by rewrite ![u1l _]ffunE !inordK // ltnS // ltnW.
    - by rewrite ffunE inord_eq0 // ffunE /= inord_eq0.
    rewrite !ffunE /= inordK //; last first.
      by rewrite ltnS -subn2 leq_subr.
    rewrite (_ : _.-2 = (3 * a.-1).+1); last first.
      by rewrite -{1}[a]prednK // mulnS.
    rewrite mod3E /= eqxx.
    by rewrite /pa /apeg /= odd_mul /= -subn1 odd_sub //; case: odd => /=.
  have {}P4 := leq_trans P4 (leq_add (leq_add (leqnn _) 
                     (leq_sum_beta _ _)) (leqnn _)).
  set x1S := \sum_(_ < _.+1) _ in P4; set x2S := \sum_(_ < _.+1) _ in P4.
  rewrite -/x1S.
  pose u2r := [ffun i : 'I_(3 * c).-2.+1 => u2 (inord i.+2)].
  pose pa1 := apeg a1 p1 p3.
  pose pa1S := apeg a1.+1 p1 p3.
  have cH1 (k : 'I_(3 * c).-2.+1) : 
    0 < k < (3 * c).-2 -> codom (u2r k) \subset [:: p2; apeg k pa1 pa1S].
    move=> /andP[k_gt0 k3L3a].
    have k2L3c : k.+2 < (3 * c).
      by have := k3L3a; rewrite -{2}subn2 ltn_subRL add2n.    
    rewrite !ffunE inordK ?ltnS 1?ltnW //.
    case: eqP => [km3E0 /= |/eqP km3D0].
      have k3_gt0 : 0 < k.+2 %/ 3.
        case: (k: nat) k_gt0 km3E0  => // [] //= k1 _ _.
        by rewrite (divnMDl 1 k1 (_ : 0 < 3)).
      have a1k3Ll1 : a1 + k.+2 %/ 3 < l.+1.
        move: k2L3c.
        rewrite {1}(divn_eq k.+2 3) km3E0 addn0 mulnC ltn_mul2l /= => k2L3c.
        rewrite -(subnK (_ : a1 <= l.+1)) ?(leq_trans a1Ll) //.
        by rewrite addnC ltn_add2r -/c.
      rewrite (_ : apeg _ _ _ = apeg (a1 + k.+2) p1 p3) ; last first.
        by rewrite /pa1 /pa1S /apeg /= odd_add /= negbK; do 2 case: odd.
      rewrite (_ : apeg _ _ _ = apeg (a1 + (k.+2) %/ 3) p1 p3) ; last first.
        rewrite /apeg odd_add {1}(divn_eq k.+2 3) !odd_add odd_mul andbT.
        by rewrite km3E0 addbF.
      have /H : 0 < (inord (a1 + k.+2 %/ 3) : 'I_l.+2) < l.+1.
        rewrite inordK; first by rewrite addn_gt0 a1_gt0.
        by rewrite ltnS ltnW.
      by rewrite ffunE inordK // ltnS ltnW.
    case: eqP => [km3E1|/eqP km3D1].
      rewrite eqn_leq ltnNge /=.
      have a1La1k : a1 < a1 + k.+2 %/3.
        by rewrite -{1}(addn0 a1) ltn_add2l divn_gt0.
      have a1k3Ll : a1 + k.+2 %/ 3 < l.+1.
        move: (ltnW k2L3c).
        rewrite {1}(divn_eq k.+2 3) km3E1 addn1 mulnC ltn_mul2l /=.
        rewrite -(subnK (_ : a1 <= l.+1)) ?(leq_trans a1Ll) //.
        by rewrite addnC ltn_add2r -/c.
      rewrite (_ : apeg _ _ _ = apeg (a1 + k.+2) p1 p3) ; last first.
        by rewrite /pa1 /pa1S /apeg /= odd_add /= negbK; do 2 case: odd.
      rewrite (_ : apeg _ _ _ = apeg (a1 + (k.+2) %/ 3).+1 p1 p3) ; last first.
        rewrite /apeg /= odd_add {1}(divn_eq k.+2 3) !odd_add odd_mul andbT.
        rewrite km3E1 addbT.
        by case: odd => /=.
      case: (sitiHb (a1 + k.+2 %/ 3)) => // [| siH _ _]; first by rewrite a1La1k.
      by move: siH; rewrite a1Max // ltnS ltnW.
    have km3E2 : k.+2 %% 3 = 2.
      by case: (_ %% _) (ltn_mod k.+2 3) km3D0 km3D1 => // [] [|[|]].
    rewrite ifN; last by case: (k : nat) k_gt0.
    have a1La1k : a1 < a1 + k.+2 %/3.
      by rewrite -{1}(addn0 a1) ltn_add2l divn_gt0.
    have a1k3Ll : a1 + k.+2 %/ 3 < l.+1.
      have: k.+2 %/ 3 * 3 < 3 * c.
        rewrite ltnW //.
        move: (ltnW k2L3c).
        by rewrite {1}(divn_eq k.+2 3) km3E2 addn2.
      rewrite mulnC ltn_mul2l /=.
      rewrite -(subnK (_ : a1 <= l.+1)) ?(leq_trans a1Ll) //.
      by rewrite addnC ltn_add2r -/c.
    rewrite (_ : apeg _ _ _ = apeg (a1 + k.+2) p1 p3) ; last first.
      by rewrite /pa1 /pa1S /apeg /= odd_add /= negbK; do 2 case: odd.
    rewrite (_ : apeg _ _ _ = apeg (a1 + (k.+2) %/ 3) p1 p3) ; last first.
      rewrite /apeg /= odd_add {1}(divn_eq k.+2 3) !odd_add odd_mul andbT.
      rewrite km3E2 addbF.
      by case: odd => /=.
    apply: codom_subC.
    case: (sitiHb (a1 + k.+2 %/ 3)) => // [| _ tiH _]; first by rewrite a1La1k.
    by move: tiH; rewrite a1Max // a1La1k ltnS ltnW.
  have P5 :
    (S_[(3 * c).-2] n.+1).*2 <=
    \sum_(i < (3 * c).-2)  d[u2 (inord i.+2), u2 (inord i.+3)] +
    \sum_(k < n.+1) (ta1 k != pa1) * beta n.+1 (3 * c).-2 k +
    \sum_(k < n.+1)
       ((cunliftr (u ord_max)) k != apeg l.+1 p1 p3) *
           beta n.+1 (3 * c).-2 k .
    apply: leq_trans (IH _ _ _ _ _ _ _ cH1) _; rewrite /pa1 /pa1S {cH1}//.
    - by rewrite /apeg /=; case: odd; rewrite // eq_sym.
    - by rewrite eq_sym.
    repeat apply: leq_add; rewrite leq_eqVlt; apply/orP; left; apply/eqP.
    - apply: eq_bigr => i _.
      by rewrite ![u2r _]ffunE !inordK // ltnS // ltnW.
    - apply: eq_bigr => i _; congr ((_ != _) * _).
      rewrite !ffunE /= !inordK //=.
      by rewrite (leq_trans (_ : 2 < (3 * 1).+1)) // ltnS leq_mul2l.
    apply: eq_bigr => i _; congr ((_ != _) * _).
      rewrite !ffunE /= !prednK ?muln_gt0 //=; last first.
        by rewrite -subn1 ltn_subRL addn0 (leq_trans (_ : _ < 3 * 1)) // 
                   leq_mul2l.
      rewrite inordK // mod3E /= div3E addnC subnK; last first.
        by apply: (leq_trans a1Ll).
      by rewrite ffunE; congr (u _ _ ); apply/val_eqP; rewrite /= inordK.
    rewrite /pa1 /pa1S -(subnK (_ : a1 <= l.+1)) // -/c.
      rewrite -subn2 /apeg odd_sub.
        by rewrite odd_mul /= odd_add; case: odd => //=.
      by rewrite (leq_trans (_ : _ < 3 * 1)) // leq_mul2l //.
    by rewrite ltnW.
  rewrite {cH1}//.
  have {}P5 := 
    leq_trans P5 (leq_add (leqnn _) (leq_sum_beta _ _)).
  set y1S := \sum_(_ < _.+1) _ * _.*2 in P5; set y2S := \sum_(_ < n.+1) _ in P5.
  rewrite -/y1S.
  have [b_gt1|b_le2] := leqP 2 b.
    pose u3 := [ffun i : 'I_3 =>
                 if i == 0 :> nat then sam1 
                 else if i == 1 :> nat then tam1 else ↓[u (inord a)]].
    have cH6 (k : 'I_3) : 
      0 < k < 2 -> codom (u3 k) \subset [:: p1; apeg k p2 p3].
      move=> /andP[k_gt0 k_lt2].
      rewrite !ffunE.
      by have ->/= : k = 1 :> nat by case: (k : nat) k_gt0 k_lt2 => // [] [|].
    have P6 : 
      (S_[2] n.+1).*2 <=
      (d[sam1, tam1] + d[tam1, ↓[u (inord a)]]) +
      \sum_(k < n.+1) (sam1 k != p2) * beta n.+1 2 k +
      \sum_(k < n.+1) (↓[u (inord a)] k != p2) * beta n.+1 2 k.
      apply: (leq_trans (IH _ _ _ _ _ _ _ cH6)) => //.
        by rewrite eq_sym.
      repeat apply: leq_add; rewrite leq_eqVlt; apply/orP; left; apply/eqP.
      - by rewrite !big_ord_recr big_ord0 !ffunE !inordK /=.
      - by apply: eq_bigr => i _; rewrite !ffunE.
      by apply: eq_bigr => i _; rewrite !ffunE.
    rewrite {cH6}// in P6.
    set x3S := \sum_(_ < _) _ in P6; set y3S := \sum_(_ < _) _ in P6.
    have x2Sx3SE : x2S + x3S <= (S_[1] n).*2 + α_[maxn (3 * a).-2 2] n.
      apply: sum_alpha_diffE; by rewrite // /pa.
    rewrite (maxn_idPl _) // in x2Sx3SE.
    pose u4 := [ffun i : 'I_b.+1 => ↓[u (inord (a + i))]].
    pose paS := apeg a.+1 p1 p3.
    have cH7 (k : 'I_b.+1) : 
      0 < k < b -> codom (u4 k) \subset [:: p2; apeg k pa paS].
      move=> /andP[k_gt0 k_ltb].
      have akLl : a + k < l.+1.
        rewrite  ltnS (leq_trans _ a1Ll) //.
        by rewrite -(subnK aLa1) addnC leq_add2r ltnW.
      rewrite !ffunE.
      have /H : 0 < (inord (a + k) : 'I_l.+2) < l.+1.
        rewrite inordK; first by rewrite addn_gt0 a_gt0.
        by rewrite ltnS ltnW.
      rewrite ffunE inordK //; last by rewrite ltnS ltnW.
      by rewrite /pa /paS /apeg odd_add /=; do 2 case: odd. 
    have P7 : 
      (S_[b] n.+1).*2 <=
      \sum_(i < b)  d[↓[u (inord (a + i))], ↓[u (inord (a + i).+1)]] +
      \sum_(k < n.+1) (↓[u (inord a)] k != pa) * beta n.+1 b k +
      \sum_(k < n.+1) (↓[u (inord a1)] k != apeg a1 p1 p3) * beta n.+1 b k.
      apply: leq_trans (IH _ _ _ _ _ _ _ cH7) (leq_add (leq_add _ _) _);
        rewrite /pa /paS // 1?eq_sym //.
      - by rewrite /apeg /=; case: odd; rewrite // eq_sym.
      - apply: leq_sum => i; rewrite !ffunE !inordK ?addnS //.
          by rewrite ltnS.
        by rewrite ltnS ltnW.
      - by apply: leq_sum => i _; rewrite !ffunE addn0.
      apply: leq_sum => i _; rewrite !ffunE /= [a + b]addnC subnK //.
      by rewrite /b /apeg odd_sub //=; do 2 case: odd.
    set x4S := \sum_(_ < n.+1) _ * _ in P7; set y4S := \sum_(_ < n.+1) _ in P7.
    have y3Sx4SE : y3S + x4S <= (S_[1] n).*2 + α_[maxn 2 b] n.
      apply: sum_alpha_diffE => //; first by rewrite /pa eq_sym.
      apply: codom_liftr.
      have := @cH (inord a); rewrite inordK //; apply.
      by rewrite a_gt0 /= ltnS (leq_trans _ a1Ll).
    rewrite (maxn_idPr _) // in y3Sx4SE.
    pose u5 := [ffun i : 'I_3 =>
                     if i == 0 :> nat then ↓[u (inord a1)]
                 else if i == 1 :> nat then sa1 else ta1].
    have cH8 (k : 'I_3) : 
      0 < k < 2 -> codom (u5 k) \subset [:: p1; apeg k p2 p3].
      move=> /andP[k_gt0 k_lt2].
      rewrite !ffunE.
      by have ->/= : k = 1 :> nat by case: (k : nat) k_gt0 k_lt2 => // [] [|].
    have P8 : 
      (S_[2] n.+1).*2 <=
      (d[↓[u (inord a1)], sa1] + d[sa1, ta1]) +
      \sum_(k < n.+1) (↓[u (inord a1)] k != p2) * beta n.+1 2 k +
      \sum_(k < n.+1) (ta1 k != p2) * beta n.+1 2 k.
      apply: (leq_trans (IH _ _ _ _ _ _ _ cH8)) => //.
        by rewrite eq_sym.
      repeat apply: leq_add; rewrite leq_eqVlt; apply/orP; left; apply/eqP.
      - by rewrite !big_ord_recr big_ord0 !ffunE !inordK /=.
      - by apply: eq_bigr => i _; rewrite !ffunE.
      by apply: eq_bigr => i _; rewrite !ffunE.
    set x5S := \sum_(_ < _) _ in P8; set y5S := \sum_(_ < _) _ in P8.
    have y4Sx5SE : y4S + x5S <= (S_[1] n).*2 + α_[maxn b 2] n.
      apply: sum_alpha_diffE => //.
      apply/codom_liftr/codom_subC.
      have := @cH (inord a1); rewrite inordK //.
        by apply; rewrite a1_gt0 /= ltnS.
      by rewrite ltnS ltnW.
    rewrite (maxn_idPl _) // in y4Sx5SE.
    have y2Sy5SE : y2S + y5S <= (S_[1] n).*2 + α_[maxn (3 * c).-2 2] n.
      apply: sum_alpha_diffE => //; first by rewrite /pa1.
      by apply: codom_subC.
    rewrite (maxn_idPl _) // in y2Sy5SE.
    rewrite [\sum_(_ < _) _](_ : _ = 
       \sum_(i < a)  d[u (inord i), u (inord i.+1)] +
       \sum_(a <= i < a1)  d[u (inord i), u (inord i.+1)] +
       \sum_(a1 <= i < l.+1)  d[u (inord i), u (inord i.+1)]); last first.
      pose f i := d[u (inord i), u (inord i.+1)].
      rewrite -!(big_mkord xpredT f).
      by rewrite -!big_cat_nat //= ltnW.
    rewrite -{}P1 -{}P2.
    rewrite [X in _ <= _ + X + _ + _ + _ + _]
       (_ : _  =
              \sum_(i < (3 * a).-2) d[u1 (inord i), u1 (inord i.+1)]
              + d[sam1, tam1] +  d[tam1, ↓[u (inord a)]]); last first.
      pose f i := d[u1 (inord i), u1 (inord i.+1)].
      rewrite -!(big_mkord xpredT f) .
      rewrite -{1}(subnK (_ : 1 < 3 * a)) //; last first.
        by rewrite -[a]prednK // mulnS.
      rewrite subn2 !addn2 !big_nat_recr /f //=; congr (_ + _ + _).
        rewrite ffunE (_ : (3 * a).-2 = (3 * (a.-1)).+1); last first.
          by rewrite -{1}[a]prednK // mulnS.
        rewrite inordK; last by rewrite ltnS ltn_mul2l /= prednK.
        rewrite mod3E /= eqxx.
        rewrite ffunE inordK; last first.
          by rewrite -[_.+3](mulnDr 3 1) add1n prednK // ltnW.
        by rewrite mod3E /= eqxx.
      rewrite ffunE (_ : (3 * a).-2 = (3 * (a.-1)).+1); last first.
        by rewrite -{1}[a]prednK // mulnS.
      rewrite inordK; last first.
        by rewrite -{2}[a]prednK // mulnS.
      rewrite mod3E /= eqxx.
      rewrite ffunE inordK; last first.
        by rewrite -{2}[a]prednK // mulnS.
      by rewrite -[(_ * _).+3](mulnDr 3 1) mod3E /= div3E add1n prednK.
    rewrite [X in _ <= _ + (_ + X) + _ + _]
       (_ : _  = d[↓[u (inord a1)], sa1] +  d[sa1, ta1] +
         \sum_(i < (3 * c).-2) d[u2 (inord i.+2), u2 (inord i.+3)]); last first.
      pose f i := d[u2 (inord i), u2 (inord i.+1)].
      rewrite -!(big_mkord xpredT f) .
      rewrite -{1}(subnK (_ : 1 < 3 * c)) //; last first.
        by rewrite -[c]prednK // mulnS.
      rewrite subn2 !addn2 !big_nat_recl // /f /= !addnA; congr (_ + _ + _).
      - rewrite !ffunE !inordK ?addn0 //=.
        by rewrite ltnS muln_gt0.
      - rewrite !ffunE !inordK //=.
          by rewrite ltnW // ltnS (leq_mul2l 3 1 c).
        by rewrite ltnS muln_gt0.
      by rewrite big_mkord.
    set z1S := \sum_(_ < _) _; set z2S := \sum_(_ < _) _.
    set z3S := \sum_(_ <= _ < _) _. 
    rewrite -/z1S in P4; rewrite -/z2S in P5; rewrite -/z3S in P3.
    rewrite -[z1S + _ + _]addnA; set d1 := d[_,_] + d[_,_]; rewrite -/d1 in P6.
    set d2 := d[_,_] + d[_,_]; rewrite -/d2 in P8.
    set xS := \sum_(_ <= _ < _) _ in P3.
    rewrite [X in _ <= X + _ + _](_ : _ = xS) in P7; last first.
      rewrite /xS -[in RHS](add0n a) big_addn -/b big_mkord.
      by apply: eq_bigr => i _; rewrite [a + _]addnC.
    have F1 := dsum_alphaL_S (3 * a).-2 n.
    have F2 := dsum_alphaL_S (3 * c).-2 n.
    have F3 := dsum_alphaL_S b n.
    have F4_a : a.*2 = 2 + a.-1 + a.-1.
      by rewrite -{1}[a]prednK // -addnn addnS.
    have F4_c : c.*2 = 2 + c.-1 + c.-1.
      by rewrite -{1}[c]prednK // -addnn addnS.
    have F4 i k : 0 < i -> S_[i.-1] k.+1 <= S_[(3 *i).-2] k + i.-1.
      move=> i_gt0; apply: leq_trans (dsum_alpha3l _ _) _.
      rewrite leq_add2r.
      apply: (increasingE (increasing_dsum_alphaL_l _)).
      by rewrite -{2}[i]prednK // mulnS addSn add2n /=.
    have F4an := F4 a n a_gt0.
    have F4an1 := F4 a n.+1 a_gt0.
    have F4cn := F4 c n (c_gt0).
    have F4cn1 := F4 c n.+1 (c_gt0).
    have l_gt1 : 1 < l.
      by rewrite -ltnS l1E -[3]/(2 + 0 + 1); rewrite !leq_add.
    have F5 := SH l_gt1.
    have F6 : S_[l.+1] n.+2 + S_[1] n.+2 <= S_[a.-1] n.+2 + S_[(b + c).+2] n.+2.
      rewrite [X in _ <= X]addnC.
      rewrite (_ : l.+1 =  1 + a.-2 + (b + c).+1); last first.
        rewrite /b /c add1n -addSnnS !prednK //; last by rewrite -ltnS prednK.
        by rewrite addnCA addnA subnK // addnC subnK // ltnW.
      rewrite (_ : a.-1 = 1 + a.-2); last first.
         by rewrite add1n prednK // -ltnS prednK.
      by apply: concaveEk1 (concave_dsum_alphaL_l n.+2).
    have F7 : S_[l] n.+1 + S_[1] n.+1 <= S_[a.-1] n.+1 + S_[(b + c).+1] n.+1.
      rewrite [X in _ <= X]addnC.
      rewrite (_ : l =  1 + a.-2 + (b + c)); last first.
        rewrite /b /c subSn // addnS -addSnnS add1n.
        rewrite !prednK //; last by rewrite -ltnS prednK.
        by rewrite addnCA addnA subnK // addnC subnK // ltnW.
      rewrite (_ : a.-1 = 1 + a.-2); last first.
         by rewrite add1n prednK // -ltnS prednK.
      by apply: concaveEk1 (concave_dsum_alphaL_l n.+1).
    have F8 : S_[(b + c).+2] n.+2 + S_[1] n.+2 <= S_[c.-1] n.+2 + S_[b.+4] n.+2.
      rewrite (_ : (b + c).+2 =  1 + b.+3 + (c.-2)); last first.
        by rewrite add1n 2!addSnnS !prednK // -subn1 ltn_subRL addn0.
      rewrite (_ : c.-1 = 1 + c.-2); last first.
        by rewrite add1n prednK // -ltnS prednK.
      by apply: concaveEk1 (concave_dsum_alphaL_l n.+2).
    have F9 : S_[(b + c).+1] n.+1 + S_[1] n.+1 <= S_[c.-1] n.+1 + S_[b.+3] n.+1.
      rewrite (_ : (b + c).+1 =  1 + b.+2 + (c.-2)); last first.
        by rewrite add1n 2!addSnnS !prednK // -subn1 ltn_subRL addn0.
      rewrite (_ : c.-1 = 1 + c.-2); last first.
        by rewrite add1n prednK // -ltnS prednK.
      by apply: concaveEk1 (concave_dsum_alphaL_l n.+1).
    have F10 : S_[b.+4] n.+2 <= S_[b.+3] n.+1 + (α_[1] n.+1).*2.
      by rewrite alphaL1E; apply: dsum_alphaL_alpha.
    have F11 : S_[b.+3] n.+1 <= S_[b.+2] n + (α_[1] n).*2.
      by rewrite alphaL1E; apply: dsum_alphaL_alpha.
    have F12 : S_[b.+2] n + S_[1] n <= S_[b] n + S_[3] n.
      rewrite (_ : b.+2 = 1 + 2 + b.-1); last first.
        by rewrite add1n addSnnS prednK // ltnW.
      rewrite -{2}[b]prednK; last by apply: ltnW.
      by apply: concaveEk1 (concave_dsum_alphaL_l n).
    have F13 : S_[1] n.+1 = (S_[3] n).+1 by rewrite dsum_alpha3_S.
    have F14 := leq_dsum_alpha_2l_1 n.+1.
    have F15n := dsum_alphaL_S 1 n.+1.
    have F15n1 := dsum_alphaL_S 1 n.
    (* lia should work *)
    move: P3 P4 P5 P6 P7 P8 => P3 P4 P5 P6 P7 P8.
    rewrite [X in _ <= X](_ : _ = 
      a.*2 + (z1S + d1) + (c.*2 + (d2 + z2S)) + x1S + y1S + z3S); last by ring.
    apply: leq_trans (leq_add (leqnn _) P3); rewrite {P3}//.
    rewrite -(leq_add2r x2S).
    rewrite [X in _ <= X](_ : _ = 
      a.*2 + d1 + (c.*2 + (d2 + z2S)) + y1S + xS + (z1S + x1S + x2S));
      last by ring.
    apply: leq_trans (leq_add (leqnn _) P4); rewrite {P4}//.
    rewrite -(leq_add2r y2S).
    rewrite [X in _ <= X](_ : _ = 
      a.*2 + d1 + (c.*2 + d2) + xS + (S_[(3 * a).-2] n.+1).*2 +
      (z2S + y2S + y1S)); last by ring.
    apply: leq_trans (leq_add (leqnn _) P5); rewrite {P5}//.
    rewrite -(leq_add2r (x3S + y3S)).
    rewrite [X in _ <= X](_ : _ = 
       a.*2 + (c.*2 + d2) + xS + (S_[(3 * a).-2] n.+1).*2 +
      (S_[(3 * c).-2] n.+1).*2 + (d1 + x3S + y3S)); last by ring.
    apply: leq_trans (leq_add (leqnn _) P6); rewrite {P6}//.
    rewrite -(leq_add2r (x4S + y4S)).
    rewrite [X in _ <= X](_ : _ = 
      a.*2 + c.*2 + d2 + (S_[(3 * a).-2] n.+1).*2 + (S_[(3 * c).-2] n.+1).*2 +
     (S_[2] n.+1).*2 + (xS + x4S + y4S)); last by ring. 
    apply: leq_trans (leq_add (leqnn _) P7); rewrite {P7}//.
    rewrite -(leq_add2r (x5S + y5S)).
    rewrite [X in _ <= X](_ : _ = 
      a.*2 + c.*2 + (S_[(3 * a).-2] n.+1).*2 + (S_[(3 * c).-2] n.+1).*2 +
      (S_[2] n.+1).*2 + (S_[b] n.+1).*2 + (d2 + x5S + y5S)); 
        last ring.
    apply: leq_trans (leq_add (leqnn _) P8); rewrite {P8}//.
    rewrite [X in X <= _](_ : _ =  
      (S_[l.+1] n.+2).*2 + (x2S + x3S) + (y2S + y5S) + 
      (y3S + x4S) + (y4S + x5S)); last by ring.
    apply: leq_trans (leq_add (leqnn _) y4Sx5SE) _.
    rewrite addnC {y4Sx5SE}addnA.
    apply: leq_trans (leq_add (leqnn _) y3Sx4SE) _.
    rewrite addnC 2!{y3Sx4SE}addnA.
    apply: leq_trans (leq_add (leqnn _) y2Sy5SE) _.
    rewrite addnC 2!{y2Sy5SE}addnA.
    apply: leq_trans (leq_add (leqnn _) x2Sx3SE) _.
    rewrite addnC 2!{x2Sx3SE}addnA.
    rewrite -[(S_[_.-2] _).*2]addnn {1}F1.
    rewrite -[(S_[_.-2] _).*2]addnn {1}F2.
    rewrite F3.
    rewrite [X in _ <= X](_ : _ =
      a.*2 + c.*2 + (S_[(3 * a).-2] n + S_[(3 * a).-2] n.+1) +
      (S_[(3 * c).-2] n  + S_[(3 * c).-2] n.+1) + 
      (S_[2] n.+1).*2 + (S_[b] n).*2 + (S_[2] n.+1).*2 +
       α_[(3 * c).-2] n + α_[b] n + α_[b] n + α_[(3 * a).-2] n);
       last by rewrite -!mul2n; ring.
    rewrite [X in X <= _](_ : _ =
      (S_[1] n).*2 + (S_[1] n).*2 +
      (S_[1] n).*2 + (S_[1] n).*2 + (S_[l.+1] n.+2).*2 +
      α_[(3 * c).-2] n + α_[b] n + α_[b] n + α_[(3 * a).-2] n); last by ring.
    rewrite !leq_add2r.
    rewrite  F4_a F4_c.
    rewrite [X in _ <= X](_ : _ =
      4 + a.-1 + c.-1 + c.-1 + (S_[(3 * a).-2] n.+1) +
     (S_[(3 * c).-2] n + S_[(3 * c).-2] n.+1) + (S_[2] n.+1).*2 + 
     (S_[b] n).*2 + (S_[2] n.+1).*2 +  (S_[(3 * a).-2] n + a.-1));last by ring.
    apply: leq_trans (leq_add (leqnn _) F4an).
    rewrite [X in _ <= X](_ : _ =
       4 + c.-1 + c.-1 + 
      (S_[(3 * c).-2] n + S_[(3 * c).-2] n.+1) + (S_[2] n.+1).*2 + 
      (S_[b] n).*2 + (S_[2] n.+1).*2 + S_[a.-1] n.+1 +
      (S_[(3 * a).-2] n.+1 + a.-1)); last by ring. 
    apply: leq_trans (leq_add (leqnn _) F4an1).
    rewrite [X in _ <= X](_ : _ =
       4 + c.-1 + (S_[(3 * c).-2] n.+1) + (S_[2] n.+1).*2 +
       (S_[b] n).*2 + (S_[2] n.+1).*2 + S_[a.-1] n.+1 + S_[a.-1] n.+2
        + (S_[(3 * c).-2] n + c.-1)); last by ring.
    apply: leq_trans (leq_add (leqnn _) F4cn).
    rewrite [X in _ <= X](_ : _ =
       4 +  (S_[2] n.+1).*2 + (S_[b] n).*2 +
      (S_[2] n.+1).*2 + S_[a.-1] n.+1 + S_[a.-1] n.+2 + S_[c.-1] n.+1 +
       (S_[(3 * c).-2] n.+1 + c.-1)); last by ring.
    apply: leq_trans (leq_add (leqnn _) F4cn1).
    rewrite {F1 F2 F3 F4 F4_a F4_c F4an F4an1 F4cn F4cn1}//.
    rewrite [X in X <= _](_ : _ =
         (8 * S_[1] n) + (S_[l.+1] n.+2).*2); last by rewrite -!muln2; ring. 
    apply: leq_trans (leq_add (leqnn _) F5) _.
    rewrite -(leq_add2r (S_[1] n.+2)).
    rewrite [X in X <= _](_ : _ =
      8 * S_[1] n + (S_[l] n.+1 + (α_[1] n.+1).*2) +
       (S_[l.+1] n.+2 + S_[1] n.+2)); last by ring.
    apply: leq_trans (leq_add (leqnn _) F6) _.
    rewrite -(leq_add2r (S_[1] n.+1)).
    rewrite [X in X <= _](_ : _ =
      8 * S_[1] n + ((α_[1] n.+1).*2) +
     (S_[a.-1] n.+2 + S_[(b + c).+2] n.+2) + (S_[l] n.+1 + S_[1] n.+1)); 
       last by ring.
    apply: leq_trans (leq_add (leqnn _) F7) _.
    rewrite {F5 F6 F7}//.
    rewrite -(leq_add2r (S_[1] n.+2)).
    rewrite [X in X <= _](_ : _ =
      8 * S_[1] n + (α_[1] n.+1).*2 + (S_[a.-1] n.+2) +
      S_[a.-1] n.+1 + S_[(b + c).+1] n.+1 + 
      ( S_[(b + c).+2] n.+2 + S_[1] n.+2)); last by ring.
    apply: leq_trans (leq_add (leqnn _) F8) _.
    rewrite -(leq_add2r (S_[1] n.+1)).
    rewrite [X in X <= _](_ : _ =
      8 * S_[1] n + (α_[1] n.+1).*2 + S_[a.-1] n.+2 + S_[a.-1] n.+1 +
       (S_[c.-1] n.+2 + S_[b.+4] n.+2) + 
      (S_[(b + c).+1] n.+1 + S_[1] n.+1)); last by ring.
    apply: leq_trans (leq_add (leqnn _) F9) _.
    rewrite {F8 F9}//.
    rewrite [X in X <= _](_ : _ =
      8 * S_[1] n + (α_[1] n.+1).*2 +  S_[b.+4] n.+2 + S_[b.+3] n.+1 +
      (S_[a.-1] n.+2 + S_[a.-1] n.+1 + S_[c.-1] n.+2 + S_[c.-1] n.+1));
      last by ring.
    rewrite [X in _ <= X](_ : _ =
      4 + (S_[2] n.+1).*2 + (S_[b] n).*2 + (S_[2] n.+1).*2 + S_[1] n.+2 + 
      S_[1] n.+1 + S_[1] n.+2 + S_[1] n.+1 +
      (S_[a.-1] n.+2 + S_[a.-1] n.+1 + S_[c.-1] n.+2 + S_[c.-1] n.+1));
      last ring.
    rewrite !leq_add2r.
    rewrite [X in X <= _](_ : _ =
      8 * S_[1] n + (α_[1] n.+1).*2 + S_[b.+3] n.+1 +
     S_[b.+4] n.+2); last by ring.
    apply: leq_trans (leq_add (leqnn _) F10) _.
    rewrite [X in X <= _](_ : _ =
      8 * S_[1] n + (α_[1] n.+1).*2 + S_[b.+3] n.+1 + (α_[1] n.+1).*2 +
      S_[b.+3] n.+1); last by ring.
    rewrite [X in X <= _](_ : _ =
      (4 * S_[1] n + (α_[1] n.+1).*2 + S_[b.+3] n.+1).*2);
       last by rewrite -!mul2n; ring.
    rewrite [X in _ <= X](_ : _ =
      (2 + S_[2] n.+1 + S_[b] n + S_[2] n.+1 + S_[1] n.+2 +
      S_[1] n.+1).*2); last by rewrite -!mul2n; ring.
    rewrite leq_double.
    apply: leq_trans (leq_add (leqnn _) F11) _.
    rewrite [X in X <= _](_ : _ =
      3 * S_[1] n + (α_[1] n.+1).*2 + (α_[1] n).*2
      + (S_[b.+2] n +  S_[1] n)); last by ring.
    apply: leq_trans (leq_add (leqnn _) F12) _.
    rewrite {F10 F11 F12}F13 -[(S_[_] _).+1]add1n !addnA leq_add2r.
    rewrite [X in _ <= X](_ : _ = 
      2 + S_[1] n.+2 + (S_[2] n.+1).*2.+1 + S_[b] n); last first.
      by rewrite -mul2n; ring.
    rewrite leq_add2r.
    apply: leq_trans _ (leq_add (leqnn _) F14).
    rewrite {F14}F15n F15n1.
    rewrite [X in _ <= X](_ : _ = 
      2 + α_[1] n + 3 * S_[1] n + (α_[1] n.+1).*2 + (α_[1] n).*2);
        last by rewrite -!mul2n; ring.
    by rewrite !leq_add2r leq_addl.
  move: b_le2; rewrite leq_eqVlt => /orP[/eqP[] bE1|].
    have a1E : a1 = a.+1 by rewrite -(subnK aLa1) -/b bE1.
    pose u3 := [ffun i : 'I_4 =>
                 if i == 0 :> nat then sam1 
                 else if i == 1 :> nat then tam1 
                 else if i == 2 :> nat then ↓[u (inord a)]
                 else ↓[u (inord a.+1)]].
    have cH6 (k : 'I_4) : 
      0 < k < 3 -> codom (u3 k) \subset [:: pa1S; apeg k p2 pa1].
      move=> /andP[k_gt0 k_lt3].
      rewrite !ffunE eqn_leq leqNgt k_gt0 /=.
      case: eqP => [->/=|/eqP kD1].
        rewrite /pa1 /pa1S /apeg /=; case: odd => //=.
        by apply: codom_subC.
      have ->/= : k = 2 :> nat.
        by apply/eqP; rewrite eqn_leq -ltnS k_lt3 ltn_neqAle eq_sym k_gt0 kD1.
      apply/codom_liftr/codom_subC.
      have /cH : 0 < (inord a : 'I_l.+2) < l.+1.
        rewrite inordK //.
        by rewrite a_gt0 /= l1E bE1 addn1 leq_addr.
      by rewrite inordK // /pa1S a1E /apeg /= negbK.
    have P6 : 
      (S_[3] n.+1).*2 <=
      (d[sam1, tam1] + d[tam1, ↓[u (inord a)]] + 
          d[↓[u (inord a)], ↓[u (inord a.+1)]]) +
      \sum_(k < n.+1) (sam1 k != p2) * beta n.+1 3 k +
      \sum_(k < n.+1) (↓[u (inord a.+1)] k != (apeg a1 p1 p3)) * beta n.+1 3 k.
      apply: (leq_trans (IH _ _ _ _ _ _ _ cH6)); rewrite /pa1S /pa1 //.
      - by rewrite eq_sym.
      - by rewrite eq_sym.
      - by rewrite /apeg /=; case: odd => //=; rewrite eq_sym.
      repeat apply: leq_add; rewrite leq_eqVlt; apply/orP; left; apply/eqP.
      - by rewrite !big_ord_recr big_ord0 !ffunE !inordK /=.
      - by apply: eq_bigr => i _; rewrite !ffunE /=.
      by apply: eq_bigr => i _; rewrite !ffunE.
    set x3S := \sum_(_ < _) _ in P6; set y3S := \sum_(_ < _) _ in P6.
    have x2Sx3SE : x2S + x3S <= (S_[1] n).*2 + α_[maxn (3 * a).-2 3] n.
      by apply: sum_alpha_diffE; rewrite /pa.
    rewrite (maxn_idPl _) in x2Sx3SE; last first.
      by rewrite -subn2  ltn_subRL ltnW // (leq_mul2l 3 2).
    pose u5 := [ffun i : 'I_3 =>
                     if i == 0 :> nat then ↓[u (inord a1)]
                 else if i == 1 :> nat then sa1 else ta1].
    have cH8 (k : 'I_3) : 
      0 < k < 2 -> codom (u5 k) \subset [:: p1; apeg k p2 p3].
      move=> /andP[k_gt0 k_lt2].
      rewrite !ffunE.
      by have ->/= : k = 1 :> nat by case: (k : nat) k_gt0 k_lt2 => // [] [|].
    have P8 : 
      (S_[2] n.+1).*2 <=
      (d[↓[u (inord a.+1)], sa1] + d[sa1, ta1]) +
      \sum_(k < n.+1) (↓[u (inord a.+1)] k != p2) * beta n.+1 2 k +
      \sum_(k < n.+1) (ta1 k != p2) * beta n.+1 2 k.
      apply: (leq_trans (IH _ _ _ _ _ _ _ cH8)) => //.
        by rewrite eq_sym.
      repeat apply: leq_add; rewrite leq_eqVlt; apply/orP; left; apply/eqP.
      - by rewrite !big_ord_recr big_ord0 !ffunE !inordK //= a1E.
      - by apply: eq_bigr => i _; rewrite !ffunE a1E.
      by apply: eq_bigr => i _; rewrite !ffunE.
    set x5S := \sum_(_ < n.+1) _ in P8; set y5S := \sum_(_ < n.+1) _ in P8.
    have y3Sx5SE : y3S + x5S <= (S_[1] n).*2 + α_[3] n.
      apply: sum_alpha_diffE => //.
      apply/codom_liftr/codom_subC.
      have := @cH (inord a.+1); rewrite inordK ?a1E //.
        by apply; rewrite andTb //= ltnS -a1E.
      by rewrite -a1E ltnS ltnW.
    have y5Sy2SE : y5S + y2S <= (S_[1] n).*2 + α_[maxn 2 (3 * c).-2] n.
      by apply: sum_alpha_diffE; rewrite // /pa1 eq_sym.
    rewrite (maxn_idPr _) in y5Sy2SE; last first.
      by rewrite -subn2 ltn_subRL (ltn_mul2l 3 1).
    rewrite [\sum_(_ < _) _](_ : _ = 
       \sum_(i < a)  d[u (inord i), u (inord i.+1)] +
       \sum_(a <= i < a1)  d[u (inord i), u (inord i.+1)] +
       \sum_(a1 <= i < l.+1)  d[u (inord i), u (inord i.+1)]); last first.
      pose f i := d[u (inord i), u (inord i.+1)].
      rewrite -!(big_mkord xpredT f).
      by rewrite -!big_cat_nat //= ltnW.
    rewrite -{}P1 -{}P2.
    apply: leq_trans 
       (leq_add (leq_add (leq_add (leq_add (leqnn _) P3) (leqnn _))
         (leqnn _)) (leqnn _)).
    rewrite {P3}//.
    rewrite [X in _ <= _ + X + _ + _ + _ + _]
       (_ : _  =
              \sum_(i < (3 * a).-2) d[u1 (inord i), u1 (inord i.+1)]
              + d[sam1, tam1] +  d[tam1, ↓[u (inord a)]]); last first.
      pose f i := d[u1 (inord i), u1 (inord i.+1)].
      rewrite -!(big_mkord xpredT f) .
      rewrite -{1}(subnK (_ : 1 < 3 * a)) //; last first.
        by rewrite -[a]prednK // mulnS.
      rewrite subn2 !addn2 !big_nat_recr /f //=; congr (_ + _ + _).
        rewrite ffunE (_ : (3 * a).-2 = (3 * (a.-1)).+1); last first.
          by rewrite -{1}[a]prednK // mulnS.
        rewrite inordK; last by rewrite ltnS ltn_mul2l /= prednK.
        rewrite mod3E /= eqxx.
        rewrite ffunE inordK; last first.
          by rewrite -[_.+3](mulnDr 3 1) add1n prednK // ltnW.
        by rewrite mod3E /= eqxx.
      rewrite ffunE (_ : (3 * a).-2 = (3 * (a.-1)).+1); last first.
        by rewrite -{1}[a]prednK // mulnS.
      rewrite inordK; last first.
        by rewrite -{2}[a]prednK // mulnS.
      rewrite mod3E /= eqxx.
      rewrite ffunE inordK; last first.
        by rewrite -{2}[a]prednK // mulnS.
      by rewrite -[(_ * _).+3](mulnDr 3 1) mod3E /= div3E add1n prednK.
    rewrite [X in _ <= _ + (_ + X) + _ + _](_ : _  = 
       d[↓[u (inord a1)], sa1] +  d[sa1, ta1] +
               \sum_(i < (3 * c).-2) 
                  d[u2 (inord i.+2), u2 (inord i.+3)]); last first.
      pose f i := d[u2 (inord i), u2 (inord i.+1)].
      rewrite -!(big_mkord xpredT f) .
      rewrite -{1}(subnK (_ : 1 < 3 * c)) //; last first.
        by rewrite -[c]prednK // mulnS.
      rewrite subn2 !addn2 !big_nat_recl // /f /= !addnA; congr (_ + _ + _).
      - rewrite !ffunE !inordK ?addn0 //=.
        by rewrite ltnS muln_gt0.
      - rewrite !ffunE !inordK //=.
          by rewrite ltnW // ltnS (leq_mul2l 3 1 c).
        by rewrite ltnS muln_gt0.
      by rewrite big_mkord.
    rewrite [X in _ <= _ + X + _ +  _ + _](_ : _ =
      d[↓[u (inord a)], ↓[u (inord a.+1)]]); last first.
      by rewrite a1E big_nat1.  
    set z1S := \sum_(_ < _) _; set z2S := \sum_(_ < _) _.
    rewrite -[a.*2 + _ + _]addnA; rewrite -![in X in a.*2 + X]addnA.
    rewrite -[a.*2 + _ + _]addnA.
    rewrite ![in X in a.*2 + (_ + X + _) + _ + _]addnA.
    rewrite -/z1S in P4; rewrite -/z2S in P5.
    set d1 := d[_,_] + d[_,_] + d[_,_]; rewrite -/d1 in P6.
    set d2 := d[_,_] + d[_,_]; rewrite -a1E -/d2 in P8.
    have F1 := dsum_alphaL_S (3 * a).-2 n.
    have F2 := dsum_alphaL_S (3 * c).-2 n.
    have F3 := dsum_alphaL_S 3 n.
    have F4_a : a.*2 = 2 + a.-1 + a.-1.
      by rewrite -{1}[a]prednK // -addnn addnS.
    have F4_c : c.*2 = 2 + c.-1 + c.-1.
      by rewrite -{1}[c]prednK // -addnn addnS.
    have F4 i k : 0 < i -> S_[i.-1] k.+1 <= S_[(3 *i).-2] k + i.-1.
      move=> i_gt0; apply: leq_trans (dsum_alpha3l _ _) _.
      rewrite leq_add2r.
      apply: (increasingE (increasing_dsum_alphaL_l _)).
      by rewrite -{2}[i]prednK // mulnS addSn add2n /=.
    have F4an := F4 a n a_gt0.
    have F4an1 := F4 a n.+1 a_gt0.
    have F4cn := F4 c n (c_gt0).
    have F4cn1 := F4 c n.+1 (c_gt0).
    have l_gt1 : 1 < l.
      by rewrite -ltnS l1E -[3]/(2 + 0 + 1); rewrite !leq_add.
    have F5 := SH l_gt1.
    have F6n : S_[1] n.+1 = (S_[3] n).+1 by rewrite dsum_alpha3_S.
    have F6n1 : S_[1] n.+2 = (S_[3] n.+1).+1 by rewrite dsum_alpha3_S.
    have am1_gt0 : 0 < a.-1 by rewrite -subn1 ltn_subRL addn0.
    have F7n1 : S_[1] n.+2 + S_[l.+1] n.+2 <= S_[a.-1] n.+2 + S_[c.+3] n.+2.
      rewrite addnC (_ : l.+1 = 1 + c.+2 + a.-2); last first.
        by rewrite /c a1E add1n !addSnnS !prednK ?subnK // -a1E ltnW.
      rewrite {2}(_ : a.-1 = 1 + a.-2); last by rewrite add1n prednK.
      by apply: concaveEk1 (concave_dsum_alphaL_l n.+2).
    have F7n : S_[1] n.+1 + S_[l] n.+1 <= S_[a.-1] n.+1 + S_[c.+2] n.+1.
      rewrite addnC (_ : l = 1 + c.+1 + a.-2); last first.
        by rewrite /c a1E add1n subSS !addSnnS !prednK ?subnK // -ltnS -a1E ltnW.
      rewrite {2}(_ : a.-1 = 1 + a.-2); last by rewrite add1n prednK.
      by apply: concaveEk1 (concave_dsum_alphaL_l n.+1).
    have cm1_gt0 : 0 < c.-1 by rewrite -subn1 ltn_subRL addn0.
    have F8n1 : S_[1] n.+2 + S_[c.+3] n.+2 <= S_[c.-1] n.+2 + S_[5] n.+2.
      rewrite addnC (_ : c.+3 = 1 + 4 + c.-2); last first.
        by rewrite add1n 2!addSnnS !prednK.
      rewrite {2}(_ : c.-1 = 1 + c.-2); last by rewrite add1n prednK.
      by apply: concaveEk1 (concave_dsum_alphaL_l n.+2).
    have F8n : S_[1] n.+1 + S_[c.+2] n.+1 <= S_[c.-1] n.+1 + S_[4] n.+1.
      rewrite addnC (_ : c.+2 = 1 + 3 + c.-2); last first.
        by rewrite add1n 2!addSnnS !prednK.
      rewrite {2}(_ : c.-1 = 1 + c.-2); last by rewrite add1n prednK.
      by apply: concaveEk1 (concave_dsum_alphaL_l n.+1).
    have F9 : S_[5] n.+2 <= S_[4] n.+1 + (α_[1] n.+1).*2.
      by rewrite alphaL1E; apply: dsum_alphaL_alpha.
    have F10 : S_[4] n.+1 <= S_[3] n + (α_[1] n).*2.
      by rewrite alphaL1E; apply: dsum_alphaL_alpha.
    have F11 : S_[1] n.+1 = (S_[3] n).+1 by rewrite dsum_alpha3_S.
    have F12 := leq_dsum_alpha_2l_1 n.+1.
    have F13n1 := dsum_alphaL_S 1 n.+1.
    have F13n := dsum_alphaL_S 1 n.
    (* lia should work *)
    move: P4 P5 P6 P8 => P4 P5 P6 P8.
    rewrite -(leq_add2r x2S).
    rewrite [X in _ <= X](_ : _ = 
      a.*2 + (y1S + d1 + (c.*2 + (d2 + z2S))) + (z1S + x1S + x2S));
      last by ring.
    apply: leq_trans (leq_add (leqnn _) P4); rewrite {P4}//.
    rewrite -(leq_add2r y2S).
    rewrite [X in _ <= X](_ : _ = 
      a.*2 + ( d1 + (c.*2 + d2 )) + (S_[(3 * a).-2] n.+1).*2 +
      (z2S + y2S + y1S)); last by ring.
    apply: leq_trans (leq_add (leqnn _) P5); rewrite {P5}//.
    rewrite -(leq_add2r (x3S + y3S)).
    rewrite [X in _ <= X](_ : _ = 
      a.*2 + c.*2 + d2 + (S_[(3 * a).-2] n.+1).*2 +
      (S_[(3 * c).-2] n.+1).*2 + (d1 + x3S + y3S)); last by ring.
    apply: leq_trans (leq_add (leqnn _) P6); rewrite {P6}//.
    rewrite -(leq_add2r (x5S + y5S)).
    rewrite [X in _ <= X](_ : _ = 
      a.*2 + c.*2 + (S_[(3 * a).-2] n.+1).*2 + (S_[(3 * c).-2] n.+1).*2 +
      (S_[3] n.+1).*2 + (d2 + x5S + y5S)); last by ring. 
    apply: leq_trans (leq_add (leqnn _) P8); rewrite {P8}//.
    rewrite [X in X <= _](_ : _ =  
      (S_[l.+1] n.+2).*2 + (x2S + x3S) + (y3S + x5S) + (y5S + y2S)); 
      last by ring.
    apply: leq_trans (leq_add (leqnn _) y5Sy2SE) _.
    rewrite {y5Sy2SE}addnC addnA.
    apply: leq_trans (leq_add (leqnn _) y3Sx5SE) _.
    rewrite {y3Sx5SE}addnC 2!addnA.
    apply: leq_trans (leq_add (leqnn _) x2Sx3SE) _; rewrite {x2Sx3SE}//.
    rewrite -[(S_[_.-2] _).*2]addnn {1}F1.
    rewrite -[(S_[_.-2] _).*2]addnn {1}F2.
    rewrite -[(S_[3] _).*2]addnn {1}F3.
    rewrite [X in _ <= X](_ : _ =
      a.*2 + c.*2 + (S_[(3 * a).-2] n + S_[(3 * a).-2] n.+1) +
      (S_[(3 * c).-2] n +  S_[(3 * c).-2] n.+1) +
      (S_[3] n + S_[3] n.+1) + (S_[2] n.+1).*2 +
      α_[(3 * c).-2] n + α_[3] n + α_[(3 * a).-2] n);
        last by ring.
    rewrite [X in X <= _](_ : _ =
      (S_[1] n).*2 + (S_[1] n).*2 + (S_[l.+1] n.+2).*2 + (S_[1] n).*2 + 
      α_[(3 * c).-2] n + α_[3] n +  α_[(3 * a).-2] n); last by ring.
    rewrite !leq_add2r.
    rewrite  F4_a F4_c.
    rewrite [X in _ <= X](_ : _ =
      2 + a.-1 + (2 + c.-1 + c.-1) + (S_[(3 * a).-2] n.+1) +
     (S_[(3 * c).-2] n + S_[(3 * c).-2] n.+1) + (S_[3] n + S_[3] n.+1) +
     (S_[2] n.+1).*2 +
       (S_[(3 * a).-2] n + a.-1));last by ring.
    apply: leq_trans (leq_add (leqnn _) F4an).
    rewrite [X in _ <= X](_ : _ =
      2 + (2 + c.-1 + c.-1) + (S_[(3 * c).-2] n + S_[(3 * c).-2] n.+1) + 
      (S_[3] n + S_[3] n.+1) + (S_[2] n.+1).*2 + S_[a.-1] n.+1 +
      (S_[(3 * a).-2] n.+1 + a.-1)); last by ring. 
    apply: leq_trans (leq_add (leqnn _) F4an1).
    rewrite [X in _ <= X](_ : _ =
      4  + c.-1 + S_[(3 * c).-2] n.+1 +
     (S_[3] n + S_[3] n.+1) + (S_[2] n.+1).*2 + S_[a.-1] n.+1 + 
     S_[a.-1] n.+2
        + (S_[(3 * c).-2] n + c.-1)); last by ring.
    apply: leq_trans (leq_add (leqnn _) F4cn).
    rewrite [X in _ <= X](_ : _ =
      4 + (S_[3] n + S_[3] n.+1) + (S_[2] n.+1).*2 +
      S_[a.-1] n.+1 + S_[a.-1] n.+2 + S_[c.-1] n.+1 +
      (S_[(3 * c).-2] n.+1 + c.-1)); last by ring.
    apply: leq_trans (leq_add (leqnn _) F4cn1).
    rewrite {F1 F2 F3 F4 F4_a F4_c F4an F4an1 F4cn F4cn1}//.
    rewrite [X in X <= _](_ : _ =
         (6 * S_[1] n) + (S_[l.+1] n.+2).*2); last by rewrite -!muln2; ring. 
    apply: leq_trans (leq_add (leqnn _) F5) _.
    rewrite [X in _ <= X](_ : _ =
      2 + (S_[3] n).+1 + (S_[3] n.+1).+1 + (S_[2] n.+1).*2 + S_[a.-1] n.+1 + 
      S_[a.-1] n.+2 + S_[c.-1] n.+1 + S_[c.-1] n.+2); last by ring.
    rewrite -{}F6n -{}F6n1.
    rewrite -(leq_add2r (S_[1] n.+2)).
    rewrite [X in X <= _](_ : _ =
     6 * S_[1] n + S_[l] n.+1 + (α_[1] n.+1).*2 + 
     (S_[1] n.+2 + S_[l.+1] n.+2)); last by ring. 
    apply: leq_trans (leq_add (leqnn _) F7n1) _.
    rewrite -(leq_add2r (S_[1] n.+1)).
    rewrite [X in X <= _](_ : _ =
      6 * S_[1] n + (α_[1] n.+1).*2 + (S_[a.-1] n.+2 + 
      S_[c.+3] n.+2) + (S_[1] n.+1 + S_[l] n.+1)); last by ring.
    apply: leq_trans (leq_add (leqnn _) F7n) _.
    rewrite {F7n1 F7n}//.
    rewrite [X in X <= _](_ : _ =
       6 * S_[1] n + (α_[1] n.+1).*2 + S_[c.+3] n.+2 + S_[c.+2] n.+1 +
       (S_[a.-1] n.+2 + S_[a.-1] n.+1)); last by ring.
    rewrite [X in _ <= X](_ : _ =
      2 + S_[1] n.+1 + S_[1] n.+2 + (S_[2] n.+1).*2 + 
      S_[c.-1] n.+1 + S_[c.-1] n.+2 + S_[1] n.+2 + S_[1] n.+1 +
      (S_[a.-1] n.+2 + S_[a.-1] n.+1)); last by ring.
    rewrite leq_add2r.
    rewrite -(leq_add2r (S_[1] n.+2)).
    rewrite [X in X <= _](_ : _ =
      6 * S_[1] n + (α_[1] n.+1).*2 + S_[c.+2] n.+1 + 
      (S_[1] n.+2 + S_[c.+3] n.+2)); last by ring.
    apply: leq_trans (leq_add (leqnn _) F8n1) _.
    rewrite -(leq_add2r (S_[1] n.+1)).
    rewrite [X in X <= _](_ : _ =
       6 * S_[1] n + (α_[1] n.+1).*2 + S_[c.-1] n.+2 + S_[5] n.+2 +
       (S_[1] n.+1 + S_[c.+2] n.+1)); last by ring.
    apply: leq_trans (leq_add (leqnn _) F8n) _.
    rewrite {F8n1 F8n}//.
    rewrite [X in X <= _](_ : _ =
        6 * S_[1] n + (α_[1] n.+1).*2 + S_[4] n.+1 +  S_[5] n.+2 +
        (S_[c.-1] n.+2 + S_[c.-1] n.+1)); last by ring.
    rewrite [X in _ <= X](_ : _ =
         2 + 3 * S_[1] n.+1 + 3 * S_[1] n.+2 + (S_[2] n.+1).*2 +
        (S_[c.-1] n.+2 + S_[c.-1] n.+1)); last by ring.
    rewrite leq_add2r.
    apply: leq_trans (leq_add (leqnn _) F9) _.
    rewrite [X in X <= _](_ : _ =
       6 * S_[1] n + 4 * α_[1] n.+1 + S_[4] n.+1 + S_[4] n.+1); 
         last by rewrite -!mul2n; ring.
    apply: leq_trans (leq_add (leqnn _) F10) _.
    rewrite [X in X <= _](_ : _ =
      6 * S_[1] n + 4 * α_[1] n.+1 + S_[3] n + (α_[1] n).*2 +
       S_[4] n.+1); last by ring.
    apply: leq_trans (leq_add (leqnn _) F10) _.
    rewrite -(leq_add2r 2).
    rewrite [X in X <= _](_ : _ =
      6 * S_[1] n + 4 * α_[1] n.+1 + (α_[1] n).*2  + (α_[1] n).*2 + 
     ((S_[3] n).+1).*2); last by rewrite -!mul2n; ring.
    rewrite -F11.
    rewrite [X in _ <= X](_ : _ =
      3 + 3 * S_[1] n.+1 + 3 * S_[1] n.+2 + (S_[2] n.+1).*2.+1);
        last by rewrite -!mul2n; ring.
    apply: leq_trans _ (leq_add (leqnn _) F12).
    rewrite F13n1 F13n.
    rewrite [X in X <= _](_ : _ =
       4 * α_[1] n.+1 + 6 * α_[1] n + 8 * S_[1] n); last by rewrite -!mul2n; ring.
    rewrite [X in _ <= X](_ : _ =
       (4 * α_[1] n.+1 + 6 * α_[1] n + 8 * S_[1] n) +
       (3 + 2 * α_[1] n));
           last by ring.
    by rewrite leq_addr.
  rewrite !ltnS leqn0 => /eqP bE0.
  have a1E : a1 = a by rewrite -(subnK aLa1) -/b bE0.
  pose u3 := [ffun i : 'I_5 =>
                 if i == 0 :> nat then sam1 
                 else if i == 1 :> nat then tam1 
                 else if i == 2 :> nat then ↓[u (inord a)]
                 else if i == 3 :> nat then sa1 
                 else ta1].
  have cH6 (k : 'I_5) : 
    0 < k < 4 -> codom (u3 k) \subset [:: pa1; apeg k p2 pa1S].
    move=> /andP[k_gt0 k_lt3].
    rewrite !ffunE eqn_leq leqNgt k_gt0 /=.
    case: eqP => [->/=|/eqP kD1].
      rewrite /pa1 /pa1S /apeg /=; case: odd => //=.
      by apply: codom_subC.
    case: eqP =>[->/=|/eqP kD2].
      apply/codom_liftr/codom_subC.
      have /cH : 0 < (inord a : 'I_l.+2) < l.+1.
        by rewrite inordK // a_gt0 /= -a1E.
      by rewrite inordK // /pa1 a1E.
    have ->/= : k = 3 :> nat.
      by case: (k : nat) k_lt3 k_gt0 kD1 kD2 => // [] [|[|[|]]].
    have := sa1C; rewrite /pa1 /pa1S /apeg /=; case: odd => //=.
    by move/codom_subC.
  have P6 : 
    (S_[4] n.+1).*2 <=
    (d[sam1, tam1] + d[tam1, ↓[u (inord a)]] + 
        d[↓[u (inord a)], sa1] +
        d[sa1, ta1]) +
    \sum_(k < n.+1) (sam1 k != p2) * beta n.+1 4 k +
    \sum_(k < n.+1) (ta1 k != p2) * beta n.+1 4 k.
    apply: (leq_trans (IH _ _ _ _ _ _ _ cH6)); rewrite /pa1S /pa1 //.
    - by rewrite eq_sym.
    - by rewrite eq_sym.
    - by rewrite /apeg /=; case: odd => //=; rewrite eq_sym.
    repeat apply: leq_add; rewrite leq_eqVlt; apply/orP; left; apply/eqP.
    - by rewrite !big_ord_recr big_ord0 !ffunE !inordK /= ?a1E.
    - by apply: eq_bigr => i _; rewrite !ffunE /=.
    by apply: eq_bigr => i _; rewrite !ffunE /= a1E.
  set x3S := \sum_(_ < _) _ in P6; set y3S := \sum_(_ < _) _ in P6.
  have x2Sx3SE : x2S + x3S <= (S_[1] n).*2 + α_[maxn (3 * a).-2 4] n.
    by apply: sum_alpha_diffE; rewrite /pa.
  rewrite (maxn_idPl _) in x2Sx3SE; last first.
    by rewrite -subn2 ltn_subRL // (leq_mul2l 3 2).
  have y2Sy3SE : y2S + y3S <= (S_[1] n).*2 + α_[maxn (3 * c).-2 4] n.
    apply: sum_alpha_diffE => //; first by rewrite /pa1.
    by apply: codom_subC.
  rewrite (maxn_idPl _) in y2Sy3SE; last first.
    by rewrite -subn2 ltn_subRL (leq_mul2l 3 2).
  rewrite [\sum_(_ < _) _](_ : _ = 
      \sum_(i < a)  d[u (inord i), u (inord i.+1)] +
      \sum_(a1 <= i < l.+1)  d[u (inord i), u (inord i.+1)]); last first.
    pose f i := d[u (inord i), u (inord i.+1)].
    by rewrite -!(big_mkord xpredT f) a1E -!big_cat_nat.
  rewrite -{}P1 -{P3}P2.
  rewrite [X in _ <= _ + X + _ + _ + _]
      (_ : _  =
            \sum_(i < (3 * a).-2) d[u1 (inord i), u1 (inord i.+1)]
            + d[sam1, tam1] +  d[tam1, ↓[u (inord a)]]); last first.
    pose f i := d[u1 (inord i), u1 (inord i.+1)].
    rewrite -!(big_mkord xpredT f) .
    rewrite -{1}(subnK (_ : 1 < 3 * a)) //; last first.
      by rewrite -[a]prednK // mulnS.
    rewrite subn2 !addn2 !big_nat_recr /f //=; congr (_ + _ + _).
      rewrite ffunE (_ : (3 * a).-2 = (3 * (a.-1)).+1); last first.
        by rewrite -{1}[a]prednK // mulnS.
      rewrite inordK; last by rewrite ltnS ltn_mul2l /= prednK.
      rewrite mod3E /= eqxx.
      rewrite ffunE inordK; last first.
        by rewrite -[_.+3](mulnDr 3 1) add1n prednK // ltnW.
      by rewrite mod3E /= eqxx.
    rewrite ffunE (_ : (3 * a).-2 = (3 * (a.-1)).+1); last first.
      by rewrite -{1}[a]prednK // mulnS.
    rewrite inordK; last first.
      by rewrite -{2}[a]prednK // mulnS.
    rewrite mod3E /= eqxx.
    rewrite ffunE inordK; last first.
      by rewrite -{2}[a]prednK // mulnS.
    by rewrite -[(_ * _).+3](mulnDr 3 1) mod3E /= div3E add1n prednK.
  rewrite [X in _ <= _ + (_ + X) + _ + _](_ : _  = 
      d[↓[u (inord a1)], sa1] +  d[sa1, ta1] +
      \sum_(i < (3 * c).-2) d[u2 (inord i.+2), u2 (inord i.+3)]); last first.
    pose f i := d[u2 (inord i), u2 (inord i.+1)].
    rewrite -!(big_mkord xpredT f) .
    rewrite -{1}(subnK (_ : 1 < 3 * c)) //; last first.
      by rewrite -[c]prednK // mulnS.
    rewrite subn2 !addn2 !big_nat_recl // /f /= !addnA; congr (_ + _ + _).
    - rewrite !ffunE !inordK ?addn0 //=.
      by rewrite ltnS muln_gt0.
    - rewrite !ffunE !inordK //=.
        by rewrite ltnW // ltnS (leq_mul2l 3 1 c).
      by rewrite ltnS muln_gt0.
    by rewrite big_mkord.
  set z1S := \sum_(_ < _) _; set z2S := \sum_(_ < _) _.
  rewrite -/z1S -/z2S in P4, P5.
  rewrite a1E.
  rewrite [X in _ <= X](_ : _ =
    a.*2 + c.*2 +  (
      d[sam1, tam1] +  d[tam1, ↓[u (inord a)]] +
      d[↓[u (inord a)], sa1] +  d[sa1, ta1]) +
      x1S + y1S + z1S + z2S); last by ring.
  set d1 := d[_,_] + d[_,_]  + d[_,_] + d[_,_]; rewrite -/d1 in P6.
  have F1 := dsum_alphaL_S (3 * a).-2 n.
  have F2 := dsum_alphaL_S (3 * c).-2 n.
  have F3 := dsum_alphaL_S 4 n.
  have F4_a : a.*2 = 2 + a.-1 + a.-1.
    by rewrite -{1}[a]prednK // -addnn addnS.
  have F4_c : c.*2 = 2 + c.-1 + c.-1.
    by rewrite -{1}[c]prednK // -addnn addnS.
  have F4 i k : 0 < i -> S_[i.-1] k.+1 <= S_[(3 *i).-2] k + i.-1.
    move=> i_gt0; apply: leq_trans (dsum_alpha3l _ _) _.
    rewrite leq_add2r.
    apply: (increasingE (increasing_dsum_alphaL_l _)).
    by rewrite -{2}[i]prednK // mulnS addSn add2n /=.
  have F4an := F4 a n a_gt0.
  have F4an1 := F4 a n.+1 a_gt0.
  have F4cn := F4 c n (c_gt0).
  have F4cn1 := F4 c n.+1 (c_gt0).
  have l_gt1 : 1 < l.
    by rewrite -ltnS l1E -[3]/(2 + 0 + 1); rewrite !leq_add.
  have F5 := SH l_gt1.
  have am1_gt0 : 0 < a.-1 by rewrite -subn1 ltn_subRL addn0.
  have F6n1 : S_[1] n.+2 + S_[l.+1] n.+2 <= S_[a.-1] n.+2 + S_[c.+2] n.+2.
    rewrite addnC (_ : l.+1 = 1 + c.+1 + a.-2); last first.
      by rewrite  /c add1n 2!addSnnS !prednK ?a1E ?subnK.
    rewrite {2}(_ : a.-1 = 1 + a.-2); last by rewrite add1n prednK.
    by apply: concaveEk1 (concave_dsum_alphaL_l n.+2).
  have F6n : S_[1] n.+1 + S_[l] n.+1 <= S_[a.-1] n.+1 + S_[c.+1] n.+1.
    rewrite addnC (_ : l = 1 + c + a.-2); last first.
      rewrite  /c add1n a1E -{1}[a]prednK // subSS.
      by rewrite !addSnnS !prednK // subnK // -ltnS prednK.
    rewrite {2}(_ : a.-1 = 1 + a.-2); last by rewrite add1n prednK.
    by apply: concaveEk1 (concave_dsum_alphaL_l n.+1).
  have cm1_gt0 : 0 < c.-1 by rewrite -subn1 ltn_subRL addn0.
  have F7n1 : S_[1] n.+2 + S_[c.+2] n.+2 <= S_[c.-1] n.+2 + S_[4] n.+2.
    rewrite addnC (_ : c.+2 = 1 + 3 + c.-2); last first.
      by rewrite add1n 2!addSnnS !prednK.
    rewrite {2}(_ : c.-1 = 1 + c.-2); last by rewrite add1n prednK.
    by apply: concaveEk1 (concave_dsum_alphaL_l n.+2).
  have F7n : S_[1] n.+1 + S_[c.+1] n.+1 <= S_[c.-1] n.+1 + S_[3] n.+1.
    rewrite addnC (_ : c.+1 = 1 + 2 + c.-2); last first.
      by rewrite add1n 2!addSnnS !prednK.
    rewrite {2}(_ : c.-1 = 1 + c.-2); last by rewrite add1n prednK.
    by apply: concaveEk1 (concave_dsum_alphaL_l n.+1).
  have F8 : S_[4] n.+2 <= S_[3] n.+1 + (α_[1] n.+1).*2.
    rewrite alphaL1E.
    by apply: dsum_alphaL_alpha n.+1 (isT : 1 < 3).
  have F9 : S_[3] n.+1 <= S_[4] n.+1 by case: (concave_dsum_alphaL_l n.+1).
  have F10n1 := dsum_alphaL_S 1 n.+1.
  have F10n := dsum_alphaL_S 1 n. 
  have F11 := bound_alphaL 2 n.
  have F12 := alphaL_1_2 n.
   (* lia should work *)
  move: P4 P5 P6 => P4 P5 P6.
  rewrite -(leq_add2r x2S).
  rewrite [X in _ <= X](_ : _ = 
    a.*2 + c.*2 + d1 + y1S + z2S + (z1S + x1S + x2S));
    last by ring.
  apply: leq_trans (leq_add (leqnn _) P4); rewrite {P4}//.
  rewrite -(leq_add2r y2S).
  rewrite [X in _ <= X](_ : _ =
      a.*2 + c.*2 + d1 + (S_[(3 * a).-2] n.+1).*2 +
      (z2S + y2S + y1S)); last by ring.
  apply: leq_trans (leq_add (leqnn _) P5); rewrite {P5}//.
  rewrite -(leq_add2r (x3S + y3S)).
  rewrite [X in _ <= X](_ : _ = 
    a.*2 + c.*2 + (S_[(3 * a).-2] n.+1).*2 + (S_[(3 * c).-2] n.+1).*2 +
    (d1 + x3S + y3S)); last by ring.
  apply: leq_trans (leq_add (leqnn _) P6); rewrite {P6}//.
  rewrite [X in X <= _](_ : _ =  
    (S_[l.+1] n.+2).*2 + (y2S + y3S) + (x2S + x3S)); last by ring.
  apply: leq_trans (leq_add (leqnn _) x2Sx3SE) _; rewrite {x2Sx3SE}addnC addnA.
  apply: leq_trans (leq_add (leqnn _) y2Sy3SE) _; rewrite {y2Sy3SE}//.
  rewrite -[(S_[_.-2] _).*2]addnn {1}F1.
  rewrite -[(S_[_.-2] _).*2]addnn {1}F2.
  rewrite [X in X <= _](_ : _ =
    (S_[1] n).*2 + (S_[l.+1] n.+2).*2 + (S_[1] n).*2 + 
      α_[(3 * a).-2] n + α_[(3 * c).-2] n); last by ring.
  rewrite [X in _ <= X](_ : _ =
      a.*2 + c.*2 + S_[(3 * a).-2] n + S_[(3 * a).-2] n.+1 + 
      S_[(3 * c).-2] n +  S_[(3 * c).-2] n.+1 + (S_[4] n.+1).*2 +
      α_[(3 * a).-2] n + α_[(3 * c).-2] n); last by ring.
  rewrite !leq_add2r.
  rewrite {}F4_a {}F4_c.
  rewrite [X in _ <= X](_ : _ =
      4 + (S_[(3 * a).-2] n + a.-1) + 
        (S_[(3 * c).-2] n + c.-1) + (S_[(3 * c).-2] n.+1 + c.-1) + 
        (S_[4] n.+1).*2 + (S_[(3 * a).-2] n.+1 + a.-1)); last by ring.
  apply: leq_trans (leq_add (leqnn _) F4an1).
  rewrite [X in _ <= X](_ : _ =
    4 + (S_[(3 * c).-2] n + c.-1) +
    (S_[(3 * c).-2] n.+1 + c.-1) + (S_[4] n.+1).*2 + 
    S_[a.-1] n.+2 +  (S_[(3 * a).-2] n + a.-1)); last by ring.
  apply: leq_trans (leq_add (leqnn _) F4an).
  rewrite [X in _ <= X](_ : _ =
    4 + (S_[(3 * c).-2] n + c.-1) + (S_[4] n.+1).*2 + S_[a.-1] n.+2 + 
    S_[a.-1] n.+1 + (S_[(3 * c).-2] n.+1 + c.-1)); last by ring.
  apply: leq_trans (leq_add (leqnn _) F4cn1).
  rewrite [X in _ <= X](_ : _ =
      4 + (S_[4] n.+1).*2 + S_[a.-1] n.+2 + S_[a.-1] n.+1 + S_[c.-1] n.+2 + 
    (S_[(3 * c).-2] n + c.-1)); last by ring.
  apply: leq_trans (leq_add (leqnn _) F4cn).
  rewrite {F4an1 F4an F4cn1 F4cn}//.
  rewrite -!addnA addnC addnA.
  apply: leq_trans (leq_add (leq_add F5 (leqnn _)) (leqnn _)) _.
  rewrite -(leq_add2r (S_[c.+2] n.+2)).
  rewrite [X in _ <= X](_ : _ =
    4 + (S_[4] n.+1).*2 +S_[a.-1] n.+1 +
    S_[c.-1] n.+2 + S_[c.-1] n.+1 + (S_[a.-1] n.+2 +  S_[c.+2] n.+2)); 
      last by ring.
  apply: leq_trans _ (leq_add (leqnn _) F6n1).
  rewrite -(leq_add2r (S_[c.+1] n.+1)).
  rewrite [X in _ <= X](_ : _ =
      4 + (S_[4] n.+1).*2 + S_[c.-1] n.+2 +
      S_[c.-1] n.+1 + (S_[1] n.+2 + S_[l.+1] n.+2) + 
      (S_[a.-1] n.+1 + S_[c.+1] n.+1)); last by ring.
  apply: leq_trans _ (leq_add (leqnn _) F6n).
  rewrite {F6n1 F6n}//.
  rewrite [X in X <= _](_ : _ =
    (α_[1] n.+1).*2 + (S_[1] n).*2 + (S_[1] n).*2 +
    S_[c.+2] n.+2 + S_[c.+1] n.+1 + (S_[l.+1] n.+2 + S_[l] n.+1 ));
        last by ring.
  rewrite [X in _ <= X](_ : _ =
      4 + (S_[4] n.+1).*2 + S_[c.-1] n.+2 + S_[c.-1] n.+1 +
    S_[1] n.+2 + S_[1] n.+1 + (S_[l.+1] n.+2  + S_[l] n.+1)); last by ring.
  rewrite leq_add2r.
  rewrite -(leq_add2r (S_[1] n.+2)).
  rewrite [X in X <= _](_ : _ =
    (α_[1] n.+1).*2 + (S_[1] n).*2 + (S_[1] n).*2 + S_[c.+1] n.+1 +
    (S_[1] n.+2 + S_[c.+2] n.+2)); last by ring.
  apply: leq_trans (leq_add (leqnn _) F7n1) _.
  rewrite -(leq_add2r (S_[1] n.+1)).
  rewrite [X in X <= _](_ : _ =
    (α_[1] n.+1).*2 + (S_[1] n).*2 + (S_[1] n).*2 +
    (S_[c.-1] n.+2 + S_[4] n.+2) + (S_[1] n.+1 + S_[c.+1] n.+1)); 
    last by ring.
  apply: leq_trans (leq_add (leqnn _) F7n) _.
  rewrite [X in X <= _](_ : _ =
    (α_[1] n.+1).*2 + (S_[1] n).*2 + (S_[1] n).*2 + S_[3] n.+1 +
      S_[4] n.+2 + (S_[c.-1] n.+2 + S_[c.-1] n.+1)); last by ring.
  rewrite [X in _ <= X](_ : _ =
    4 + (S_[4] n.+1).*2 + S_[1] n.+2 + S_[1] n.+1 + S_[1] n.+2 + S_[1] n.+1 +
    (S_[c.-1] n.+2 + S_[c.-1] n.+1)); last by ring.
  rewrite [X in X <= _](_ : _ =
    (α_[1] n.+1).*2 + (S_[1] n).*2 + (S_[1] n).*2 + S_[3] n.+1 +
    (S_[c.-1] n.+2 + S_[c.-1] n.+1) + S_[4] n.+2); last by ring. 
  apply: leq_trans (leq_add (leqnn _) F8) _.
  rewrite [X in X <= _](_ : _ =
    (α_[1] n.+1).*2 + (S_[1] n).*2 + (S_[1] n).*2 +
    (α_[1] n.+1).*2 + (S_[3] n.+1).*2 + (S_[c.-1] n.+2 + S_[c.-1] n.+1));
      last by rewrite -!mul2n; ring.
  rewrite [X in _ <= X](_ : _ =
    4 + S_[1] n.+2 + S_[1] n.+1 + S_[1] n.+2 + S_[1] n.+1 +
    (S_[4] n.+1).*2  + (S_[c.-1] n.+2 + S_[c.-1] n.+1)); last by ring.
  rewrite leq_add2r.
  apply: leq_add; last by rewrite leq_double.
  rewrite F10n1 F10n.
  rewrite [X in X <= _](_ : _ = 
      (α_[1] n.+1).*2 + (α_[1] n.+1).*2  + 4 * S_[1] n);
      last by rewrite -!mul2n; ring.
  rewrite [X in _ <= X](_ : _ =
      (2 + (α_[1] n).*2).*2 + (α_[1] n.+1).*2 + 4 * S_[1] n); 
        last by rewrite -!mul2n; ring.
  rewrite !leq_add2r leq_double.
  by rewrite (leq_trans F12) // leq_addl.
rewrite negb_and -!leqNgt => acH.
have aLc : a <= c by [].
have aE1 : a = 1.
  case/orP: acH; case: (a) aLc a_gt0 => // [] [|n1] //.
  by case: (c) => // [] [].
move: c_gt0; rewrite leq_eqVlt eq_sym => /orP[/eqP cE1|c_gt1].
  move : P1 P2 P3 => P1 P2 P3.
  have l_gt0 : 0 < l by rewrite -ltnS l1E aE1 cE1 addn1.
  have a1El : a1 = l.
    by rewrite -(subKn (_ : a1 <= l.+1)) 1?ltnW // -/c cE1 subSS subn0.
  have [b_gt1|b_lt2]:= leqP 2 b.
    rewrite [\sum_(_ < _) _](_ : _ = 
        \sum_(i < a)  d[u (inord i), u (inord i.+1)] +
        \sum_(a <= i < a1)  d[u (inord i), u (inord i.+1)] +
        \sum_(a1 <= i < l.+1)  d[u (inord i), u (inord i.+1)]); last first.
      pose f i := d[u (inord i), u (inord i.+1)].
      rewrite -!(big_mkord xpredT f).
      by rewrite -!big_cat_nat //= ltnW.
    rewrite !sum_beta_S // KH1 eqxx addn0 KH2 eqxx addn0.
    apply: leq_trans (leq_add (leq_add (leq_add (leq_add (leqnn _) P3) 
                       (leqnn _)) (leqnn _)) (leqnn _)); rewrite -{P3}P1 -{}P2.
    set x0S := \sum_(_ < _) _; set x2S := \sum_(_ < _) _.
    pose u3 := [ffun i : 'I_b.+1 => ↓[u (inord (a + i))]].
    rewrite [\sum_(_ <= _ < _) _](_ : _ =
        \sum_(i < b)  d[u3 (inord i), u3 (inord i.+1)]); last first.
      rewrite -{1}[a]add0n big_addn  -/b big_mkord.
      apply: eq_bigr => i _.
      by rewrite !ffunE addnC !inordK ?(addnS, ltnS) // ltnW.
    pose paS := apeg a.+1 p1 p3.
    have cH3 (k : 'I_b.+1) : 
      0 < k < b -> codom (u3 k) \subset [:: p2; apeg k pa paS].
      move=> /andP[k_gt0 k_ltb].
      have akLl : a + k < l.+1.
        rewrite  ltnS (leq_trans _ a1Ll) //.
        by rewrite -(subnK aLa1) addnC leq_add2r ltnW.
      rewrite !ffunE.
      have /H : 0 < (inord (a + k) : 'I_l.+2) < l.+1.
        rewrite inordK; first by rewrite addn_gt0 a_gt0.
        by rewrite ltnS ltnW.
      rewrite ffunE inordK //; last by rewrite ltnS ltnW.
      by rewrite /pa /paS /apeg odd_add /=; do 2 case: odd. 
    pose pa1 := apeg a1 p1 p3.
    have P3 : 
      (S_[b] n.+1).*2 <=
      \sum_(i < b)  d[↓[u (inord (a + i))], ↓[u (inord (a + i).+1)]] +
      \sum_(k < n.+1) (↓[u (inord a)] k != pa) * beta n.+1 b k +
      \sum_(k < n.+1) (↓[u (inord a1)] k != pa1) * beta n.+1 b k.
      apply: leq_trans (IH _ _ _ _ _ _ _ cH3) (leq_add (leq_add _ _) _);
        rewrite /pa /paS // 1?eq_sym //.
      - by rewrite /apeg /=; case: odd; rewrite // eq_sym.
      - apply: leq_sum => i; rewrite !ffunE !inordK ?addnS //.
          by rewrite ltnS.
        by rewrite ltnS ltnW.
      - by apply: leq_sum => i _; rewrite !ffunE addn0.
      apply: leq_sum => i _; rewrite !ffunE /= [a + b]addnC subnK //.
      by rewrite /b /pa /pa1 /apeg odd_sub //=; do 2 case: odd.
    set x1S := \sum_(_ < _) _ in P3; set y2S := \sum_(_ < _) _ in P3.
    set y3S := \sum_(_ < _) _ in P3.
    rewrite [\sum_(_ < _) _](_ : _ = x1S); last first.
      by apply: eq_bigr => i; rewrite !ffunE !inordK ?addnS // ltnS // ltnW.
    set y0S := \sum_(_ < _)_; set y5S := \sum_(_ < _)_.
    have cH1 (k : 'I_(3 * a).+1) : 
      0 < k < 3 * a -> codom (u1 k) \subset [:: p3; apeg k p1 p2].
      move=> /andP[k_gt0 k_ltb].
      rewrite {2}aE1 muln1 in k_ltb.
      rewrite ffunE !modn_small // !divn_small // inord_eq0 //.
      rewrite [in 3 * a.-1]aE1 /=.
      case: (k : nat) k_gt0 k_ltb => //= [] [|[|]] //= _ _.
        by have := sam1C; rewrite /pa /paS aE1 /apeg /=.
      by apply: codom_subC.
    have P1 : 
      (S_[3 * a] n.+1).*2 <= x0S +
      \sum_(k < n.+1) (↓[u ord0] k != p1) * beta n.+1 3 k +
      \sum_(k < n.+1) (↓[u (inord a)] k != p2) * beta n.+1 3 k.
      apply: leq_trans (IH _ _ _ _ _ _ _ cH1) (leq_add (leq_add _ _) _);
          rewrite // 1?eq_sym //.
        by apply: leq_sum => i _; rewrite ffunE /= inord_eq0 // aE1 muln1.
      by apply: leq_sum => i _; rewrite ffunE /= mod3E /= div3E // aE1 muln1.
    have {}P1 := leq_trans P1 (leq_add (leq_add (leqnn _) (leq_sum_beta _ _))
                          (leqnn _)).
    rewrite -/y0S in P1; set y1S := \sum_(_ < _) _ in P1.
    rewrite aE1 muln1 in P1.
    have y1Sy2SE : y1S + y2S <= (S_[1] n).*2 + α_[maxn 3 b] n.
      apply: sum_alpha_diffE => //; first by rewrite /pa // eq_sym.
      apply: codom_liftr.
      have /cH : 0 < (inord 1 : 'I_l.+2) < l.+1 by rewrite inordK.
      by rewrite /pa aE1 inordK.
    have cH2 (k : 'I_(3 * c).+1) : 
      0 < k < 3 * c -> 
      codom (u2 k) \subset [:: apeg a1 p1 p3; apeg k p2 (apeg a1.+1 p1 p3)].
      move=> /andP[k_gt0 k_ltb].
      rewrite {2}cE1 muln1 in k_ltb.
      rewrite ffunE !modn_small // !divn_small // addn0.
      case: (k : nat) k_gt0 k_ltb => //= [] [|[|]] //= _ _.
        rewrite /apeg /=; case: odd => //=.
        by apply: codom_subC.
      by apply: codom_subC.
    have P2 : 
      (S_[3 * c] n.+1).*2 <= x2S +
      \sum_(k < n.+1) (↓[u (inord a1)] k != p2) * beta n.+1 3 k +
      \sum_(k < n.+1) (↓[u ord_max] k != apeg l.+1 p1 p3) * beta n.+1 3 k.
      apply: leq_trans (IH _ _ _ _ _ _ _ cH2) (leq_add (leq_add _ _) _);
          rewrite // 1?eq_sym //.
      - by rewrite /apeg /=; case: odd; rewrite //= eq_sym.
      - by apply: leq_sum => i _; rewrite ffunE /= addn0 cE1 muln1.
      apply: leq_sum => i _; rewrite ffunE /= mod3E /= div3E // cE1 muln1.
      rewrite a1El addn1 (_ : inord _ = ord_max) //.
      by apply/val_eqP; rewrite /= inordK.
    have {}P2 := leq_trans P2 (leq_add (leqnn _) (leq_sum_beta _ _)).
    rewrite -/y5S in P2; set y4S := \sum_(_ < _) _ in P2.
    have y3Sy4SE : y3S + y4S <= (S_[1] n).*2 + α_[maxn b 3] n.
      apply: sum_alpha_diffE; rewrite /pa /pa1 //.
      apply/codom_liftr/codom_subC.
      have /cH : 0 < (inord l : 'I_l.+2) < l.+1 by rewrite inordK // l_gt0 /=.
      by rewrite a1El inordK.
    have Eb1 : l = b.+1.
      by have := l1E; rewrite aE1 cE1 addn1 => [] [].
    rewrite Eb1.
    have F1b := dsum_alphaL_S b n.
    have F1n31 : (S_[3] n.+1).+1 = S_[1] n.+2.
      by rewrite dsum_alpha3_S.
    have F1n1 := dsum_alphaL_S 1 n.
    have F1n2 := dsum_alphaL_S 1 n.+1.
    have b_gt0 : 0 < b by apply: leq_trans b_gt1.
    have F2n1 : S_[b.+2] n.+2 <= S_[b.+1] n.+1 + (α_[1] n.+1).*2.
      by rewrite alphaL1E dsum_alphaL_alpha .
    have F2n : S_[b.+1] n.+1 <= S_[b] n + (α_[1] n).*2.
      by rewrite alphaL1E dsum_alphaL_alpha.
    have F3n : S_[4] n.+2 <= S_[3] n.+1 + (α_[1] n.+1).*2.
      by rewrite alphaL1E dsum_alphaL_alpha.
    have F4n := alphaL_3E n.
    have F5 := leq_dsum_alpha_2l_1 n.+1.
    (* lia should solve this *)
    move: P1 P2 P3 => P1 P2 P3.
    rewrite -(leq_add2r y1S).
    rewrite [X in _ <= X](_ : _ =
      a.*2 + x1S + (c.*2 + x2S) + y5S + (x0S + y0S + y1S));
        last by ring.
    apply: leq_trans (leq_add (leqnn _) P1); rewrite {P1}//.
    rewrite -(leq_add2r y4S).
    rewrite [X in _ <= X](_ : _ =   a.*2 + x1S + c.*2 + 
      (S_[3] n.+1).*2 + (x2S + y4S + y5S)); last by ring.
    apply: leq_trans (leq_add (leqnn _) P2); rewrite {P2}//.
    rewrite -(leq_add2r (y2S + y3S)).
    rewrite [X in _ <= X](_ : _ =
       a.*2 + c.*2 + (S_[3] n.+1).*2 + (S_[3 * c] n.+1).*2 +
       (x1S + y2S + y3S)); last by ring.
    apply: leq_trans (leq_add (leqnn _) P3); rewrite {P3}//.
    rewrite [X in X <= _](_ : _ =
      (S_[b.+2] n.+2).*2 + (y1S + y2S) + (y3S + y4S)); last by ring.
    apply: leq_trans (leq_add (leqnn _) y3Sy4SE) _; rewrite {y3Sy4SE}//.
    rewrite addnAC maxnC aE1 cE1 muln1.
    apply: leq_trans (leq_add (leqnn _) y1Sy2SE) _; rewrite {y1Sy2SE}//.
    rewrite [X in X <= _](_ : _ =
       (S_[b.+2] n.+2 + (S_[1] n).*2 + α_[maxn 3 b] n).*2); 
       last by rewrite -!mul2n; ring.  
    rewrite [X in _ <= X](_ : _ =
       ((S_[3] n.+1).+1.*2 + S_[b] n.+1).*2); last by rewrite -!mul2n; ring.
    rewrite leq_double.
    move: b_gt1; rewrite leq_eqVlt => /orP[/eqP<-|b_gt2]; last first.
      rewrite (maxn_idPr _) //.    
      rewrite F1b addnA leq_add2r F1n31 F1n2 F1n1.
      rewrite [X in _ <= X](_ : _ = 
        (S_[1] n).*2 + (α_[1] n.+1).*2 + (S_[b] n + (α_[1] n).*2));
          last by rewrite -!mul2n; ring.
      apply: leq_trans (leq_add (leqnn _) F2n).
      rewrite addnAC -addnA.
      apply: leq_trans (leq_add (leqnn _) F2n1).
      by rewrite addnC.
    rewrite (maxn_idPl _) // -addnA.
    apply: leq_trans (leq_add F3n (leqnn _)) _.
    rewrite -ltnS -!addSn !F1n31 F4n.
    rewrite -[in X in _ <= X]addnn -addnS -!addnA leq_add2l.
    rewrite F1n2 -addSn  !addnA [in X in _ <= X]addnAC leq_add2r.
    have [n_gt3 |] := leqP 4 n; last first.
      by case: n => [|[|[|[|n1]]]]; rewrite // !(alphaS_small, alpha_small).
    rewrite -leq_double -ltnS !doubleD -!addnS.
    apply: leq_trans (leq_add (leqnn _) F5).
    rewrite F1n2 F1n1.
    rewrite [X in X <= _](_ : _ = 3 * α_[1] n.+1 +
                                (1 + 4 * S_[1] n + α_[1] n.+1));
      last by rewrite -!mul2n; ring.
    rewrite [X in _ <= X](_ : _ = 1 + 4 * α_[1] n + 
                          (1 + 4 * S_[1] n +  α_[1] n.+1));
      last by rewrite -!mul2n; ring.
    rewrite leq_add2r ltnW // ltnS.
    by rewrite !alphaL1E; apply: alpha_4_3.
  move: b_lt2; rewrite leq_eqVlt => /orP[/eqP [] bE1 | b_lt1].
    pose u1l := 
      [ffun i =>  
        if (i : 'I_5) == 0 :> nat then ↓[u ord0] else
        if i == 1 :> nat then sam1 else
        if i == 2 :> nat then tam1 else 
        if i == 3 :> nat then ↓[u (inord 1)] else ↓[u (inord 2)]].
    have a1E2 : a1 = 2.
      by move: (cE1); rewrite /c l1E aE1 bE1 cE1; case: (a1) => // [] [|[|]].
    have P1l1 : 
      a.*2 + \sum_(i < 4)  d[u1l (inord i), u1l (inord i.+1)] <=
      \sum_(i < a1) d[u (inord i), u (inord i.+1)].
      rewrite a1E2 !big_ord_recr /= !big_ord0 !add0n {1}aE1.
      rewrite !ffunE /= !inordK ?aE1 //= add2n -2!addSn leq_add //; last first.
        by apply/gdist_cunlift/shanoi_connect.
      rewrite (inord_eq0 _ (_ : 0 = 0)) //.
      rewrite (_ : ord0 = inord a.-1); last first.
        by apply/val_eqP; rewrite /= inordK aE1.
      by rewrite -[in inord 1]aE1 duam1ua1E /= addnA addn0.
    have cH1 (k : 'I_5) : 
      0 < k < 4 -> codom (u1l k) \subset [:: p3; apeg k p1 p2].
      case: k => [] [|[|[|[|]]]] //= iH _; rewrite !ffunE /apeg /=.
      - by have := sam1C; rewrite /pa aE1.
      - by apply: codom_subC.
      apply/codom_liftr/codom_subC.
      have /cH: 0 < (inord 1 : 'I_l.+2) < l.+1 by rewrite inordK.
      by rewrite inordK.
    have lE2 : l = 2 by move: l1E; rewrite aE1 bE1 cE1 => [] [].
    have {cH1}P4 :
      (S_[4] n.+1).*2 <=
      \sum_(i < 4)  d[u1l (inord i), u1l (inord i.+1)] +
      \sum_(k < n.+1) (↓[u ord0] k != p1) * beta n.+1 4 k +
      \sum_(k < n.+1) (↓[u (inord a1)] k != p1) * beta n.+1 4 k.
      apply: leq_trans (IH _ _ _ _ _ _ _ cH1) _ => //.
        by rewrite eq_sym.
      repeat apply: leq_add => //; apply: leq_sum  => i /= _; rewrite !ffunE //.
      by rewrite a1El -[in inord 2]lE2.
    have {}P4 := leq_trans P4 (leq_add (leq_add (leqnn _) (leq_sum_beta _ _))
                                    (leqnn _)).
    set x1S := \sum_(_ < _) _ in P4.
    set y1S := \sum_(_ < _) _ in P4; set y2S := \sum_(_ < _) _ in P4.
    have cH2 (k : 'I_(3 * c).+1) : 
      0 < k < 3 * c -> 
      codom (u2 k) \subset [:: apeg a1 p1 p3; apeg k p2 (apeg a1.+1 p1 p3)].
      move=> /andP[k_gt0 k_ltb].
      rewrite {2}cE1 muln1 in k_ltb.
      rewrite ffunE !modn_small // !divn_small // addn0.
      case: (k : nat) k_gt0 k_ltb => //= [] [|[|]] //= _ _.
        by rewrite a1E2.
      by apply: codom_subC.
    have P5 : 
      (S_[3 * c] n.+1).*2 <= \sum_(i < 3 * c)  d[u2 (inord i), u2 (inord i.+1)] +
      \sum_(k < n.+1) (↓[u (inord a1)] k != p2) * beta n.+1 3 k +
      \sum_(k < n.+1) (↓[u ord_max] k != apeg l.+1 p1 p3) * beta n.+1 3 k.
      apply: leq_trans (IH _ _ _ _ _ _ _ cH2) (leq_add (leq_add _ _) _);
          rewrite // 1?eq_sym //.
      - by rewrite a1E2 eq_sym.
      - by apply: leq_sum => i _; rewrite ffunE /= addn0 cE1 muln1.
      apply: leq_sum => i _; rewrite ffunE /= mod3E /= div3E // cE1 muln1.
      rewrite a1El addn1 (_ : inord _ = ord_max) //.
      by apply/val_eqP; rewrite /= inordK.
    have {}P5 := leq_trans P5 (leq_add (leqnn _) (leq_sum_beta _ _)).
    rewrite // {1}[in 3 *c]cE1 muln1 in P5.
    set x2S := \sum_(_ < _) _ in P5.
    set y3S := \sum_(_ < _) _ in P5; set y4S := \sum_(_ < _) _ in P5.
    rewrite -(big_mkord xpredT (fun i => d[u (inord i), u (inord i.+1)])).
    rewrite (big_cat_nat _ _ _ (_ : 0 <= a1)) //=; last by apply: ltnW.
    rewrite big_mkord -!addnA.
    apply: leq_trans (leq_add P1l1  (leqnn _)); rewrite -/x1S.
    rewrite -{P1l1}P2 -/x2S {1}lE2 !sum_beta_S //.
    rewrite KH1 KH2 !eqxx !addn0 aE1 -/y1S -/y4S.
    have y2Sy3SE : y2S + y3S <= (S_[1] n).*2 + α_[4] n.
      apply: sum_alpha_diffE => //.
      apply/codom_liftr/codom_subC.
      have /cH : 0 < (inord a1 : 'I_l.+2) < l.+1 by rewrite inordK // a1E2 lE2.
      by rewrite inordK // a1E2.
    rewrite {1}aE1 -[1.*2]/2 in P1.
    rewrite {1}cE1 -[1.*2]/2.
    have F1n4 := dsum_alphaL_S 4 n.
    have F1n3 : (S_[3] n.+2).+1 = S_[1] n.+3.
      by rewrite -dsum_alpha3_S.
    have F1n13 : (S_[3] n.+1).+1 = S_[1] n.+2.
      by rewrite -dsum_alpha3_S.
    have F2 k : 5 * S_[1] k.+1 + S_[1] k.+2 <= 6 * S_[4] k + 9.
      have F3 :  4 * S_[3] k + 2 * S_[6] k <= 6 * S_[4] k.
        rewrite -{1}[4]/(2 * 2) -mulnA -mulnDr -{2}[6]/(2 * 3) -mulnA.
        rewrite leq_mul2l /= -(leq_add2r (S_[5] k)).
        rewrite[X in X <= _](_ : _ =
          S_[6] k + S_[3] k +  (S_[5] k + S_[3] k)
          ); last by ring.
        rewrite[X in _ <= X](_ : _ =
          S_[5] k + S_[4] k +  (S_[4] k + S_[4] k)
          ); last by ring.
        by apply: leq_add; apply: concaveEk1 3 _ _ (concave_dsum_alphaL_l k).
      apply: leq_trans (leq_add F3 (leqnn _)).
      have F3k : S_[1] k.+1 <= S_[3] k + 1 by apply: dsum_alpha3l.
      have F3k1 : S_[2] k.+1 <= S_[6] k + 2 by apply: dsum_alpha3l.
      rewrite [X in _ <= X](_ : _ = 
        (((S_[3] k + 1) + (S_[3] k + 1)) + 
        ((S_[3] k + 1) + (S_[3] k + 1))) + 1 +
        ((S_[6] k + 2) + (S_[6] k + 2))); last by ring.
      apply: leq_trans (leq_add (leqnn _) (leq_add F3k1 F3k1)).
      rewrite -addnA.
      apply: leq_trans (leq_add (leq_add (leq_add F3k F3k) (leq_add F3k F3k))
                (leqnn _)).
      have F4 := leq_dsum_alpha_2l_1 k.+1.
      rewrite !addnn add1n.
      apply: leq_trans (leq_add (leqnn _) F4).
      rewrite !addnA leq_add2r.
      by rewrite [X in _ <= X](_ : _ = 5 * S_[1] k.+1 ) => //; 
         rewrite -!mul2n; ring.
   (* lia should work *)
    move: P4 P5 => P4 P5.
    rewrite -(leq_add2r y2S).
    rewrite [X in _ <= X](_ : _ =
      4 + x2S + y4S + (x1S + y1S + y2S)); last by ring.
    apply: leq_trans (leq_add (leqnn _) P4); rewrite {P4}//.
    rewrite -(leq_add2r y3S).
    rewrite [X in _ <= X](_ : _ =
      4 + (S_[4] n.+1).*2 + (x2S + y3S + y4S)); last ring.
    apply: leq_trans (leq_add (leqnn _) P5); rewrite {P5}//.
    rewrite [X in X <= _](_ : _ =
      (S_[3] n.+2).*2 + (y2S + y3S)); last by ring.
    apply: leq_trans (leq_add (leqnn _) y2Sy3SE) _; rewrite {y2Sy3SE}//.
    rewrite -[in X in _ <= X]addnn.
    rewrite {1}F1n4 -(leq_add2r 2).
    rewrite [X in X <= _](_ : _ =
      ((S_[3] n.+2).+1).*2 + (S_[1] n).*2 + α_[4] n); 
      last by rewrite -!mul2n; ring.
    rewrite [X in _ <= X](_ : _ =
      4 + S_[4] n + S_[4] n.+1 + ((S_[3] n.+1).+1).*2 + α_[4] n); 
        last by rewrite -!mul2n; ring.
    rewrite leq_add2r F1n3 F1n13.
    rewrite -(leq_add2r (S_[1] n.+2).*2).
    case : n => [|[|[|[|n1]]]]; try by rewrite !alphaS_small.
    set m1 := n1.+3.
    rewrite -[_ <= _](leq_mul2l 6).
    rewrite[X in _ <= X](_ : _ =
      6 + 24 * (S_[1] m1.+3) + ((6 * S_[4] m1.+1 + 9) +
                                (6 * S_[4] m1.+2 + 9)));
      last by rewrite -!mul2n; ring.
    apply: leq_trans _ (leq_add (leqnn _) (leq_add (F2 m1.+1) (F2 m1.+2))).
    rewrite[ X in _ <= X](_ : _ =
      18 * S_[1] m1.+3 + 5 * S_[1] m1.+2 + 6 +
           (S_[1] m1.+4 + 12 * S_[1] m1.+3));
      last by ring.
    rewrite[ X in X <= _](_ : _ =
      11 * S_[1] m1.+4 + 12 * S_[1] m1.+1 + 
             (S_[1] m1.+4 + 12 * S_[1] m1.+3 ));
      last by rewrite -!mul2n; ring.
    rewrite leq_add2r.
    have F3n3 := dsum_alphaL_S 1 m1.+3.
    have F3n2 := dsum_alphaL_S 1 m1.+2.
    have F3n1 := dsum_alphaL_S 1 m1.+1.
    rewrite !(F3n3, F3n2, F3n1).
    rewrite [X in X <= _](_ : _ =
      11 * α_[1] m1.+3 +
      (11 * α_[1] m1.+1 + 11 * α_[1] m1.+2 + 23 * S_[1] m1.+1)); last by ring.
    rewrite [X in _ <= X](_ : _ =
      7 * α_[1] m1.+2 +
      12 * α_[1] m1.+1 + 6 + (11 * α_[1] m1.+1 + 
      11 * α_[1] m1.+2 + 23 * S_[1] m1.+1)); last by ring.
    rewrite leq_add2r.
    have F4m1 : 12 * α_[1] m1.+3 <= 16 * α_[1] m1.+2.
      rewrite -[12]/(4 * 3) -mulnA.
      rewrite -[16]/(4 * 4) -mulnA leq_mul2l /=.
      by rewrite !alphaL1E alpha_4_3.
    apply: leq_trans (leq_trans _ F4m1) _; first by rewrite leq_mul2r orbT.
    rewrite -[16]/(7 + 9) mulnDl -addnA leq_add2l.
    have F4m2 : 9 * α_[1] m1.+2 <= 12 * α_[1] m1.+1.
      rewrite -[12]/(3 * 4) -mulnA.
      rewrite -[9]/(3 * 3) -mulnA leq_mul2l /=.
      by rewrite !alphaL1E alpha_4_3.
    by apply: leq_trans F4m2 (leq_addr _ _).
  have bE0 : b = 0 by case: (b) b_lt1 => //.
  have lE1 : l = 1 by have := l1E; rewrite aE1 bE0 cE1 => [] [].
  have a1E1 : a1 = 1 by rewrite a1El.
  rewrite (_ : apeg 0 p1 p3 = apeg 0 p1 p2) //.
  rewrite (_ : apeg l.+1 p1 p3 = apeg l.+1 p1 p2); last by rewrite lE1.
  apply: (@case2 m IH)  => //.
  - by rewrite (_ : apeg _ = apeg 1).
  - move=> k hK; rewrite {3}lE1 in hK.
    have -> : k = inord 1.
      apply/val_eqP; rewrite /= inordK //.
      by case: (k : nat) hK => [] // [|].
    rewrite inordK /apeg //= .
    apply: codom_subC.
    have := cH (inord 1).
    rewrite inordK /apeg //= .
    by apply.
  - by rewrite KH2 lE1.
  move=> k.
  have [->|[->|->]] // : k = ord0 \/ k = (inord 1) \/ k = (inord 2).
  - move: k; rewrite lE1.
    case => [] []; first by left; apply: val_inj => /=.
    case.
      by right; left; apply: val_inj; rewrite /= inordK.
    case => //.
    by right; right; apply: val_inj; rewrite /= inordK.
  by rewrite -[in inord 1]aE1 uaLEp2 aE1 inordK.
  rewrite {1}(_ : inord 2 = ord_max); last first.
    by apply/val_eqP; rewrite /= lE1 inordK.
  by rewrite KH2 lE1 /= inordK.
pose u2r := [ffun i : 'I_(3 * c).-2.+1 => u2 (inord i.+2)].
pose pa1 := apeg a1 p1 p3.
pose pa1S := apeg a1.+1 p1 p3.
have cH8 (k : 'I_(3 * c).-2.+1) : 
  0 < k < (3 * c).-2 -> codom (u2r k) \subset [:: p2; apeg k pa1 pa1S].
  move=> /andP[k_gt0 k3L3a].
  have k2L3c : k.+2 < (3 * c).
    by have := k3L3a; rewrite -{2}subn2 ltn_subRL add2n.    
  rewrite !ffunE inordK ?ltnS 1?ltnW //.
  case: eqP => [km3E0 /= |/eqP km3D0].
    have k3_gt0 : 0 < k.+2 %/ 3.
      case: (k: nat) k_gt0 km3E0  => // [] //= k1 _ _.
      by rewrite (divnMDl 1 k1 (_ : 0 < 3)).
    have a1k3Ll1 : a1 + k.+2 %/ 3 < l.+1.
      move: k2L3c.
      rewrite {1}(divn_eq k.+2 3) km3E0 addn0 mulnC ltn_mul2l /= => k2L3c.
      rewrite -(subnK (_ : a1 <= l.+1)) ?(leq_trans a1Ll) //.
      by rewrite addnC ltn_add2r -/c.
    rewrite (_ : apeg _ _ _ = apeg (a1 + k.+2) p1 p3) ; last first.
      by rewrite /pa1 /pa1S /apeg /= odd_add /= negbK; do 2 case: odd.
    rewrite (_ : apeg _ _ _ = apeg (a1 + (k.+2) %/ 3) p1 p3) ; last first.
      rewrite /apeg odd_add {1}(divn_eq k.+2 3) !odd_add odd_mul andbT.
      by rewrite km3E0 addbF.
    have /H : 0 < (inord (a1 + k.+2 %/ 3) : 'I_l.+2) < l.+1.
      rewrite inordK; first by rewrite addn_gt0 a1_gt0.
      by rewrite ltnS ltnW.
    by rewrite ffunE inordK // ltnS ltnW.
  case: eqP => [km3E1|/eqP km3D1].
    rewrite eqn_leq ltnNge /=.
    have a1La1k : a1 < a1 + k.+2 %/3.
      by rewrite -{1}(addn0 a1) ltn_add2l divn_gt0.
    have a1k3Ll : a1 + k.+2 %/ 3 < l.+1.
      move: (ltnW k2L3c).
      rewrite {1}(divn_eq k.+2 3) km3E1 addn1 mulnC ltn_mul2l /=.
      rewrite -(subnK (_ : a1 <= l.+1)) ?(leq_trans a1Ll) //.
      by rewrite addnC ltn_add2r -/c.
    rewrite (_ : apeg _ _ _ = apeg (a1 + k.+2) p1 p3) ; last first.
      by rewrite /pa1 /pa1S /apeg /= odd_add /= negbK; do 2 case: odd.
    rewrite (_ : apeg _ _ _ = apeg (a1 + (k.+2) %/ 3).+1 p1 p3) ; last first.
      rewrite /apeg /= odd_add {1}(divn_eq k.+2 3) !odd_add odd_mul andbT.
      rewrite km3E1 addbT.
      by case: odd => /=.
    case: (sitiHb (a1 + k.+2 %/ 3)) => // [| siH _ _]; first by rewrite a1La1k.
    by move: siH; rewrite a1Max // ltnS ltnW.
  have km3E2 : k.+2 %% 3 = 2.
    by case: (_ %% _) (ltn_mod k.+2 3) km3D0 km3D1 => // [] [|[|]].
  rewrite ifN; last by case: (k : nat) k_gt0.
  have a1La1k : a1 < a1 + k.+2 %/3.
    by rewrite -{1}(addn0 a1) ltn_add2l divn_gt0.
  have a1k3Ll : a1 + k.+2 %/ 3 < l.+1.
    have: k.+2 %/ 3 * 3 < 3 * c.
      rewrite ltnW //.
      move: (ltnW k2L3c).
      by rewrite {1}(divn_eq k.+2 3) km3E2 addn2.
    rewrite mulnC ltn_mul2l /=.
    rewrite -(subnK (_ : a1 <= l.+1)) ?(leq_trans a1Ll) //.
    by rewrite addnC ltn_add2r -/c.
  rewrite (_ : apeg _ _ _ = apeg (a1 + k.+2) p1 p3) ; last first.
    by rewrite /pa1 /pa1S /apeg /= odd_add /= negbK; do 2 case: odd.
  rewrite (_ : apeg _ _ _ = apeg (a1 + (k.+2) %/ 3) p1 p3) ; last first.
    rewrite /apeg /= odd_add {1}(divn_eq k.+2 3) !odd_add odd_mul andbT.
    rewrite km3E2 addbF.
    by case: odd => /=.
  apply: codom_subC.
  case: (sitiHb (a1 + k.+2 %/ 3)) => // [| _ tiH _]; first by rewrite a1La1k.
  by move: tiH; rewrite a1Max // a1La1k ltnS ltnW.
have c_gt0 : 0 < c by rewrite ltnW.
have P8 :
  (S_[(3 * c).-2] n.+1).*2 <=
  \sum_(i < (3 * c).-2)  d[u2 (inord i.+2), u2 (inord i.+3)] +
  \sum_(k < n.+1) (ta1 k != pa1) * beta n.+1 (3 * c).-2 k +
  \sum_(k < n.+1)
      ((cunliftr (u ord_max)) k != apeg l.+1 p1 p3) *
          beta n.+1 (3 * c).-2 k .
  apply: leq_trans (IH _ _ _ _ _ _ _ cH8) _; rewrite /pa1 /pa1S {cH8}//.
  - by rewrite /apeg /=; case: odd; rewrite // eq_sym.
  - by rewrite eq_sym.
  repeat apply: leq_add; rewrite leq_eqVlt; apply/orP; left; apply/eqP.
  - apply: eq_bigr => i _.
    by rewrite ![u2r _]ffunE !inordK // ltnS // ltnW.
  - apply: eq_bigr => i _; congr ((_ != _) * _).
    rewrite !ffunE /= !inordK //=.
    by rewrite (leq_trans (_ : 2 < (3 * 1).+1)) // ltnS leq_mul2l ltnW.
  apply: eq_bigr => i _; congr ((_ != _) * _).
    rewrite !ffunE /= !prednK ?muln_gt0 //=; last first.
      by rewrite -subn1 ltn_subRL addn0 (leq_trans (_ : _ < 3 * 1)) //
                 leq_mul2l.
    rewrite inordK // mod3E /= div3E addnC subnK; last first.
      by apply: (leq_trans a1Ll).
    by rewrite ffunE; congr (u _ _ ); apply/val_eqP; rewrite /= inordK.
  rewrite /pa1 /pa1S -(subnK (_ : a1 <= l.+1)) // -/c.
    rewrite -subn2 /apeg odd_sub.
      by rewrite odd_mul /= odd_add; case: odd => //=.
    by rewrite (leq_trans (_ : _ < 3 * 1)) // leq_mul2l //.
  by rewrite ltnW.
rewrite {cH8}//.
have l_gt0 : 0 < l.
  by rewrite -ltnS l1E aE1 add1n addSn ltnS addn_gt0 c_gt0 orbT.
have c3m2_gt1 : 1 < (3 * c).-2.
  by rewrite -subn2 ltn_subRL -[2 +1]/(3 * 1) ltn_mul2l.
have {}P8 := leq_trans P8 (leq_add (leq_add (leqnn _) (leqnn _))
                      (leq_sum_beta _ _)).
set y7S := \sum_(_ < n.+1) _ in P8; set y8S := \sum_(_ < n.+1) _ in P8.
rewrite !sum_beta_S // KH1 KH2 !eqxx !addn0 -/y8S.
rewrite (_ : \sum_(_ < _) _ =
  \sum_(i < a)  d[u (inord i), u (inord i.+1)] +
  \sum_(a <= i < a1)  d[u (inord i), u (inord i.+1)] +
  \sum_(a1 <= i < l.+1)  d[u (inord i), u (inord i.+1)]); last first.
  rewrite -[X in _ = X + _ + _](big_mkord xpredT 
                (fun i => d[u (inord i), u (inord i.+1)])).
  by rewrite -!big_cat_nat ?big_mkord //= ltnW.
rewrite -{}P1 -{}P2.
move: P3 => P3.
rewrite -2!addnA.
apply: leq_trans (leq_add (leq_add (leqnn _) P3) (leqnn _)); rewrite {P3}//.
have du2E : d[↓[u (inord a1)], sa1] +  d[sa1, ta1] =
             \sum_(i < 2)  d[u2 (inord i), u2 (inord i.+1)].
  rewrite !big_ord_recr /= big_ord0 !ffunE !inordK //= ?addn0 //.
    by rewrite ltnW // ltnS (leq_mul2l 3 1).
  by rewrite ltnS muln_gt0.
rewrite (_ : \sum_(_ < 3 * c) _ =
  (d[↓[u (inord a1)], sa1] + d[sa1, ta1]) +
  \sum_(i <  (3 * c).-2)  d[u2 (inord i.+2), u2 (inord i.+3)]); last first.
  rewrite du2E.
  rewrite -!(big_mkord xpredT 
                (fun i => d[u2 (inord i), u2 (inord i.+1)])).
  rewrite -!(big_mkord xpredT 
                (fun i => d[u2 (inord i.+2), u2 (inord i.+3)])).
  rewrite[X in _ = _ + X] (eq_bigr
                (fun i => d[u2 (inord (i + 2)), u2 (inord (i + 2).+1)])); 
    last by move=> i_; rewrite !addn2.
  rewrite -subn2.
  have <- := big_addn _ _ _ xpredT (fun i => d[u2 (inord i), u2 (inord i.+1)]).
  rewrite -big_cat_nat //.
  by rewrite ltnW // (leq_mul2l 3 1).
set x3S := \sum_(_ < _) _ in P8; rewrite -/x3S.       
have [|b_gt0] := leqP b 0; last first.
  have cH1 (k : 'I_(3 * a).+1) : 
    0 < k < 3 * a -> codom (u1 k) \subset [:: p3; apeg k p1 p2].
    move=> /andP[k_gt0 k_ltb].
    rewrite {2}aE1 muln1 in k_ltb.
    rewrite ffunE !modn_small // !divn_small // inord_eq0 //.
    rewrite [in 3 * a.-1]aE1 /=.
    case: (k : nat) k_gt0 k_ltb => //= [] [|[|]] //= _ _.
      by have := sam1C; rewrite /pa aE1 /apeg /=.
    by apply: codom_subC.
  set x0S := \sum_(i < 3 * a) _.
  have P4 : 
    (S_[3 * a] n.+1).*2 <= x0S +
    \sum_(k < n.+1) (↓[u ord0] k != p1) * beta n.+1 3 k +
    \sum_(k < n.+1) (↓[u (inord a)] k != p2) * beta n.+1 3 k.
    apply: leq_trans (IH _ _ _ _ _ _ _ cH1) (leq_add (leq_add _ _) _);
        rewrite // 1?eq_sym //.
      by apply: leq_sum => i _; rewrite ffunE /= inord_eq0 // aE1 muln1.
    by apply: leq_sum => i _; rewrite ffunE /= mod3E /= div3E // aE1 muln1.
  have {}P4 := leq_trans P4 (leq_add (leq_add (leqnn _) (leq_sum_beta _ _))
                        (leqnn _)).
  set y0S := \sum_(_ < _) _ in P4; set y1S := \sum_(_ < _) _ in P4.
  have [b_gt1|b_le2] := leqP 2 b.
    pose u3 := [ffun i => ↓[u (inord ((i : 'I_b.+1) + a))]].
    pose paS := apeg a.+1 p1 p3.
    have cH6 (k : 'I_b.+1) :
        0 < k < b -> codom (u3 k) \subset [:: p2; apeg k pa paS].
      move=> /andP[k_gt0 kLb].
      have kBound : 0 < k + a < l.+1.
        rewrite (leq_trans a_gt0) ?leq_addl //=.
        move: kLb; rewrite /b ltn_subRL addnC => /leq_trans-> //.
        by rewrite ltnW.
      rewrite ffunE codom_liftr //.
      have := @cH (inord (k + a)).
      rewrite /pa /paS /apeg /= !inordK //; last first.
        by rewrite ltnW // ltnS; case/andP: kBound.
      by rewrite odd_add //=; do 2 case: odd => //=; apply.
    have {cH6}P6 : 
    (S_[b] n.+1).*2 <=
      \sum_(i5 < b)  d[u3 (inord i5), u3 (inord i5.+1)] +
      \sum_(k < n.+1) (u3 ord0 k != pa) * beta n.+1 b k +
      \sum_(k < n.+1) (u3 ord_max k != apeg b pa paS) * beta n.+1 b k.
      apply: IH cH6 => //; try by rewrite /pa /paS // eq_sym.
      by rewrite /pa /paS /apeg /=; case: odd; rewrite // eq_sym.
    set x1S := \sum_(_ <= _ < _) _.
    rewrite !ffunE [\sum_(_ < _) _](_ : _ = x1S) in P6; last first.
      rewrite /x1S -[a]add0n big_addn -/b big_mkord.
      by apply: eq_bigr => i _; rewrite !ffunE !inordK ?ltnS // ltnW.
    rewrite add0n subnK // in P6.
    set y2S := \sum_(_ < n.+1) _ in P6; set y3S := \sum_(_ < n.+1) _ in P6.
    have aLl : a <= l by apply: leq_trans aLa1 _.
    have y1Sy2SE : y1S + y2S <= (S_[1] n).*2 + α_[maxn 3 b] n.
      apply: sum_alpha_diffE => //; first by rewrite /pa eq_sym.
      apply/codom_liftr.
      have /cH : 0 < (inord a : 'I_l.+2) < l.+1 by rewrite inordK // a_gt0.
      by rewrite inordK // aE1  /=.
    pose u5 := [ffun i : 'I_3 =>
                     if i == 0 :> nat then ↓[u (inord a1)]
                     else if i == 1 :> nat then sa1 else ta1].
    have cH7 (k : 'I_3) : 
      0 < k < 2 -> codom (u5 k) \subset [:: p1; apeg k p2 p3].
      move=> /andP[k_gt0 k_lt2].
      rewrite !ffunE.
      by have ->/= : k = 1 :> nat by case: (k : nat) k_gt0 k_lt2 => // [] [|].
    have P7 : 
      (S_[2] n.+1).*2 <=
      (d[↓[u (inord a1)], sa1] + d[sa1, ta1]) +
      \sum_(k < n.+1) (↓[u (inord a1)] k != p2) * beta n.+1 2 k +
      \sum_(k < n.+1) (ta1 k != p2) * beta n.+1 2 k.
      apply: (leq_trans (IH _ _ _ _ _ _ _ cH7)) => //.
        by rewrite eq_sym.
      repeat apply: leq_add; rewrite leq_eqVlt; apply/orP; left; apply/eqP.
      - by rewrite !big_ord_recr big_ord0 !ffunE !inordK /=.
      - by apply: eq_bigr => i _; rewrite !ffunE.
      by apply: eq_bigr => i _; rewrite !ffunE.
    set x2S := (d[_, _] + d[_, _]); rewrite -/x2S in P7.
    set y4S := \sum_(_ < _) _ in P7; set y5S := \sum_(_ < _) _ in P7.
    have y3Sy4SE : y3S + y4S <= (S_[1] n).*2 + α_[maxn b 2] n.
      apply: sum_alpha_diffE => //.
        by rewrite /pa /paS /apeg /=; do 2 case: odd; rewrite // eq_sym.
      apply: codom_liftr.
      apply: codom_subC.
      have /cH : 0 < (inord a1 : 'I_l.+2) < l.+1.
        by rewrite inordK ?a1_gt0 // ltnS (leq_trans a1Ll).
      rewrite inordK ?ltnS ?(leq_trans a1Ll) //.
      by rewrite /b /pa /paS /apeg odd_sub //=; do 2 case: odd.
    rewrite (maxn_idPl _) // in y3Sy4SE.
    have y5Sy7SE : y5S + y7S <= (S_[1] n).*2 + α_[maxn 2 (3 * c).-2] n.
      by apply: sum_alpha_diffE => //; first by rewrite /pa1 eq_sym.
    rewrite (maxn_idPr _) // in y5Sy7SE.
    rewrite -/y0S.
    move: P4 P6 P7 P8 => P4 P6 P7 P8.
    rewrite -(leq_add2r y1S).
    rewrite [X in _ <= X](_ : _ = 
      a.*2 + x1S + c.*2 + x2S + x3S + y8S + (x0S + y0S + y1S)); last by ring.
    apply: leq_trans (leq_add (leqnn _) P4); rewrite {P4}//.
    rewrite -(leq_add2r (y2S + y3S)).
    rewrite [X in _ <= X](_ : _ = 
      a.*2 + c.*2 + x2S + x3S + y8S + (S_[3 * a] n.+1).*2 + (x1S + y2S + y3S));
      last by ring.
    apply: leq_trans (leq_add (leqnn _) P6); rewrite {P6}//.
    rewrite -(leq_add2r (y4S + y5S)).
    rewrite [X in _ <= X](_ : _ = 
      a.*2 + c.*2 + x3S + y8S + (S_[3 * a] n.+1).*2 + (S_[b] n.+1).*2 +
      (x2S + y4S + y5S)); last by ring.
    apply: leq_trans (leq_add (leqnn _) P7); rewrite {P7}//.
    rewrite -(leq_add2r y7S).
    rewrite [X in _ <= X](_ : _ = 
      a.*2 + c.*2 + (S_[3 * a] n.+1).*2 + (S_[b] n.+1).*2 +
      (S_[2] n.+1).*2 + (x3S + y7S + y8S)); last by ring.
    apply: leq_trans (leq_add (leqnn _) P8); rewrite {P8}//.
    rewrite [X in X <= _](_ : _ =
      (S_[l.+1] n.+2).*2 + (y1S + y2S) + (y3S + y4S) + (y5S + y7S));
      last by ring.
    apply: leq_trans (leq_add (leqnn _) y5Sy7SE) _.
    rewrite {y5Sy7SE}addnC addnA.
    apply: leq_trans (leq_add (leqnn _) y3Sy4SE) _.
    rewrite {y3Sy4SE}addnC 2!addnA.
    apply: leq_trans (leq_add (leqnn _) y1Sy2SE) _.
    rewrite aE1 muln1 -[1.*2]/2.
    have F1 := dsum_alphaL_S (3 * c).-2 n.
    rewrite -[(S_[(3 * c).-2] n.+1).*2]addnn {2}F1 {F1}!addnA.
    rewrite [X in X <= _](_ : _ = 
       6 * (S_[1] n) + α_[b] n + (S_[l.+1] n.+2).*2 +
       α_[maxn 3 b] n + α_[(3 * c).-2] n); last by rewrite -!mul2n; ring.
    rewrite leq_add2r.
    have F2 i k : 0 < i -> S_[i.-1] k.+1 <= S_[(3 *i).-2] k + i.-1.
      move=> i_gt0; apply: leq_trans (dsum_alpha3l _ _) _.
      rewrite leq_add2r.
      apply: (increasingE (increasing_dsum_alphaL_l _)).
      by rewrite -{2}[i]prednK // mulnS addSn add2n /=.
    have F2n := F2 c n c_gt0.
    have F2n1 := F2 c n.+1 c_gt0.
    have F3 : c = c.-1.+1 by rewrite prednK.
    rewrite {}[in c.*2]F3.
    rewrite [X in _ <= X](_ : _ = 
       4 + (S_[3] n.+1).*2 + (S_[b] n.+1).*2 + (S_[2] n.+1).*2 +
      ((S_[(3 * c).-2] n.+1 + c.-1) + (S_[(3 * c).-2] n + c.-1)));
      last by rewrite -!mul2n; ring_simplify.
    apply: leq_trans (leq_add (leqnn _) (leq_add F2n1 F2n)).
    rewrite {F2n1 F2n F2}//.
    have l_gt1 : 1 < l.
      by rewrite -ltnS l1E aE1 add1n addSn ltnS (leq_trans b_gt1) // leq_addr.
    have F4 := SH l_gt1.
    rewrite addnAC addnA.
    apply: leq_trans (leq_add (leqnn _) F4) _; rewrite {F4}//.
    have cB1_gt0 : 0 < c.-1 by rewrite -ltnS prednK.
    have F5 : S_[l.+1] n.+2 + S_[1] n.+2 <= S_[c.-1] n.+2 + S_[b.+3] n.+2.
      rewrite [X in _ <= X]addnC.
      rewrite (_ : l.+1 =  1 + c.-2 + b.+2); last first.
        by rewrite l1E aE1 !add1n -addSnnS !prednK // addnC.
      rewrite (_ : c.-1 = 1 + c.-2); last first.
         by rewrite add1n prednK // -ltnS prednK.
      by apply: concaveEk1 (concave_dsum_alphaL_l n.+2).
    have F6 : S_[l] n.+1 + S_[1] n.+1 <= S_[c.-1] n.+1 + S_[b.+2] n.+1.
      rewrite [X in _ <= X]addnC.
      rewrite (_ : l =  1 + c.-2 + b.+1); last first.
        rewrite -[l]/(l.+1.-1) l1E aE1.
        by rewrite !add1n -addSnnS !prednK // addnC addnS.
      rewrite (_ : c.-1 = 1 + c.-2); last first.
         by rewrite add1n prednK // -ltnS prednK.
      by apply: concaveEk1 (concave_dsum_alphaL_l n.+1).
    rewrite -(leq_add2r (S_[b.+2] n.+1)) -[X in _ <= X]addnA.
    apply: leq_trans (leq_add (leqnn _) F6); rewrite {F6}//.
    rewrite -[X in _ <= X]addnC !addnA.
    rewrite -(leq_add2r (S_[b.+3] n.+2)) -[X in _ <= X]addnA.
    apply: leq_trans (leq_add (leqnn _) F5); rewrite {F5}//.
    rewrite [X in X <= _](_ : _ = 
      6 * S_[1] n + α_[b] n + α_[maxn 3 b] n + (α_[1] n.+1).*2 + 
      S_[b.+2] n.+1 + S_[b.+3] n.+2 + (S_[l.+1] n.+2 + S_[l] n.+1));
      last by ring.
    rewrite [X in _ <= X](_ : _ = 
      S_[1] n.+1 + 4 + (S_[3] n.+1).*2 + (S_[b] n.+1).*2 +
      (S_[2] n.+1).*2 + S_[1] n.+2 + (S_[l.+1] n.+2 + S_[l] n.+1)); 
      last by ring.
    rewrite leq_add2r.
    have [b_gt2|b_le3] := leqP 3 b.
      rewrite (maxn_idPr _) //.
      have F7 := dsum_alphaL_S b n.
      rewrite {}F7.
      rewrite [X in X <= _](_ : _ = 
        6 * S_[1] n + (α_[1] n.+1).*2 + S_[b.+2] n.+1 +
        S_[b.+3] n.+2 + (α_[b] n + α_[b] n)); last by ring.
      rewrite [X in _ <= X](_ : _ = 
        S_[1] n.+1 + 4 + (S_[3] n.+1).*2 + (S_[b] n).*2 + (S_[2] n.+1).*2 +
        S_[1] n.+2 + (α_[b] n + α_[b] n)); last by rewrite -!mul2n; ring.
      rewrite leq_add2r.
      have F8 : S_[b.+3] n.+2 <= S_[b.+2] n.+1 + (α_[1] n.+1).*2.
        by rewrite alphaL1E; apply: dsum_alphaL_alpha.
      apply: leq_trans (leq_add (leqnn _) F8) _.
      rewrite addnAC.
      have F9 : S_[b.+1] n.+1 <= S_[b] n + (α_[1] n).*2.
        by rewrite alphaL1E; apply: dsum_alphaL_alpha.
      rewrite -(leq_add2r (4 * α_[1] n)).
      rewrite [X in _ <= X](_ : _ = 
        S_[1] n.+1 + 4 + (S_[3] n.+1).*2 + (S_[2] n.+1).*2 +
        S_[1] n.+2 + ((S_[b] n + (α_[1] n).*2) + (S_[b] n + (α_[1] n).*2))); 
          last by rewrite -!mul2n; ring.
      apply: leq_trans (leq_add (leqnn _) (leq_add F9 F9)).
      have F10 : S_[1] n.+1 + S_[b.+2] n.+1 <= S_[b.+1] n.+1 + S_[2] n.+1.
        rewrite addnC -[b.+2]/(1 + 1 + b).
        by apply: concaveEk1 (concave_dsum_alphaL_l n.+1).
      rewrite [X in _ <= X](_ : _ = 
        S_[1] n.+1 + 2 + ((S_[3] n.+1).+1).*2 + S_[1] n.+2 +
        ((S_[b.+1] n.+1 + S_[2] n.+1) + (S_[b.+1] n.+1 + S_[2] n.+1)));
         last by rewrite -!mul2n; ring.
      apply: leq_trans (leq_add (leqnn _) (leq_add F10 F10)).
      have F11 := dsum_alpha3_S n.+1.
      rewrite -F11.
      have F12 := dsum_alphaL_S 1 n.+1.
      rewrite F12.
      have F13 := dsum_alphaL_S 1 n.
      rewrite !F13.
      rewrite [X in X <= _](_ : _ = 
        α_[1] n.+1 + (6 * S_[1] n + 3 * α_[1] n.+1 + 4 * α_[1] n + 
        2 * S_[b.+2] n.+1)); last by rewrite -!mul2n; ring.
      rewrite [X in _ <= X](_ : _ = 
        2 + 2 * α_[1] n + (6 * S_[1] n + 3 * α_[1] n.+1 + 4 * α_[1] n + 
        2 * S_[b.+2] n.+1)); last by rewrite -!mul2n; ring.
      rewrite leq_add2r.
      have F14 := alphaL_1_2 n.
      by apply: leq_trans F14 _; rewrite mul2n leq_addl.
    have bE2 : b = 2.
      by case: (b) b_gt1 b_le3 => // [] [|[|]].
    rewrite bE2 -[maxn 3 2]/3.
    rewrite -![in X in _ <= X]addnn.
    have F1 := dsum_alphaL_S 2 n.
    rewrite {1}F1.
    have F2 := dsum_alphaL_S 3 n.
    rewrite {1}F2.
    have F3 : S_[5] n.+2 <= S_[4] n.+1 + (α_[1] n.+1).*2.
      by rewrite alphaL1E; apply: dsum_alphaL_alpha.
    apply: leq_trans (leq_add (leqnn _) F3) _.
    rewrite [X in X <= _](_ : _ = 
      6 * S_[1] n + α_[2] n + α_[3] n + (α_[1] n.+1).*2 +
      (α_[1] n.+1).*2 + (S_[4] n.+1 + S_[4] n.+1)); last by ring.
    have F4 : S_[4] n.+1 <= S_[3] n + (α_[1] n).*2.
      by rewrite alphaL1E; apply: dsum_alphaL_alpha.
    apply: leq_trans (leq_add (leqnn _) (leq_add F4 F4)) _.
    rewrite -ltnS.
    rewrite [X in X <= _](_ : _ =
      6 * S_[1] n + 4 * (α_[1] n.+1) + 4 * (α_[1] n) + (S_[3] n).+1 +
      (S_[3] n + α_[2] n + α_[3] n)); last by rewrite -!mul2n; ring.
    rewrite [X in _ <= X](_ : _ =
     S_[1] n.+1 + 4 + S_[2] n + 3 * (S_[2] n.+1) + S_[1] n.+2 +
    (S_[3] n.+1).+1 + (S_[3] n + α_[2] n + α_[3] n)); last by ring.
    rewrite leq_add2r.
    have F5 := dsum_alpha3_S n.+1.
    rewrite -F5.
    have F6 := dsum_alpha3_S n.
    rewrite -F6.
    rewrite -leq_double.
    have F7 := leq_dsum_alpha_2l_1 n.+1.
    have F8 := leq_dsum_alpha_2l_1 n.
    rewrite [X in _ <= X](_ : _ =
      2 * S_[1] n.+1 + 4 + 4 * S_[1] n.+2 +
      (((S_[2] n).*2.+1 + (S_[2] n.+1).*2.+1) +    
       ((S_[2] n.+1).*2.+1 + (S_[2] n.+1).*2.+1)));
         last by rewrite -!mul2n; ring.
    apply: leq_trans (leq_add (leqnn _) 
            (leq_add (leq_add F8 F7) (leq_add F7 F7))).
    have F9 := dsum_alphaL_S 1 n.+1.
    have F10 := dsum_alphaL_S 1 n.
    rewrite !(F9, F10).
   rewrite [X in X <= _](_ : _ = 
      α_[1] n.+1 +
      (14 * S_[1] n + 7 * α_[1] n.+1 + 10 * α_[1] n)); 
      last by rewrite -!mul2n; ring.
    rewrite [X in _ <= X](_ : _ = 
      (α_[1] n).*2 + (α_[1] n + 4) +
      (14 * S_[1] n + 7 * α_[1] n.+1 + 10 * α_[1] n)); 
      last by rewrite -mul2n; ring.
    rewrite leq_add2r.
    have F11 := alphaL_1_2 n.
    by apply: leq_trans F11 (leq_addr _ _).
  have bE1 : b = 1.
    by case: (b) b_gt0 b_le2 => // [] [|].
  have a1E2 : a1 = 2.
    by move: bE1; rewrite /b aE1; case: (a1) => // [] [|[]].
  pose u3 := 
    [ffun i : 'I_4 =>  
    if i == 0 :> nat then ↓[u (inord a)] else
    if i == 1 :> nat then ↓[u (inord a1)] else
    if i == 2 :> nat then sa1 else ta1].
  set x1S := \sum_(_ <= _ < _) _.
  set d1 := d[_, _] + d[_, _].
  rewrite -/y0S.
  rewrite [X in _ <= X](_ : _ =
    a.*2 + x0S + c.*2 + x3S + y0S + y8S + (x1S + d1)); last by ring.
  have -> : x1S + d1 = \sum_(i < 3) d[u3 (inord i), u3 (inord i.+1)].
    rewrite /x1S aE1 a1E2 big_nat1 /d1 !big_ord_recr big_ord0 /=.
    by rewrite !ffunE !inordK //= aE1 a1E2 add0n !addnA.
    have l_gt2 : 2 < l by rewrite -ltnS l1E aE1 bE1 !add1n.
  set x6S := \sum_(_ < 3) _.
  have cH6 (k : 'I_4) : 
    0 < k < 3 -> codom (u3 k) \subset [:: pa1; apeg k pa1S p2].
    move=> /andP[k_gt0 k_lt3].
    rewrite !ffunE eqn_leq leqNgt k_gt0 /=.
    case: eqP => [->/=|/eqP kD1].
      apply/codom_liftr/codom_subC.
      have /cH :  0 < (inord a1 : 'I_l.+2 ) < l.+1.
        by rewrite inordK a1E2 // (leq_trans l_gt2).
      by rewrite inordK // a1E2 (leq_trans l_gt2) // ltnW.
    have -> : k = 2 :> nat.
      by case: (k : nat) k_gt0 k_lt3 kD1 => // [] [|[]].
    have := sa1C; rewrite eqxx /pa1 /pa1S /apeg /=; case: odd => //=.
    by move=> /codom_subC.
  have P6 : 
    (S_[3] n.+1).*2 <=
    x6S +
    \sum_(k < n.+1) (u3 ord0 k != pa1S) * beta n.+1 3 k +
    \sum_(k < n.+1) (u3 ord_max k != p2) * beta n.+1 3 k.
    apply: IH cH6; rewrite /pa1S /pa1 //.
    by rewrite a1E2 eq_sym.
  rewrite !ffunE /= in P6.
  set y2S := \sum_(_ < _) _ in P6; set y3S := \sum_(_ < _) _ in P6.
  have y1Sy2SE : y1S + y2S <= (S_[1] n).*2 + α_[3] n.
    apply: sum_alpha_diffE => //; first by rewrite eq_sym /pa1S a1E2.
    have /H : 0 < (inord a : 'I_l.+2) < l.+1; first by rewrite inordK // aE1.
    by rewrite ffunE inordK // /pa1S /= aE1 a1E2.
  have lEc : l = c.+1 by rewrite -[l]/l.+1.-1 l1E aE1 bE1.
  rewrite lEc.
  have y3Sy7SE : y3S + y7S <=  (S_[1] n).*2 + α_[maxn 3 (3 * c).-2] n.
    by apply: sum_alpha_diffE => //; first by rewrite /pa1 a1E2 eq_sym.
  rewrite (maxn_idPr _) in y3Sy7SE; last first.
    by rewrite -subn2 ltn_subRL ltnW // (leq_mul2l 3 2).
  move: P4 P6 P8 => P4 P6 P8.
  rewrite -(leq_add2r y1S).
  rewrite [X in _ <= X](_ : _ =
    a.*2 + c.*2 + x3S + y8S + x6S + (x0S + y0S + y1S));
    last by ring.
  apply: leq_trans (leq_add (leqnn _) P4); rewrite {P4}//.
  rewrite -(leq_add2r (y2S + y3S)).
  rewrite [X in _ <= X](_ : _ =
    a.*2 + c.*2 + x3S + y8S + (S_[3 * a] n.+1).*2 +
    (x6S + y2S + y3S)); last by ring.
  apply: leq_trans (leq_add (leqnn _) P6); rewrite {P6}//.
  rewrite -(leq_add2r y7S).
  rewrite [X in _ <= X](_ : _ =
    a.*2 + c.*2 + (S_[3 * a] n.+1).*2 + (S_[3] n.+1).*2 + 
    (x3S + y7S + y8S)); last ring.
  apply: leq_trans (leq_add (leqnn _) P8); rewrite {P8}//.
  rewrite aE1 muln1 -[1.*2]/2.
  rewrite [X in X <= _](_ : _ =
    (S_[c.+2] n.+2).*2 + ((y1S + y2S) + (y3S + y7S))); last by ring.
  apply: leq_trans (leq_add (leqnn _) (leq_add y1Sy2SE y3Sy7SE)) _.
  rewrite -![in X in _ <= X]addnn.
  have F1 := dsum_alphaL_S 3 n.
  rewrite {1}F1.
  have F2 := dsum_alphaL_S (3 * c).-2 n.
  rewrite {1}F2.
  have F4 k : S_[c.-1] k.+1 <= S_[(3 *c).-2] k + c.-1.
    apply: leq_trans (dsum_alpha3l _ _) _.
    rewrite leq_add2r.
    apply: (increasingE (increasing_dsum_alphaL_l _)).
    by rewrite -{2}[c]prednK // mulnS addSn add2n /=.
  have F4n := F4 n.
  have F4n1 := F4 n.+1.
  have F5 := prednK c_gt0.
  rewrite -[in (c + c)]F5.
  rewrite [X in X <= _](_ : _ =
    (S_[c.+2] n.+2).*2 + 4 * (S_[1] n) + (α_[3] n + α_[(3 * c).-2] n));
    last by rewrite -!mul2n; ring.
  rewrite [X in _ <= X](_ : _ = 
    4 + S_[3] n + 3 * S_[3] n.+1 + ((S_[(3 * c).-2] n + c.-1) + 
    (S_[(3 * c).-2] n.+1 + c.-1)) + (α_[3] n + α_[(3 * c).-2] n));
       last by ring.
  rewrite leq_add2r.
  apply: leq_trans (leq_add (leqnn _) (leq_add F4n F4n1)).
  have l_gt1 : 1 < l by rewrite lEc.
  have F6 : (S_[c.+2] n.+2).*2 <= S_[c.+2] n.+2 + S_[c.+1] n.+1 + (α_[1] n.+1).*2.
    by have := (SH l_gt1); rewrite lEc.
  apply: leq_trans (leq_add F6 (leqnn _)) _.
  have F7 : S_[c.+2] n.+2 + S_[1] n.+2 <= S_[c.-1] n.+2 + S_[4] n.+2.
    rewrite (_ : c.+2 =  1 + 3 + c.-2); last first.
      by rewrite !addSn add0n !prednK ?addn2 // -ltnS prednK.
    rewrite {2}(_ : c.-1 = 1 + c.-2); last first.
      by rewrite add1n prednK // -ltnS prednK.
    by apply: concaveEk1 (concave_dsum_alphaL_l n.+2).
  have F8 : S_[c.+1] n.+1 + S_[1] n.+1 <= S_[c.-1] n.+1 + S_[3] n.+1.
    rewrite (_ : c.+1 =  1 + 2 + c.-2); last first.
      by rewrite !addSn add0n !prednK ?addn2 // -ltnS prednK.
    rewrite {2}(_ : c.-1 = 1 + c.-2); last first.
      by rewrite add1n prednK // -ltnS prednK.
    by apply: concaveEk1 (concave_dsum_alphaL_l n.+1).
  rewrite -(leq_add2r (S_[1] n.+2 + S_[1] n.+1)).
  rewrite [X in X <= _](_ : _ = 
    (α_[1] n.+1).*2 + 4 * S_[1] n + 
    ((S_[c.+2] n.+2 + S_[1] n.+2) + (S_[c.+1] n.+1 + S_[1] n.+1)));
    last by ring.
  apply: leq_trans (leq_add (leqnn _) (leq_add F7 F8)) _.
  rewrite [X in X <= _](_ : _ = 
    (α_[1] n.+1).*2 + 4 * S_[1] n + S_[3] n.+1 + S_[4] n.+2 +
    (S_[c.-1] n.+2 + (S_[c.-1] n.+1))); last by ring.
  rewrite [X in _ <= X](_ : _ = 
    4 + S_[3] n + 3 * S_[3] n.+1 + S_[1] n.+2 + S_[1] n.+1 +
    (S_[c.-1] n.+2 + S_[c.-1] n.+1)); last by ring.
  rewrite leq_add2r. 
  have F9 : S_[4] n.+2 <= S_[3] n.+1 + (α_[1] n.+1).*2.
    by rewrite alphaL1E; apply: dsum_alphaL_alpha.
  apply: leq_trans (leq_add (leqnn _) F9) _.
  have F10 := dsum_alpha3_S n.
  have F11 := dsum_alpha3_S n.+1.
  rewrite -ltnS.
  rewrite [X in X <= _](_ : _ =
    4 * α_[1] n.+1 + 4 * S_[1] n + (S_[3] n.+1).+1 + S_[3] n.+1);
    last by rewrite -!mul2n; ring.
  rewrite [X in _ <= X](_ : _ =
    2 + (S_[3] n).+1 + 2 * (S_[3] n.+1).+1 + S_[1] n.+2 + S_[1] n.+1 +
    S_[3] n.+1); last by ring.
  rewrite leq_add2r -F10 -F11.
  have F12 := dsum_alphaL_S 1 n.+1.
  have F13 := dsum_alphaL_S 1 n.
  rewrite F12 F13.
  rewrite [X in X <= _](_ : _ = 
    (α_[1] n.+1).*2 + (3 * α_[1] n.+1 + 5 * S_[1] n + α_[1] n)); 
      last by rewrite -!mul2n; ring.
  rewrite [X in _ <= X](_ : _ =
    (1 +  (α_[1] n).*2).*2 + (3 * α_[1] n.+1 + 5 * S_[1] n + α_[1] n)); 
    last by rewrite -!mul2n; ring.
  rewrite leq_add2r leq_double.
  have F14 := alphaL_1_2 n.
  apply: leq_trans F14 (leq_addl _ _).
rewrite leqn0 => /eqP bE0.
have a1Ea : a1 = a by rewrite -(subnK aLa1) -/b bE0.
rewrite big_geq ?a1Ea // addn0.
have lEc : l = c by rewrite -[l]/(l.+1.-1) l1E aE1 bE0.
rewrite {1}lEc.
set d1 := d[_, _] + d[_, _].
set x0S := \sum_(_ < _) _; set y0S := \sum_(_ < _) _.
rewrite [X in _ <= X](_ : _ =
  a.*2 + c.*2 + x3S + y0S + y8S + (x0S + d1)); last by ring.
Admitted.

End Case3.

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
    rewrite inord_eq0 // (_ : inord 1 = ord_max); last first.
      by apply/val_eqP; rewrite /= inordK.
    rewrite /beta /apeg /= alphaL1E -[_ 0]/1; do 2 case: eqP; rewrite /= ?addn0;
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
    rewrite -H inord_eq0 // u0E /apeg /= inordK //=.
    by rewrite !inE (negPf p1Dp2) (negPf p1Dp3).
  - by rewrite configuration1_eq ffunE inord_eq0 // u0E.
  rewrite configuration1_eq ffunE.
  case: eqP => // H.
  have /cH :  0 < (inord 1 : 'I_l.+3) < l.+2 by rewrite inordK /=.
  move=> /subsetP/(_ _ (codom_f _ d0)).
  rewrite H !inE eq_sym (negPf p2Dp0) /apeg /=; case: odd => /=.
    by rewrite eq_sym (negPf p3Dp0).
  by rewrite eq_sym (negPf p1Dp0).
case: l u cH => [|l] u cH; first by rewrite S0E.
pose u' : {ffun 'I_l.+2 -> configuration 4 n.+1} :=
     [ffun i : 'I_l.+2 => ↓[u i]].
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
  by rewrite mul1n /beta /= /alphaL /delta !S1E.
rewrite negb_or negb_and.
have: K <= 2 by rewrite /K; do 2 case: (_ != _).
case: ltngtP; rewrite // ltnS.
case: ltngtP => //= KE _ _ l_gt0; last first.
  move: KE; rewrite /K.
  (case: eqP => [KH1|/eqP KH1] /=; case: eqP) => // [/eqP KH2|KH2] _.
    by apply: (@case1 _ IH) cH KH1 KH2 l_gt0.
  pose u1 : {ffun 'I_l.+2 -> configuration 4 n.+2} := 
     [ffun i : 'I_l.+2 => u (inord (l.+1 - i))].
  have -> : \sum_(i < l.+1)  d[u (inord i), u (inord i.+1)] =
            \sum_(i < l.+1)  d[u1 (inord i), u1 (inord i.+1)].
    have F : injective (fun i : 'I_l.+1 => (inord (l - i) : 'I_l.+1)).
      move=> i j /val_eqP.
      have lBiLl (i1 : 'I_l.+1) : l - i1 < l.+1.
        by rewrite ltn_subLR ?leq_addl // -ltnS.
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
    by rewrite inord_eq0 // /apeg /p3' /p1' /=; case: odd.
  have -> : \sum_(k < n.+2) 
              (u ord_max k != apeg l.+1 p1 p3) * beta n.+2 l.+1 k =
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
  have:= KH1; rewrite /apeg /p3' /p1' /= inord_eq0 //.
  by case: odd.
move: KE; rewrite /K; do 2 case: eqP => //=.
move => uME u0E _.
by apply: (case3 IH (nLm : n < m) _ _ _ _ _ _ cH).
Qed.

End sHanoi4.


