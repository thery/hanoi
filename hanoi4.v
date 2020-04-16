From mathcomp Require Import all_ssreflect.
Require Import tsplit gdist ghanoi triangular phi hanoi3 psi.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Section Hanoi4.

(*****************************************************************************)
(*  The pegs are the three elements of 'I_4                                  *)
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

Lemma split_first (A : eqType) (a : A) (l : seq A) (P : pred A) :
  P a -> ~~ all P l -> exists b, exists l1, exists l2,
    [/\ all P l1, ~~ P b &  l = l1 ++ b :: l2].
Proof.
elim: l a => //= b l IH a aP.
rewrite negb_and; case: (boolP (P b)) => /= bP lNP; last first.
  by exists b; exists nil; exists l; split.
case: (IH _ aP lNP) => c [l1 [l2 [H1 H2 ->]]].
by exists c; exists (b :: l1); exists l2; split; rewrite /= ?bP.
Qed.

Lemma split_last (A : eqType) (a : A) (l : seq A) (P : pred A) :
  P a -> ~~ all P l -> exists b, exists l1, exists l2, exists l3,
    [/\ all (fun i => ~~ P i) (b :: l2), all P l3, P (last a l1) &  
        l = l1 ++ b :: (l2 ++ l3)].
Proof.
move=> aP.
elim/last_ind : l => //= l b IH.
rewrite all_rcons negb_and orbC; case: (boolP (all P l)) => /= [lP bP|lP _].
  exists b; exists l; exists [::]; exists [::]; split; rewrite /= ?bP //.
    elim: (l) (a) aP lP => //= c l1 IH1 d dP /andP[H1 H2].
    by apply: IH1.
  by rewrite cats1.
case: (IH lP) => c [l1 [l2 [l3 [/andP[H1 H2] H3 H4 ->]]]].
case: (boolP (P b)) => /= bP; last first.
  case: l3 H3 => [|d l3] H3.
    exists c; exists l1; exists (rcons l2 b); exists [::]; split => //=.
      by rewrite H1 all_rcons H2 bP.
    by rewrite -!cats1 !cats0 -catA /=.
  exists b; exists (l1 ++ c :: l2 ++ d :: l3); exists [::]; exists [::].
  split=> //=.
  - by rewrite bP.
  - rewrite last_cat /= last_cat /=.
    apply: (allP H3).
    by apply: mem_last.
  by rewrite -!cats1 /= -catA.
exists c; exists l1; exists l2; exists (rcons l3 b); split => //.
- by rewrite H1.
- by rewrite all_rcons bP.
by rewrite -!cats1 /= -catA /= -catA.
Qed.

(* This is theorem 2.9 *)
Lemma phi_2_9 n (u v : configuration 4 n) (p0 p2 p3 : peg 4)
  (E := [set i | u i == p0]) : 
  [/\ p3 != p2, p3 != p0 & p2 != p0] ->
  (codom v) \subset [:: p2 ; p3] -> psi E  <= `d[u, v]_hmove.
Proof.
move=> pH.
suff H k :
 let E := [set i | ((i : 'I_n) < n - k) && (u i == p0)] in 
          (codom v) \subset [:: p2 ; p3] -> psi E  <= `d[u, v]_hmove.
  have ->: E = [set i | ((i : 'I_n) < n - 0) && (u i == p0)].
    by apply/setP => i; rewrite !inE subn0 ltn_ord.
  by apply: H.
elim: n u v k {E}p0 p2 p3 pH =>
    [u v k p0 p2 p3 [p3Dp2 p3Dp0 p2Dp0] E cH |
     n IH u v [|k] p0 p2 p3 [p3Dp2 p3Dp0 p2Dp0] E cH]; first 2 last.
- apply: leq_trans (gdist_cunlift (connect_move _ _)).
  pose N : disk n.+1 := ord_max.
  have->: E = E :\ N.
    apply/setP=> i; rewrite 2![in RHS]inE.
    case: eqP => // ->.
    by rewrite !inE subSS /N /= ltnNge leq_subr.
  rewrite psi_ord_max.
  have -> : [set i | lift ord_max i \in E] =
            [set i | ((i : 'I_n) < n - k) && (↓[u] i == p0)].
    apply/setP => i; rewrite !inE /= !ffunE // trshift_lift.
    by rewrite subSS /bump [n <= i]leqNgt ltn_ord.
  apply: IH.
    by split; [exact: p3Dp2 | exact: p3Dp0 | exact p2Dp0].
  apply/subsetP=> i /codomP[j]; rewrite !ffunE !inE => ->.
  have /subsetP /(_  (v (trshift 1 j))) := cH.
  rewrite !inE; apply.
  by apply: codom_f.
- suff ->: E = set0 by rewrite psi_set0.
  by apply/setP=> [] [].
pose N : disk n.+1 := ord_max.
have [NiE|NniE] := boolP (N \in E); last first.
  have->: E = E :\ N.
    apply/setP=> i; rewrite 2![in RHS]inE.
    case: eqP => // ->.
    by rewrite (negPf NniE).
  rewrite psi_ord_max.
  apply: leq_trans (gdist_cunlift (connect_move _ _)).
  have -> : [set i | lift ord_max i \in E] =
            [set i | ((i : 'I_n) < n - 0) && (↓[u] i == p0)].
    apply/setP => i; rewrite !inE /= !ffunE // trshift_lift.
    by rewrite !subn0 /bump [n <= i]leqNgt ltn_ord add0n ltnW // ltnS ltn_ord.
  apply: IH.
    by split; [exact: p3Dp2 | exact: p3Dp0 | exact p2Dp0].
  apply/subsetP=> i /codomP[j]; rewrite !ffunE !inE => ->.
  have /subsetP /(_  (v (trshift 1 j))) := cH.
  rewrite !inE; apply.
  by apply: codom_f.
have uN0 : u N = p0 by move: NiE; rewrite inE => /andP[_ /eqP].
(* maybe I should do a wlog *)
pose np2 : peg _ := v N.
have vN2 : v N = np2 by [].
pose np3 : peg _ := if np2 == p2 then p3 else p2.
have np2Dp0 : np2 != p0.
  have /subsetP /(_  (v N)) := cH.
  by rewrite /np2 !inE =>  /(_ (codom_f v N))/orP[]/eqP->.
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
have /gdist_path [g [gH1 gH2 gH3 <-]] := connect_move u v.
have vIg : v \in g.
  by have := mem_last u g; rewrite inE gH2 eq_sym (negPf uDv).
pose E' := [set i | [exists c, (c \in (u :: g)) && (c i == np3) ]] :&: E.
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
  apply: leq_trans (gdist_cproj F aH gH2 gH1).
  have -> : cproj E p0Isp u = `c[enum_rank_in p0Isp p0].
    apply/ffunP=> i.
    rewrite !ffunE; congr (enum_rank_in _ _).
    by have := enum_valP i; rewrite !inE subn0 ltn_ord; apply/eqP.
  have -> : cproj E p0Isp v = `c[enum_rank_in p0Isp np2].
    apply/ffunP=> i.
    rewrite !ffunE; congr (enum_rank_in _ _).
    have := subsetP cH (v (enum_val i)); rewrite !inE codom_f => /(_ isT).
    case/orP=> /eqP //.
    have /eqP/setP/(_ (enum_val i)) := Ez.
    have := enum_valP i.
    rewrite !inE => -> /idP/negP; rewrite andbT negb_exists.
    by move=> /forallP/(_ v); rewrite -{1}gH2 mem_last => /= /eqP.
  have : (enum_rank_in p0Isp p0) != (enum_rank_in p0Isp np2).
    rewrite eq_sym; apply/eqP => /enum_rank_in_inj.
    rewrite !inE eq_sym np3Dp2 eq_sym np3Dp0 => /(_ isT isT) H.
    by case/eqP: np2Dp0.
  have U : #|P| = 3.
    have := cardsC [set np3]; rewrite -/P.
    by rewrite cards1 add1n card_ord => [] [].
  move: (enum_rank_in p0Isp p0) (enum_rank_in p0Isp np2).
  rewrite U => u1 v1 u1Dv1.
  rewrite gdist_perfect (negPf u1Dv1) muln1.
  apply: psi_exp.
  rewrite -{5}[n.+1]card_ord.
  by apply: max_card.
rewrite -card_gt0 in EnZ.
case: (eq_bigmax_cond (@nat_of_ord _) EnZ) => /= T TinE' Tmax.
have {}Tmax := sym_equal Tmax.
have uT0 : u T = p0.
  apply/eqP; move: TinE'.
  by rewrite inE => /andP[_]; rewrite inE => /andP[].
pose E'' := [set i in E | i > T].
pose K := #|E''|.
have KTE : T + K < n.+1.
  rewrite -{2}[n.+1]card_ord -addSn.
  pose ST := [set @inord n i | i : 'I_T.+1].
  rewrite -[_ + _]subn0 -(_ : #|ST :&: E''| = 0); last first.
    apply/eqP; rewrite cards_eq0; apply/eqP/setP => i.
    rewrite /ST !inE; apply/idP => /and3P[/imsetP[d _ -> /=] _].
    rewrite inordK; first by rewrite ltnNge -ltnS ltn_ord.
    by apply: leq_trans (ltn_ord _) (ltn_ord _).
  have-> : T.+1 = #|ST| :> nat.
    rewrite card_imset ?card_ord // => i j /val_eqP/=.
    rewrite !inordK //; first by move=> H; apply/val_eqP.
      apply: leq_trans (ltn_ord _) _.
      by apply: leq_trans (ltn_ord _) _.
    apply: leq_trans (ltn_ord _) _.
    by apply: leq_trans (ltn_ord _) _.
  by rewrite -cardsU max_card.
move: TinE'.
rewrite !inE => /andP[/existsP[/= c_p3 /andP[]]].
  rewrite inE => /orP[/eqP->|]; first by rewrite uT0 eq_sym (negPf np3Dp0).
move=> c_p3Ig /eqP c_p3T3 _.
case (@split_first _ u g (fun c : configuration _ _ => c(T) == p0)) => /=.
- by rewrite uT0.
- by apply/negP => /allP /(_  _ c_p3Ig); rewrite c_p3T3 (negPf np3Dp0).
move=> x0s [x0sb [x0sa [/allP x0sbP0 x0pT0 gE]]].
pose x0 := last u x0sb.
have x0T0 : x0 T = p0.
  by have := mem_last u x0sb; rewrite !inE /x0 => /orP[/eqP->|/x0sbP0/eqP].
have x0Mx0s : x0 `--> x0s.
  by move: gH1; rewrite gE cat_path /= -/x0 => /and3P[].
case (@split_first _ x0 (x0s :: x0sa)
                (fun c : configuration _ _ => c(T) != np3)) => /=.
- by rewrite x0T0 eq_sym.
- rewrite negb_and negbK.
  move: c_p3Ig; rewrite gE mem_cat !inE => /or3P[].
  * by move /x0sbP0; rewrite c_p3T3 (negPf np3Dp0).
  * by move/eqP<-; rewrite c_p3T3 eqxx.
  move=> cp3Ix0a; apply/orP; right; apply/negP=> /allP /(_ _ cp3Ix0a).
  by rewrite c_p3T3 eqxx.
move => x3 [x3b [x3a [/allP x3bP0 x3T3 x0xaE]]].
rewrite negbK in x3T3; have /eqP {}x3T3 := x3T3.
pose x3p := last x0 x3b.
have x3pND3 : x3p T != np3.
  have := mem_last x0 x3b; rewrite -/x3p inE => /orP[/eqP->|/x3bP0//].
  by rewrite x0T0 eq_sym.
have x3pMx3 : x3p `--> x3.
  by move: gH1; rewrite gE x0xaE cat_path /= cat_path /= => /and4P[].
case (@split_first _ u g (fun c : configuration _ _ => c(N) == p0)) => /=.
- by rewrite uN0.
- apply/negP => /allP /(_  _ vIg).
  by rewrite vN2 (negPf np2Dp0).
move=> z0s [z0sb [z0sa [/allP z0sbP0 z0sbTD0 gE']]].
pose z0 := last u z0sb.
have z0N0 : z0 N = p0.
  by have := mem_last u z0sb; rewrite !inE /z0 => /orP[/eqP->|/z0sbP0/eqP].
have z0Mz0s : z0 `--> z0s.
   by move: gH1; rewrite gE' cat_path /= => /and3P[].
case (@split_last _ z0 (z0s :: z0sa) 
             (fun c : configuration _ _ => c(N) != np2)) => /=.
- by rewrite z0N0 eq_sym.
- rewrite negb_and negbK.
  move: vIg; rewrite gE' mem_cat !inE => /or3P[].
  * by move /z0sbP0; rewrite vN2 (negPf np2Dp0).
  * by move/eqP<-; rewrite vN2 eqxx.
  move=> vIz0sa; apply/orP; right; apply/negP=> /allP /(_ _ vIz0sa).
  by rewrite vN2 eqxx.
move=> z2 [z2b [z2a1 [z2a2 [/andP[z2N2 /allP z2a1P2] 
                             /allP z2a2PD2 z2pND2 z0sz0saE]]]].
rewrite negbK in z2N2; have /eqP {}z2N2 := z2N2.
pose z2p := last z0 z2b.
rewrite -/z2p in z2pND2.
have z2pMz2 : z2p `--> z2.
  by move: gH1; rewrite gE' z0sz0saE cat_path /= cat_path /= => /and4P[].
Admitted.

End Hanoi4.


