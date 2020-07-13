From mathcomp Require Import all_ssreflect.
From hanoi Require Import gdist ghanoi ghanoi3.

(******************************************************************************)
(*                                                                            *)
(*             Linear Hanoi Problem with 3 pegs                               *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section LHanoi3.

Lemma lrel3D (p1 p2 : peg 3) : p1 != p2 -> lrel p1 p2 || lrel p1 `p[p1, p2].
Proof.
move=> p1Dp2.
have D p3 p4 : (p3 == p4) = (val p3 == val p4).
  by apply/eqP/idP => /val_eqP.
move: p1Dp2 (opegDl p1 p2) (opegDr p1 p2).
by case: (peg3E `p[p1, p2]) => ->;
   case: (peg3E p1) => ->; 
   case: (peg3E p2) => ->; 
   rewrite !D /lrel /= ?inordK.
Qed.

Lemma lrel3B (p1 p2 : peg 3) : p1 != p2 -> 
  ~~ [&& lrel p1 p2, lrel p1 `p[p1, p2] & lrel p2 `p[p1, p2]].
Proof.
have D p3 p4 : (p3 == p4) = (val p3 == val p4).
  by apply/eqP/idP => /val_eqP.
move: (opegDl p1 p2) (opegDr p1 p2).
by case: (peg3E `p[p1, p2]) => ->;
   case: (peg3E p1) => ->; 
   case: (peg3E p2) => ->; 
   rewrite !D /lrel /= ?inordK.
Qed.

Lemma lrel3O (p1 p2 : peg 3) : p1 != p2 -> 
  ~~ lrel p1 p2 -> lrel p1 `p[p1, p2].
Proof. by move/lrel3D; case: lrel. Qed.

Lemma lrel3ON (p1 p2 : peg 3) : p1 != p2 -> 
  lrel p1 p2 -> ~~ lrel p1 `p[p1, p2] -> lrel p2 `p[p1, p2].
Proof.
have D p3 p4 : (p3 == p4) = (val p3 == val p4).
  by apply/eqP/idP => /val_eqP.
move: (opegDl p1 p2) (opegDr p1 p2).
by case: (peg3E `p[p1, p2]) => ->;
   case: (peg3E p1) => ->; 
   case: (peg3E p2) => ->; 
   rewrite !D /lrel /= ?inordK.
Qed.

Lemma lrel3ON4 (p1 p2 p3 p4 : peg 3) : 
     p1 != p2 -> p1 != p3 -> p2 != p3 ->
     lrel p1 p2 -> lrel p1 p3 -> lrel p3 p4 -> p4 = p1.
Proof.
have D p5 p6 : (p5 == p6) = (val p5 == val p6).
  by apply/eqP/idP => /val_eqP.
by case: (peg3E p1) => ->;
   case: (peg3E p2) => ->; 
   case: (peg3E p3) => ->; 
   case: (peg3E p4) => ->; 
   rewrite !D /lrel /= ?inordK.
Qed.

Local Notation "c1 `-->_r c2" := (lmove c1 c2)
    (format "c1  `-->_r  c2", at level 60).
Local Notation "c1 `-->*_r c2" := (connect lmove c1 c2)
    (format "c1  `-->*_r  c2", at level 60).

(******************************************************************************)
(* Function that builds a path from a configuration to a peg                  *)
(******************************************************************************)

Fixpoint lhanoi3 {n : nat} : configuration 3 n -> configuration _ n -> _ :=
  match n with
  | 0 => fun _ _ => [::] : seq (configuration _ 0)
  | n1.+1 =>
      fun c1 c2 =>
       let p1 := c1 ldisk in
       let p2 := c2 ldisk in
       if p1 == p2 then [seq ↑[i]_p2 | i <- lhanoi3 ↓[c1] ↓[c2]] else
       let p3 := `p[p1, p2] in
       if lrel p1 p2 then
          [seq ↑[i]_p1 | i <- lhanoi3 ↓[c1] `c[p3]] ++
          [seq ↑[i]_p2 | i <- `c[p3] :: lhanoi3 `c[p3] ↓[c2]]
        else
          [seq ↑[i]_p1 | i <- lhanoi3 ↓[c1] `c[p2]] ++
          [seq ↑[i]_p3 | i <- `c[p2] :: lhanoi3 `c[p2] `c[p1]] ++
          [seq ↑[i]_p2 | i <- `c[p1] :: lhanoi3 `c[p1] ↓[c2]]
  end.

Lemma lhanoi3_nil_inv n (c1 c2 : _ _ n) : lhanoi3 c1 c2 = [::] -> c1 = c2.
Proof.
elim: n c1 c2 => [c1 c2 _|n IH c1 c2] /=; first by apply/ffunP=> [] [].
case: eqP => [H | H] //=; last by case: lrel; case: map.
rewrite -{2}[c1]cunliftrK -{3}[c2]cunliftrK.
case: lhanoi3 (IH ↓[c1] ↓[c2]) => //= -> // _.
by rewrite H.
Qed.

Lemma last_lhanoi3 n (c1 c2 : _ _ n) (cs := lhanoi3 c1 c2) :
  last c1 cs = c2.
Proof.
have HH := @lirr 3.
rewrite /cs; elim: n c1 c2 {cs} => /= [c1 c2| n IH c1 c2].
  by apply/ffunP=> [] [].
case: eqP => [Ho|/eqP Do].
  by rewrite -{1}[c1](cunliftrK) Ho last_map IH // cunliftrK.
set p1 := _ ldisk; set p2 := opeg _ _.
set cp2 := `c[_]; set cp := `c[_]; set cp1 := `c[_].
case: (boolP (lrel _ _)) => [Hrel|Hrel].
  by rewrite last_cat /= last_map IH cunliftrK.
by rewrite last_cat /= last_cat /= last_map IH cunliftrK.
Qed.

Lemma path_lhanoi3 n (c1 c2 : _ _ n) (cs := lhanoi3 c1 c2) :
  path lmove c1 cs.
Proof.
have HH := @lirr 3.
rewrite /cs; elim: n c1 c2 {cs} => //= n IH c1 c2.
case: eqP => [Ho|/eqP Do].
  by rewrite -{1}[c1](cunliftrK) Ho path_liftr.
set p1 := _ ldisk; set p2 := opeg _ _.
set cp2 := `c[_]; set cp := `c[_]; set cp1 := `c[_].
case: (boolP (lrel _ _)) => [Hrel|Hrel].
  rewrite cat_path /=; apply/and3P; repeat split.
  - by rewrite -{1}[c1]cunliftrK path_liftr.
  - rewrite -{1}[c1]cunliftrK last_map last_lhanoi3.
    by apply: move_liftr_perfect; rewrite // eq_sym (opegDl, opegDr).
  by rewrite path_liftr.
rewrite cat_path /= cat_path /=; apply/and5P; split.
- by rewrite -{1}[c1]cunliftrK /= path_liftr.
- rewrite -{1}[c1]cunliftrK /= last_map last_lhanoi3.
- apply: move_liftr_perfect => //; first by apply: lrel3O.
  by rewrite opegDr.
- by rewrite path_liftr.
- rewrite last_map last_lhanoi3.
  apply: move_liftr_perfect => //.
  - rewrite /p2 opeg_sym lsym lrel3O ?opegDl //; first by rewrite eq_sym.
    by rewrite lsym.
  - by rewrite opegDl.
  by rewrite eq_sym.
by rewrite path_liftr.
Qed.

(* Two configurations are always connected *)
Lemma move_lconnect3 n (c1 c2 : configuration 3 n) : c1 `-->*_r c2.
Proof.
apply/connectP; exists (lhanoi3 c1 c2); first by apply: path_lhanoi3.
by rewrite last_lhanoi3.
Qed.

(* lhanoi gives the smallest path connecting c1 to c2                         *)
(* This path is unique                                                        *)
Lemma lhanoi3_min n (c1 c2 : configuration 3 n) cs :
  path lmove c1 cs -> last c1 cs = c2 ->
  size (lhanoi3 c1 c2) <= size cs ?= iff (cs == lhanoi3 c1 c2).
Proof.
(* we adapt the proof for the standard ha
noi problem
   surely a shorter proof exists *)
have [m sLm] := ubnP (size cs); elim: m => // m IHm in n c1 c2 cs sLm *.
(* The usual induction on the number of disks                       *)
elim : n c1 c2 cs sLm => [c1 p [|] //=|n IH c1 c cs Scs c1Pcs lc1csEp /=].
set (p := c ldisk).
rewrite !fun_if !size_cat /= !size_cat /= !size_map.
case: (c1 _ =P p) => [lc1Ep |/eqP lc1Dp].
  (* the largest disk is already well-placed *)
  have [cs1 [c1'Pcs1 lc1'csElc1cs' /leqifP]] := 
     pathS_restrict (@lirr 3) c1Pcs.
  have lc1'cs1E : last ↓[c1] cs1 = ↓[c].
    by rewrite lc1'csElc1cs'; congr cunliftr.
  case: eqP=> [csEcs1 /eqP<- |/eqP csDcs1 scs1L].
    rewrite csEcs1 lc1Ep eq_map_liftr.
    apply: IH => //.
    by move: Scs; rewrite csEcs1 size_map.
  apply/leqifP; case: eqP => [->//|_].
    by rewrite size_map.
  apply: leq_ltn_trans (scs1L).
  apply: IH => //.
  by apply: ltn_trans Scs.
pose f (c : configuration 3 n.+1) := c ldisk.
have HHr := @lirr 3.
have HHs := @lsym 3.
(* We need to move the largest disk *)
case: path3SP c1Pcs => // [c1' cs' p1 csE c1'Ecs1'|
                           cs1 cs2 p1 p2 p3 c1' c2 p1Dp2 p1Rp2
                           lc1'cs1Epp3 csE c1'Pcs1 c2Pcs2 _].
  (* this case is impossible the largest disk has to move *)
  case/eqP: lc1Dp.
  move: lc1csEp => /(congr1 f).
  by rewrite /f csE -{1}[c1]cunliftrK last_map cliftr_ldisk.
(* c4 is the first configuration when the largest disk has moved *)
rewrite csE size_cat -/p1.
have Scs1 : size cs1 < m.+1.
  apply: ltn_trans Scs.
  by rewrite csE size_cat /= size_map addnS ltnS leq_addr.
have Scs2 : size cs2 < m.+1.
  apply: ltn_trans Scs.
  by rewrite csE size_cat /= size_map addnS ltnS leq_addl.
have [p1Rp| p1NRp] := boolP (lrel p1 p).
  case: (p2 =P p) => [p2Ep|/eqP p2Dp].
    (* the first moves of largest disk of cs is the right one *)
    rewrite -p2Ep -/p3 size_map /=.
    have/(pathS_restrict (@lirr 3))[cs2' [c2'Pcs2' lc2'cs2'E cs2'L]] := c2Pcs2.
    have Scs2' : size cs2' < m.+1.
      by apply: leq_ltn_trans Scs2; rewrite cs2'L.
    have /IH := lc1'cs1Epp3 => // /(_ Scs1 c1'Pcs1) IHc1.
    have /IH : last ↓[c2] cs2' = ↓[c]
           => [| /(_ Scs2' c2'Pcs2') IHc2].
      rewrite lc2'cs2'E; congr cunliftr.
      by move: lc1csEp; rewrite csE last_cat /= => ->.
    rewrite cliftrK in IHc2.
    move /leqifP : cs2'L.
    case: eqP => [cs2E _ | /eqP cs2D Lcs2].
      (* there is only one move of the largest disk in cs *)
      rewrite cs2E size_map cliftr_ldisk /=.
      have /leqifP := IHc1; case: eqP => [->_ |_ Lc1].
        (* the first part of cs is perfect *)
        have /leqifP := IHc2; case: eqP => [->_ |_ Lc2].
          (* the second part of cs is perfect, only case of equality *)
          apply/leqifP; case: eqP => [/(congr1 size)|[]].
            by rewrite !size_cat /= !size_map => ->.
          by congr (_ ++ _ :: _); rewrite !cliftK.
        apply/leqifP; case: eqP => [/(congr1 size)|_].
          by rewrite size_cat /= size_cat /= !size_map => ->.
        by rewrite ltn_add2l ltnS.
      apply/leqifP; case: eqP => [/(congr1 size)|_].
        by rewrite !size_cat /= !size_map => ->.
      by rewrite -addSn leq_add // ltnS IHc2.
    apply/leqifP; case: eqP => [/(congr1 size)|_].
      by rewrite !size_cat /= !size_map => ->.
    rewrite -addnS leq_add //= ?ltnS.
      by rewrite IHc1.
    by apply: leq_ltn_trans Lcs2; rewrite IHc2.
  (* The largest disk jumped to an intermediate peg *)
  have p3Ep : p3 = p by apply/eqP; rewrite opeg3E // lc1Dp.
  have p1Dp : p1 != p by rewrite eq_sym -p3Ep opeg3E // eqxx.
  (* cs cannot be optimal *)
  apply/leqifP; case: eqP => [/(congr1 size)|_].
     by rewrite !size_cat /= !size_map => ->.
  case: path3SP c2Pcs2 => // [c2' cs2' p2' cs2E c2'Pcs2' _|
                              cs3 cs4 p4 p5 p6 c2' c3
                              p4Dp5 p4Rp5 lc2'cs3Epp6 cs2E c2'Pcs3 c3Pcs4 _].
    (* this is impossible we need another move of the largest disk *)
    case/eqP: p2Dp.
    have := lc1csEp.
    rewrite csE last_cat /= cs2E -[c2]cunliftrK last_map => /(congr1 f).
    by rewrite /f !cliftr_ldisk.
  (* cs has a duplicate *)
  have p4Ep2 : p4 = p2 by rewrite /p4 !cliftr_ldisk.
  have p5Ep1: p5 = p1.
    apply: (@lrel3ON4 p1 p p2 p5) => //; first by rewrite eq_sym.
    by rewrite -p4Ep2.
  have p6Ep3 : p6 = p3.
    by apply/eqP; rewrite /p6 opeg3E // p4Ep2 p5Ep1 p3Ep p2Dp.
  (* exhibit a shortest path *)
  pose cs5 := [seq ↑[i]_p1 | i <- cs1] ++ cs4.
  have scs5Lscs : size cs5 < size cs.
    rewrite /cs5 csE cs2E !size_cat /= !size_cat /= !size_map.
    by rewrite ltn_add2l // !addnS! ltnS -addSn leq_addl.
  have c1Mcs5 : path lmove c1 cs5.
    rewrite cat_path -{1}[c1]cunliftrK /= !path_liftr //=.
    rewrite c1'Pcs1.
    rewrite -{1}[c1]cunliftrK  last_map lc1'cs1Epp3 //.
    by rewrite -p6Ep3 -/p1 -p5Ep1.
  have lc1cs5E : last c1 cs5 = c.
    rewrite last_cat.
    rewrite -[c1]cunliftrK last_map lc1'cs1Epp3 //.
    rewrite -p6Ep3 -/p1 -p5Ep1 //.
    have := lc1csEp.
    by rewrite csE cs2E last_cat /= last_cat.
  apply: leq_trans (_ : size cs5 < _); last first.
    by rewrite cs2E /= !size_cat /= !size_map ltn_add2l //= 
               ltnS -addSnnS leq_addl.
  rewrite ltnS.
  have /IHm : size cs5 < m.
    rewrite -ltnS.
    by apply: leq_ltn_trans Scs.
  move=> /(_ c1 c c1Mcs5 lc1cs5E) /=.
  by rewrite /= (negPf lc1Dp) p1Rp -/p1 size_cat /= !size_map => ->.
have p2Dp : p2 != p by apply: contra p1NRp => /eqP<-.
have p3Ep : p3 = p.
  by apply/eqP; rewrite opeg3E // lc1Dp.
case: path3SP c2Pcs2 => // [c2' cs2' p2' cs2E c2'Pcs2' _|
                            cs3 cs4 p4 p5 p6 c2' c3
                            p4Dp5 p4Rp5 lc2'cs3Epp6 cs2E c2'Pcs3 c3Pcs4 _].
  (* this is impossible at least two moves to reach p *)
  case/eqP: p2Dp.
  move: lc1csEp.
  rewrite csE cs2E last_cat /= -[c2]cunliftrK last_map !cliftr_ldisk.
  by move => /(congr1 f); rewrite /f !cliftr_ldisk.
rewrite cs2E /= size_cat !size_map /=.
have Scs3 : size cs3 < m.+1.
   by apply: leq_trans Scs2; rewrite ltnS cs2E size_cat /= size_map leq_addr.
have Scs4 : size cs4 < m.+1.
   by apply: leq_trans Scs2; rewrite ltnS cs2E size_cat /= -addSnnS leq_addl.
have p4Ep2 : p4 = p2 by rewrite [LHS]cliftr_ldisk.
case: (p5 =P p1) => [p5Ep1|/eqP p5Dp1].
  (* cs has a duplicate *)
  apply/leqifP; case: eqP => [/(congr1 size)|_].
    rewrite !size_cat /= size_cat !size_map size_cat /= !size_map => ->.
    by rewrite !(addSn, addnS) addnA.
  have p6Ep3 : p6 = p3.
    by rewrite /p6 /p3 opeg_sym; congr opeg.
  have lc1'cs1Ec3 : cliftr p1 (last c1' cs1) = c3.
    by rewrite lc1'cs1Epp3 -p6Ep3 -p5Ep1.
  (* exhibit a shortest path *)
  pose cs5 := [seq ↑[i]_p1 | i <- cs1] ++ cs4.
  have scs5Lscs : size cs5 < size cs.
    rewrite /cs5 csE cs2E !size_cat /= !size_cat /= !size_map.
    by rewrite ltn_add2l // addnS !ltnS -addSn leq_addl.
  have c1Mcs5 : path lmove c1 cs5.
    rewrite cat_path -{1}[c1]cunliftrK /= !path_liftr //=.
    rewrite c1'Pcs1.
    rewrite -{1}[c1]cunliftrK  last_map lc1'cs1Epp3 //.
    by rewrite -p6Ep3 -/p1 -p5Ep1.
  have lc1cs5E : last c1 cs5 = c.
    rewrite last_cat.
    rewrite -[c1]cunliftrK last_map lc1'cs1Epp3 //.
    rewrite -p6Ep3 -/p1 -p5Ep1 //.
    have := lc1csEp.
    by rewrite csE cs2E last_cat /= last_cat.
  apply: leq_trans (_ : size cs5 < _); last first.
    by rewrite !size_cat /= !size_map ltn_add2l //= ltnS -addSnnS leq_addl.
  have /IHm : size cs5 < m.
    rewrite -ltnS.
    by apply: leq_ltn_trans Scs.
  move=> /(_ c1 c c1Mcs5 lc1cs5E) /=.
  rewrite /= (negPf lc1Dp) (negPf p1NRp) -/p1 ltnS.
  by rewrite !size_cat /= size_cat /= !size_map => ->.
have p5Ep : p5 = p.
  by apply/eqP; rewrite eq_sym -p3Ep opeg3E // eq_sym p5Dp1 -p4Ep2.
have p2Ep1p : p2 = opeg p1 p.
  by apply/eqP; rewrite eq_sym opeg3E // p1Dp2 eq_sym p2Dp.
have p6Ep1 : p6 = p1.
  by apply/eqP; rewrite opeg3E // p4Ep2 eq_sym p1Dp2.
case: path3SP c3Pcs4 => // [c3' cs4' p8 cs4E c3'Pcs4' _|
                            cs5 cs6 p8 p9 p10 c3' c4
                            p8Dp9 p8Rp9 lc3'cs5Epp10 cs4E c3'Pcs5 c4Pcs6 _].
  have Scs4' : size cs4' < m.+1 by rewrite cs4E size_map in Scs4.
  rewrite cs4E size_map.
  rewrite csE cs2E last_cat /= last_cat /=
          -[c3]cunliftrK cs4E last_map in lc1csEp.
  have /(congr1 cunliftr) := lc1csEp.
  rewrite cliftrK =>  lc3'cs4'Ec'.
  have /IH := c1'Pcs1 => /(_ _ Scs1 lc1'cs1Epp3) IH1.
  rewrite p3Ep in IH1.
  have /IH := c2'Pcs3 => /(_ _ Scs3 lc2'cs3Epp6) IH2.
  rewrite [c2']cliftrK p3Ep p6Ep1 in IH2.
  have /IH := c3'Pcs4' => /(_ _ Scs4' lc3'cs4'Ec') IH3.
  rewrite [c3']cliftrK p6Ep1 in IH3.
  move /leqifP : IH1.
  case: eqP => [E1 _ | /eqP cs1D Lcs1].
    (* the first part cs1 is perfect *)
    have /leqifP := IH2; case: eqP => [E2 _ |_ Lc1].
      (* the second part cs3 is perfect *)
      have /leqifP := IH3; case: eqP => [E3 _ |_ Lc2].
      (* the third part cs4 is perfect, only case of equality *)
        apply/leqifP; case: eqP => [/(congr1 size)|[]].
          rewrite !size_cat /= size_cat /= size_cat /= !size_map => ->.
          by rewrite !(addSn, addnS) addnA.
        congr (_ ++ _ :: _ ++ _ :: _).
        - by rewrite E1.
        - by rewrite /c2 p3Ep p2Ep1p.
        - by rewrite p4Ep2 -p2Ep1p E2.
        - by rewrite /c3 p6Ep1 p5Ep.
        - congr (map (cliftr _) _).
            by rewrite /p8 !cliftr_ldisk.
          by [].
      apply/leqifP; case: eqP => [/(congr1 size)|_].
        rewrite !size_cat /= !size_cat /= !size_map => ->.
        by rewrite !(addSn, addnS) addnA.
      by rewrite E1 E2 !(addSn, addnS) !ltnS !ltn_add2l.
    apply/leqifP; case: eqP => [/(congr1 size)|_].
      rewrite !size_cat /= !size_cat /= !size_map => ->.
      by rewrite !(addSn, addnS) addnA.
    rewrite E1 !(addSn, addnS) !ltnS !ltn_add2l.
    apply: leq_ltn_trans (_ : _ <= size (lhanoi3 `c[p, n] `c[p1])
                                   + size cs4') _.
      by rewrite leq_add2l IH3.
    by rewrite ltn_add2r.
  apply/leqifP; case: eqP => [/(congr1 size)|_].
    rewrite !size_cat /= !size_cat /= !size_map => ->.
    by rewrite !(addSn, addnS).
  by rewrite !(addSn, addnS) !ltnS -addSn !leq_add ?IH2 ?IH3.
(* three moves in a row -> duplicate *)
have p8Ep : p8 = p by rewrite [LHS]cliftr_ldisk.
have p9Ep2 : p9 = p2.
  apply: lrel3ON4 p8Rp9.
  - by rewrite eq_sym; exact: p1Dp2.
  - by rewrite p8Ep.
  - by rewrite p8Ep.
  - by rewrite lsym.
  by rewrite p8Ep -p4Ep2 -p5Ep.
have p10Ep1 : p10 = p1.
  by apply/eqP; rewrite opeg3E // p8Ep eq_sym lc1Dp p9Ep2 eq_sym.
have cc : cliftr p2 (last c2' cs3) = c4.
  by rewrite /c4 lc2'cs3Epp6 p6Ep1 p10Ep1 p9Ep2.
apply/leqifP; case: eqP => [/(congr1 size)|_].
  rewrite !size_cat /= size_cat !size_map size_cat /= !size_map => ->.
  by rewrite !(addSn, addnS).
(* exhibit a shortest path *)
pose cs7 := [seq ↑[i]_p1 | i <- cs1] ++ c2 :: [seq ↑[i]_p4 | i <- cs3] ++ cs6.
have scs7Lscs7: size cs7 < size cs.
  rewrite /cs7 csE cs2E cs4E.
  rewrite size_cat /= size_cat /= size_cat /= size_cat /= size_cat /= !size_map.
  by rewrite !addnS ltnS -!addnS !leq_add2l addnS ltnS -addSnnS leq_addl.
have c1Mcs7 : path lmove c1 cs7.
  rewrite cat_path -{1}[c1]cunliftrK /= !path_liftr //=.
  rewrite c1'Pcs1.
  rewrite -{1}[c1]cunliftrK  last_map lc1'cs1Epp3 //.
  rewrite p4Ep2 cat_path /c2 -/p1 /=.
  apply/and3P; split => //.
    - apply: move_liftr_perfect => //.
        by rewrite eq_sym opegDl.
      by rewrite eq_sym opegDr.
    by rewrite path_liftr //; rewrite [c2']cliftrK in c2'Pcs3.
  by rewrite last_map; rewrite [c2']cliftrK in cc; rewrite cc.
have lc1cs7E : last c1 cs7 = c.
  rewrite last_cat /= last_cat p4Ep2.
  rewrite -[c2]cunliftrK !cliftr_ldisk.
  rewrite last_map lc2'cs3Epp6.
  have := lc1csEp.
  rewrite csE cs2E cs4E last_cat /= last_cat /= last_cat /=.
  by rewrite /c4 p10Ep1 p6Ep1 p9Ep2.
apply: leq_trans (_ : size cs7 < _); last first.
  rewrite !size_cat /= size_cat /= !size_map ltn_add2l //=.
  rewrite cs4E size_cat /= size_map !addnS !ltnS -addnS -addSn.
  by rewrite leq_add2l leq_addl.
have /IHm : size cs7 < m.
  rewrite -ltnS.
   by apply: leq_ltn_trans Scs.
move=> /(_ c1 c c1Mcs7 lc1cs7E) /=.
rewrite /= (negPf lc1Dp) (negPf p1NRp) -/p1 ltnS.
by rewrite size_cat /= size_cat /= !size_map => ->.
Qed.

(* size on a perfect configuration depends which peg we consider *)
Lemma size_app_lhanoi3_p n p1 p2 :
   size (lhanoi3 `c[p1, n] `c[p2])  =
     if lrel p1 p2 then (3 ^ n).-1./2 else (3 ^ n).-1 * (p1 != p2).
Proof.
elim: n p1 p2 => [p1 p2|n IH p1 p2] /=; first by rewrite if_same.
rewrite !ffunE; case: eqP => [p1Ep2|/eqP p1Dp2].
  by rewrite !perfect_unliftr size_map IH p1Ep2 eqxx lirr !muln0.
rewrite !perfect_unliftr !fun_if !size_cat /= !size_cat /= !size_map.
rewrite !IH eq_sym opegDl // opegDr //= !muln1.
have Hd : (3 ^ n.+1).-1 = (3 ^ n).-1 + (3 ^ n).*2.
  rewrite expnS -[3 ^n]prednK ?expn_gt0 //.
  by rewrite mulnS /= doubleS !addnS mulSn mul2n.
rewrite ![lrel p2 _]lsym.
case: (boolP (lrel _ _)) => [Hrel1|Hrel1]; last first.
  rewrite [p2 == _]eq_sym p1Dp2 !muln1.
  rewrite expnS !mulSn addn0.
  by case: expn (expn_gt0 3 n) => // k _; rewrite !addnS addnA.
case: (boolP (lrel _ _)) => [Hrel2|Hrel2].
  rewrite !ifN.
    by rewrite Hd halfD /= odd_double andbF add0n doubleK prednK ?expn_gt0.
  by have := lrel3B p1Dp2; rewrite Hrel1 Hrel2 lsym.
rewrite ifT; last by rewrite lsym; apply: lrel3ON.
rewrite Hd halfD /= odd_double andbF add0n doubleK -addSnnS addnC.
by rewrite prednK // expn_gt0.
Qed.

Fixpoint size_lhanoi3 {n : nat} : configuration 3 n -> configuration 3 n -> _ :=
  match n with
  | 0 => fun _ _ => 0
  | n1.+1 =>
      fun c1 c2 =>
       let p1 := c1 ldisk in
       let p2 := c2 ldisk in
       if p1 == p2 then size_lhanoi3 ↓[c1] ↓[c2] else
       let p3 := `p[p1, p2] in
       if lrel p1 p2 then
         (size_lhanoi3 ↓[c1] `c[p3] + size_lhanoi3 `c[p3] ↓[c2]).+1 
        else
         (size_lhanoi3 ↓[c1] `c[p2] +
          (3 ^ n1).-1  +
         size_lhanoi3 `c[p1] ↓[c2]).+2  
  end.

Lemma size_lhanoi3E n (c1 c2 : _ _ n) :
  size_lhanoi3 c1 c2 = size (lhanoi3 c1 c2).
Proof.
elim: n c1 c2 => //= n IH c1 c2.
case: eqP => [lc1Elc2|/eqP lc1Dlc2].
  by rewrite size_map IH.
case: (boolP (lrel _ _)) => [lc1Rlc2|lc1NRlc2].
  by rewrite size_cat /= !size_map !IH addnS.
rewrite size_cat /= size_cat /= !size_map size_app_lhanoi3_p
        lsym (negPf lc1NRlc2).
by rewrite eq_sym (negPf lc1Dlc2) muln1 !addnS addnA !IH.
Qed.

(* size on a perfect configuration depends which peg we consider *)
Lemma size_lhanoi3_p n p1 p2 :
   size_lhanoi3 `c[p1, n] `c[p2] =
     if lrel p1 p2 then (3 ^ n).-1./2 else (3 ^ n).-1 * (p1 != p2).
Proof. by rewrite size_lhanoi3E size_app_lhanoi3_p. Qed.

Lemma gdist_lhanoi3_size n (c1 c2 : _ _ n) : 
  `d[c1, c2]_lmove = size_lhanoi3 c1 c2.     
Proof.
apply/eqP; rewrite eqn_leq [size_lhanoi3 _ _]size_lhanoi3E.
rewrite gdist_path_le //=; last 2 first.
- by apply: path_lhanoi3.
- by apply: last_lhanoi3.
have /gpath_connect[p1 p1H] : connect lmove c1 c2 by apply: move_lconnect3.
rewrite (gpath_dist p1H) lhanoi3_min //; first by apply: gpath_path p1H.
by apply: gpath_last p1H.
Qed.

Lemma gdist_lhanoi3p n (p1 p2 : peg 3) :
  `d[`c[p1, n], `c[p2, n]]_lmove =
   if lrel p1 p2 then (3 ^ n).-1./2 else (3 ^ n).-1 * (p1 != p2).
Proof. by rewrite gdist_lhanoi3_size size_lhanoi3_p. Qed.

End LHanoi3.
