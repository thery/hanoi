From mathcomp Require Import all_ssreflect.
Require Import gdist ghanoi ghanoi3.

(*****************************************************************************)
(*                                                                           *)
(*             Linear Hanoi Problem with 3 pegs                              *)
(*                                                                           *)
(*****************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section LHanoi3.

Let hrel : rel (peg 3) := [rel x y | ((nat_of_ord x).+1 == y) || (y.+1 == x)].
Let hirr : irreflexive hrel.
Proof. by move=> n; rewrite /hrel /= (gtn_eqF (leqnn _)). Qed.
Let hsym : symmetric hrel.
Proof. by move=> x y; rewrite /hrel /= orbC.
Qed.

Let hrelD p1 p2 : p1 != p2 -> hrel p1 p2 || hrel p1 (opeg3 p1 p2).
Proof.
by case: (peg3E p1) => ->; case: (peg3E p2) => -> // /eqP/val_eqP;
  rewrite /hrel /opeg3 /= ?inordK.
Qed.

Let hrelB p1 p2 : p1 != p2 -> ~~ [&& hrel p1 p2, hrel p1 (opeg3 p1 p2) & hrel p2 (opeg3 p1 p2)].
Proof.
by case: (peg3E p1) => ->; case: (peg3E p2) => -> // /eqP/val_eqP;
  rewrite /hrel /opeg3 /= ?inordK.
Qed.

Let hrelO p1 p2 : p1 != p2 -> ~~ hrel p1 p2 -> hrel p1 (opeg3 p1 p2).
Proof. by move/hrelD; case: hrel. Qed.

Let hrelON p1 p2 : p1 != p2 -> hrel p1 p2 -> ~~ hrel p1 (opeg3 p1 p2) ->
        hrel p2 (opeg3 p1 p2).
Proof.
by case: (peg3E p1) => ->; case: (peg3E p2) => -> // /eqP/val_eqP;
  rewrite /hrel /opeg3 /= ?inordK.
Qed.

Let hrelON4 p1 p2 p3 p4 : p1 != p2 -> p1 != p3 -> p2 != p3 ->
     hrel p1 p2 -> hrel p1 p3 -> hrel p3 p4 -> p4 = p1.
Proof.
by case: (peg3E p1) => ->; case: (peg3E p2) => ->;
   case: (peg3E p3) => ->; case: (peg3E p4) => ->// /eqP/val_eqP;
   rewrite /hrel /opeg3 /= ?inordK // eqxx.
Qed.

Let hmove {n} := @move 3 hrel n.
Let hmove_sym n (c1 c2 : configuration 3 n) : hmove c1 c2 = hmove c2 c1
  := move_sym hsym c1 c2.
Let hconnect n := connect (@hmove n).

Local Notation "c1 `--> c2" := (hmove c1 c2)
    (format "c1  `-->  c2", at level 60).
Local Notation "c1 `-->* c2" := (hconnect c1 c2)
    (format "c1  `-->*  c2", at level 60).
Local Notation "`c[ p ] " := (perfect p )
    (format "`c[ p ]", at level 60).
Local Notation "`p[ p1 , p2 ] " := (opeg3 p1 p2)
    (format "`p[ p1 ,  p2 ]", at level 60).

Lemma move_lperfect n p1 p2 p3 :
  p1 != p3 -> p2 != p3 -> hrel p1 p2 ->
 @hmove n.+1 (clift p1 (perfect p3)) (clift p2 (perfect p3)).
Proof.
move=> p1Dp3 p2Dp3 Hrel.
have p1Dp2 : p1 != p2.
  by apply/eqP=> p1Ep2; have := hirr p2; rewrite -{1}p1Ep2 Hrel.
apply/moveP; exists ldisk; split => [|d lDd|d|d].
- by rewrite !ffunE unlift_none.
- by rewrite !ffunE; case: unliftP => // lEd /=; case/eqP: lDd.
- rewrite !ffunE unlift_none /=; case: unliftP => [i|->] //=.
  by rewrite ffunE => _ p1Ep3; case/negP: p1Dp3; rewrite p1Ep3.
rewrite !ffunE unlift_none /=; case: unliftP => [i|->] //=.
by rewrite ffunE => _ p2Ep3; case/negP: p2Dp3; rewrite p2Ep3.
Qed.


(*****************************************************************************)
(* Function that builds a path from a configuration to a peg                 *)
(*****************************************************************************)

Fixpoint lhanoi {n : nat} : configuration _ n -> configuration _ n -> _ :=
  match n with
  | 0 => fun _ _ => [::] : seq (configuration _ 0)
  | n1.+1 =>
      fun c1 c2 =>
       let p1 := c1 ldisk in
       let p2 := c2 ldisk in
       if p1 == p2 then map (clift p2) (lhanoi (cunlift c1) (cunlift c2)) else
       let p3 := opeg3 p1 p2 in
       if hrel p1 p2 then
         map (clift p1) (lhanoi (cunlift c1) (perfect p3)) ++
         map (clift p2) (perfect p3 :: lhanoi (perfect p3) (cunlift c2)) else
         map (clift p1) (lhanoi (cunlift c1) (perfect p2)) ++
         map (clift p3) (perfect p2 :: lhanoi (perfect p2) (perfect p1)) ++
         map (clift p2) (perfect p1 :: lhanoi (perfect p1) (cunlift c2))
  end.

Lemma lhanoi_nil_inv n (c1 c2 : _ _ n) : lhanoi c1 c2 = [::] -> c1 = c2.
Proof.
elim: n c1 c2 => [c1 c2 _|n IH c1 c2] /=; first by apply/ffunP=> [] [].
case: eqP => [H | H] //=; last by case: hrel; case: map.
rewrite -{2}[c1]cunliftK -{3}[c2]cunliftK.
case: lhanoi (IH (cunlift c1) (cunlift c2)) => //= -> // _.
by rewrite H.
Qed.

Lemma lhanoi_correct n (c1 c2 : _ _ n) (cs := lhanoi c1 c2) :
  path (@hmove n) c1 cs /\ last c1 cs = c2.
Proof.
rewrite /cs; elim: n c1 c2 {cs} => /= [c1 c2| n IH c1 c2].
  by split=> //; apply/ffunP=> [] [].
case: eqP => [Ho|/eqP Do].
  have [Hp Hl] := IH (cunlift c1) (cunlift c2).
  split.
    by rewrite -{1}[c1](cunliftK) Ho path_lift.
  by rewrite -{1}[c1](cunliftK) Ho last_map Hl cunliftK.
set p1 := _ ldisk.
set p2 := opeg3 _ _.
set cp2 := perfect _.
set cp := perfect _.
set cp1 := perfect _.
case: (boolP (hrel _ _)) => [Hrel|Hrel].
  have [cPlr lclrEp2] := IH (cunlift c1) cp2.
  have [p2Plr lp2lrEc2'] := IH cp2 (cunlift c2).
  rewrite last_cat cat_path /= -{1 3}[c1]cunliftK !path_lift //=.
  rewrite cPlr p2Plr.
  rewrite !last_map lclrEp2 lp2lrEc2'  andbT; split => //.
    by apply: move_lperfect; rewrite // eq_sym (opeg3Dl, opeg3Dr).
  by rewrite cunliftK.
have [cPlr lclrEp] := IH (cunlift c1) cp.
have [pPlr lplrEp] := IH cp cp1.
have [p1Plr lp1lrEp] := IH cp1 (cunlift c2).
rewrite cat_path /= cat_path last_cat /= last_cat.
rewrite -{1 3}[c1]cunliftK /= !last_map !path_lift //=.
rewrite lclrEp lplrEp lp1lrEp; split=> //; last first.
  by rewrite cunliftK.
rewrite cPlr pPlr p1Plr /= andbT.
apply/andP; split => //; apply: move_lperfect => //.
- by rewrite opeg3Dr.
- by apply: hrelO.
- by rewrite opeg3Dl.
- by rewrite eq_sym.
rewrite hsym [p2]opeg3_sym.
apply: hrelO; first by rewrite eq_sym.
by rewrite hsym.
Qed.

(* Two configurations are always connected *)
Lemma move_lconnect n (c1 c2 : configuration _ n) : hconnect c1 c2.
Proof.
have [H1 H2] := lhanoi_correct c1 c2.
by apply/connectP; exists (lhanoi c1 c2).
Qed.

(* lhanoi gives the smallest path connecting c1 to c2    *)
(* This path is unique                                               *)
Lemma lhanoi_min n c1 c2 cs :
  path (@hmove n) c1 cs -> last c1 cs = c2 ->
  size (lhanoi c1 c2) <= size cs ?= iff (cs == lhanoi c1 c2).
Proof.
(* we adapt the proof for the standard hanoi problem
   surely a shorter proof exists *)
elim: {n cs}(size _).+1 {-5}(n) c1 c2 {-2}cs (leqnn (size cs).+1) =>
      // m IHm.
(* The usual induction on the number of disks                       *)
elim => [c1 p [|] //=|n IH c1 c cs Scs c1Pcs lc1csEp /=].
set (p := c ldisk).
rewrite !fun_if !size_cat /= !size_cat /= !size_map.
case: (c1 _ =P p) => [lc1Ep |/eqP lc1Dp].
  (* the last disk is already well-placed *)
  have [cs1 [c1'Pcs1 lc1'csElc1cs' /leqifP]] := pathS_restrict hirr c1Pcs.
  have lc1'cs1E : last (cunlift c1) cs1 = cunlift c.
    by rewrite lc1'csElc1cs'; congr cunlift.
  case: eqP=> [csEcs1 /eqP<- |/eqP csDcs1 scs1L].
    rewrite csEcs1 lc1Ep eq_map_clift.
    apply: IH => //.
    by move: Scs; rewrite csEcs1 size_map.
  apply/leqifP; case: eqP => [->//|_].
    by rewrite size_map.
  apply: leq_ltn_trans (scs1L).
  apply: IH => //.
  by apply: ltn_trans Scs.
pose f (c : configuration 3 n.+1) := c ldisk.
(* We need to move the last disk *)
case: path3SP c1Pcs => // [c1' cs' p1 csE c1'Ecs1'|
                           cs1 cs2 p1 p2 p3 c1' c2 p1Dp2 p1Rp2
                           lc1'cs1Epp3 csE c1'Pcs1 c2Pcs2 _].
  (* this case is impossible the last disk has to move *)
  case/eqP: lc1Dp.
  move: lc1csEp => /(congr1 f).
  by rewrite /f csE -{1}[c1]cunliftK last_map ffunE unlift_none.
(* c4 is the first configuration when the last disk has moved *)
rewrite csE size_cat -/p1.
have Scs1 : size cs1 < m.+1.
  apply: ltn_trans Scs.
  by rewrite csE size_cat /= size_map addnS ltnS leq_addr.
have Scs2 : size cs2 < m.+1.
  apply: ltn_trans Scs.
  by rewrite csE size_cat /= size_map addnS ltnS leq_addl.
have [p1Rp| p1NRp] := boolP (hrel p1 p).
  case: (p2 =P p) => [p2Ep|/eqP p2Dp].
    (* the first moves of last disk of cs is the right one *)
    rewrite -p2Ep -/p3 size_map /=.
    have/(pathS_restrict hirr)[cs2' [c2'Pcs2' lc2'cs2'E cs2'L]] := c2Pcs2.
    have Scs2' : size cs2' < m.+1.
      by apply: leq_ltn_trans Scs2; rewrite cs2'L.
    have /IH := lc1'cs1Epp3 => // /(_ Scs1 c1'Pcs1) IHc1.
    have /IH : last (cunlift c2) cs2' = (cunlift c) => [| /(_ Scs2' c2'Pcs2') IHc2].
      rewrite lc2'cs2'E; congr cunlift.
      by move: lc1csEp; rewrite csE last_cat /= => ->.
    rewrite cliftK in IHc2.
    move /leqifP : cs2'L.
    case: eqP => [cs2E _ | /eqP cs2D Lcs2].
      (* there is only one move of the last disk in cs *)
      rewrite cs2E size_map ffunE unlift_none /=.
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
  (* The last disk jumped to an intermediate peg *)
  have p3Ep : p3 = p by apply/eqP; rewrite opeg3E // lc1Dp.
  have p1Dp : p1 != p by rewrite eq_sym -p3Ep opeg3E // eqxx.
  (* cs cannot be optimal *)
  apply/leqifP; case: eqP => [/(congr1 size)|_].
     by rewrite !size_cat /= !size_map => ->.
  case: path3SP c2Pcs2 => // [c2' cs2' p2' cs2E c2'Pcs2' _|
                              cs3 cs4 p4 p5 p6 c2' c3
                              p4Dp5 p4Rp5 lc2'cs3Epp6 cs2E c2'Pcs3 c3Pcs4 _].
    (* this is impossible we need another move of the last disk *)
    case/eqP: p2Dp.
    have := lc1csEp.
    rewrite csE last_cat /= cs2E -[c2]cunliftK last_map => /(congr1 f).
    by rewrite /f !ffunE unlift_none.
  (* cs has a duplicate *)
  have p4Ep2 : p4 = p2 by rewrite /p4 ffunE unlift_none.
  have p5Ep1: p5 = p1.
    apply: (@hrelON4 p1 p p2 p5) => //; first by rewrite eq_sym.
    by rewrite -p4Ep2.
  have p6Ep3 : p6 = p3.
    by apply/eqP; rewrite /p6 opeg3E // p4Ep2 p5Ep1 p3Ep p2Dp.
  (* exhibit a shortest path *)
  pose cs5 := [seq ↑[i]_p1 | i <- cs1] ++ cs4.
  have scs5Lscs : size cs5 < size cs.
    rewrite /cs5 csE cs2E !size_cat /= !size_cat /= !size_map.
    by rewrite ltn_add2l // !addnS! ltnS -addSn leq_addl.
  have c1Mcs5 : path hmove c1 cs5.
    rewrite cat_path -{1}[c1]cunliftK /= !path_lift //=.
    rewrite c1'Pcs1.
    rewrite -{1}[c1]cunliftK  last_map lc1'cs1Epp3 //.
    by rewrite -p6Ep3 -/p1 -p5Ep1.
  have lc1cs5E : last c1 cs5 = c.
    rewrite last_cat.
    rewrite -[c1]cunliftK last_map lc1'cs1Epp3 //.
    rewrite -p6Ep3 -/p1 -p5Ep1 //.
    have := lc1csEp.
    by rewrite csE cs2E last_cat /= last_cat.
  apply: leq_trans (_ : size cs5 < _); last first.
    by rewrite cs2E /= !size_cat /= !size_map ltn_add2l //= ltnS -addSnnS leq_addl.
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
  rewrite csE cs2E last_cat /= -[c2]cunliftK last_map ffunE unlift_none /=.
  by move => /(congr1 f); rewrite /f !ffunE unlift_none /=.
rewrite cs2E /= size_cat !size_map /=.
have Scs3 : size cs3 < m.+1.
   by apply: leq_trans Scs2; rewrite ltnS cs2E size_cat /= size_map leq_addr.
have Scs4 : size cs4 < m.+1.
   by apply: leq_trans Scs2; rewrite ltnS cs2E size_cat /= -addSnnS leq_addl.
have p4Ep2 : p4 = p2 by rewrite [LHS]ffunE unlift_none.
case: (p5 =P p1) => [p5Ep1|/eqP p5Dp1].
  (* cs has a duplicate *)
  apply/leqifP; case: eqP => [/(congr1 size)|_].
    rewrite !size_cat /= size_cat !size_map size_cat /= !size_map => ->.
    by rewrite !(addSn, addnS) addnA.
  have p6Ep3 : p6 = p3.
    by rewrite /p6 /p3 opeg3_sym; congr opeg3.
  have lc1'cs1Ec3 : clift p1 (last c1' cs1) = c3.
    by rewrite lc1'cs1Epp3 -p6Ep3 -p5Ep1.
  (* exhibit a shortest path *)
  pose cs5 := [seq ↑[i]_p1 | i <- cs1] ++ cs4.
  have scs5Lscs : size cs5 < size cs.
    rewrite /cs5 csE cs2E !size_cat /= !size_cat /= !size_map.
    by rewrite ltn_add2l // addnS !ltnS -addSn leq_addl.
  have c1Mcs5 : path hmove c1 cs5.
    rewrite cat_path -{1}[c1]cunliftK /= !path_lift //=.
    rewrite c1'Pcs1.
    rewrite -{1}[c1]cunliftK  last_map lc1'cs1Epp3 //.
    by rewrite -p6Ep3 -/p1 -p5Ep1.
  have lc1cs5E : last c1 cs5 = c.
    rewrite last_cat.
    rewrite -[c1]cunliftK last_map lc1'cs1Epp3 //.
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
have p2Ep1p : p2 = opeg3 p1 p.
  by apply/eqP; rewrite eq_sym opeg3E // p1Dp2 eq_sym p2Dp.
have p6Ep1 : p6 = p1.
  by apply/eqP; rewrite opeg3E // p4Ep2 eq_sym p1Dp2.
case: path3SP c3Pcs4 => // [c3' cs4' p8 cs4E c3'Pcs4' _|
                            cs5 cs6 p8 p9 p10 c3' c4
                            p8Dp9 p8Rp9 lc3'cs5Epp10 cs4E c3'Pcs5 c4Pcs6 _].
  have Scs4' : size cs4' < m.+1 by rewrite cs4E size_map in Scs4.
  rewrite cs4E size_map.
  rewrite csE cs2E last_cat /= last_cat /=
          -[c3]cunliftK cs4E last_map in lc1csEp.
  have /(congr1 cunlift) := lc1csEp.
  rewrite cliftK =>  lc3'cs4'Ec'.
  have /IH := c1'Pcs1 => /(_ _ Scs1 lc1'cs1Epp3) IH1.
  rewrite p3Ep in IH1.
  have /IH := c2'Pcs3 => /(_ _ Scs3 lc2'cs3Epp6) IH2.
  rewrite [c2']cliftK p3Ep p6Ep1 in IH2.
  have /IH := c3'Pcs4' => /(_ _ Scs4' lc3'cs4'Ec') IH3.
  rewrite [c3']cliftK p6Ep1 in IH3.
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
        - congr (map (clift _) _).
            by rewrite /p8 ffunE unlift_none p5Ep.
          by [].
      apply/leqifP; case: eqP => [/(congr1 size)|_].
        rewrite !size_cat /= !size_cat /= !size_map => ->.
        by rewrite !(addSn, addnS) addnA.
      by rewrite E1 E2 !(addSn, addnS) !ltnS !ltn_add2l.
    apply/leqifP; case: eqP => [/(congr1 size)|_].
      rewrite !size_cat /= !size_cat /= !size_map => ->.
      by rewrite !(addSn, addnS) addnA.
    rewrite E1 !(addSn, addnS) !ltnS !ltn_add2l.
    apply: leq_ltn_trans (_ : _ <= size (lhanoi (@perfect _ n p) (perfect p1)) + size cs4') _.
      by rewrite leq_add2l IH3.
    by rewrite ltn_add2r.
  apply/leqifP; case: eqP => [/(congr1 size)|_].
    rewrite !size_cat /= !size_cat /= !size_map => ->.
    by rewrite !(addSn, addnS).
  by rewrite !(addSn, addnS) !ltnS -addSn !leq_add ?IH2 ?IH3.
(* three moves in a row -> duplicate *)
have p8Ep : p8 = p by rewrite [LHS]ffunE unlift_none p5Ep.
have p9Ep2 : p9 = p2.
  apply: hrelON4 p8Rp9.
  - by rewrite eq_sym; exact: p1Dp2.
  - by rewrite p8Ep.
  - by rewrite p8Ep.
  - by rewrite hsym.
  by rewrite p8Ep -p4Ep2 -p5Ep.
have p10Ep1 : p10 = p1.
  by apply/eqP; rewrite opeg3E // p8Ep eq_sym lc1Dp p9Ep2 eq_sym.
have cc : clift p2 (last c2' cs3) = c4.
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
have c1Mcs7 : path hmove c1 cs7.
  rewrite cat_path -{1}[c1]cunliftK /= !path_lift //=.
  rewrite c1'Pcs1.
  rewrite -{1}[c1]cunliftK  last_map lc1'cs1Epp3 //.
  rewrite p4Ep2 cat_path /c2 -/p1 /=.
  apply/and3P; split; first by apply: move_perfect3.
    by rewrite path_lift //; rewrite [c2']cliftK in c2'Pcs3.
  by rewrite last_map; rewrite [c2']cliftK in cc; rewrite cc.
have lc1cs7E : last c1 cs7 = c.
  rewrite last_cat /= last_cat p4Ep2.
  rewrite -[c2]cunliftK ffunE unlift_none /=.
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
Lemma size_app_lhanoi_p n p1 p2 :
   size (@lhanoi n (perfect p1) (perfect p2))  =
     if hrel p1 p2 then (3 ^ n).-1./2 else (3 ^ n).-1 * (p1 != p2).
Proof.
elim: n p1 p2 => [p1 p2|n IH p1 p2] /=; first by rewrite if_same.
rewrite !ffunE; case: eqP => [p1Ep2|/eqP p1Dp2].
  by rewrite !perfect_unlift size_map IH p1Ep2 eqxx hirr !muln0.
rewrite !perfect_unlift !fun_if !size_cat /= !size_cat /= !size_map.
rewrite !IH eq_sym opeg3Dl // opeg3Dr //= !muln1.
have Hd : (3 ^ n.+1).-1 = (3 ^ n).-1 + (3 ^ n).*2.
  rewrite expnS -[3 ^n]prednK ?expn_gt0 //.
  by rewrite mulnS /= doubleS !addnS mulSn mul2n.
rewrite ![hrel p2 _]hsym.
case: (boolP (hrel _ _)) => [Hrel1|Hrel1]; last first.
  rewrite [p2 == _]eq_sym p1Dp2 !muln1.
  rewrite expnS !mulSn addn0.
  by case: expn (expn_gt0 3 n) => // k _; rewrite !addnS addnA.
case: (boolP (hrel _ _)) => [Hrel2|Hrel2].
  rewrite !ifN.
    by rewrite Hd halfD /= odd_double andbF add0n doubleK prednK ?expn_gt0.
  by have := hrelB p1Dp2; rewrite Hrel1 Hrel2 hsym.
rewrite ifT; last by rewrite hsym; apply: hrelON.
rewrite Hd halfD /= odd_double andbF add0n doubleK -addSnnS addnC.
by rewrite prednK // expn_gt0.
Qed.

Fixpoint size_lhanoi {n : nat} : configuration _ n -> configuration _ n -> _ :=
  match n with
  | 0 => fun _ _ => 0
  | n1.+1 =>
      fun c1 c2 =>
       let p1 := c1 ldisk in
       let p2 := c2 ldisk in
       if p1 == p2 then size_lhanoi (cunlift c1) (cunlift c2) else
       let p3 := opeg3 p1 p2 in
       if hrel p1 p2 then
         (size_lhanoi (cunlift c1) (perfect p3) + size_lhanoi (perfect p3) (cunlift c2)).+1 else
         (size_lhanoi (cunlift c1) (perfect p2) +
          (3 ^ n1).-1  +
         size_lhanoi (@perfect _ n1 p1) (cunlift c2)).+2
  end.

Lemma size_lhanoiE n (c1 c2 : _ _ n) : size_lhanoi c1 c2 = size (lhanoi c1 c2).
Proof.
elim: n c1 c2 => //= n IH c1 c2.
case: eqP => [lc1Elc2|/eqP lc1Dlc2].
  by rewrite size_map IH.
case: (boolP (hrel _ _)) => [lc1Rlc2|lc1NRlc2].
  by rewrite size_cat /= !size_map !IH addnS.
rewrite size_cat /= size_cat /= !size_map size_app_lhanoi_p hsym (negPf lc1NRlc2).
by rewrite eq_sym (negPf lc1Dlc2) muln1 !addnS addnA !IH.
Qed.

(* size on a perfect configuration depends which peg we consider *)
Lemma size_lhanoi_p n p1 p2 :
   @size_lhanoi n (perfect p1) (perfect p2)  =
     if hrel p1 p2 then (3 ^ n).-1./2 else (3 ^ n).-1 * (p1 != p2).
Proof. by rewrite size_lhanoiE size_app_lhanoi_p. Qed.

Lemma dist_size_lhanoi n (c1 c2 : _ _ n) :
  `d[c1, c2]_hmove = size_lhanoi c1 c2.
Proof.
apply/eqP; rewrite eqn_leq [size_lhanoi _ _]size_lhanoiE.
have [H1 H2] := lhanoi_correct c1 c2.
rewrite gdist_path_le //.
have /gdist_path[p1 [H1p1 H2p1 H3p1 <-]] : hconnect c1 c2.
  by apply: move_lconnect.
by rewrite lhanoi_min.
Qed.

End LHanoi3.
