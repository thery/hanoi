From mathcomp Require Import all_ssreflect.
Require Import extra gdist ghanoi ghanoi3.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Section Hanoi3.

(*****************************************************************************)
(*  The pegs are the three elements of 'I_3                                  *)
(*****************************************************************************)

Implicit Type p : peg 3.

Let hmove {n} := @move 3 (@drel 3) n.
Let hmove_sym n (c1 c2 : configuration 3 n) : hmove c1 c2 = hmove c2 c1
  := move_sym (@dsym 3) c1 c2.
Let hconnect n := connect (@hmove n).

Local Notation "c1 `--> c2" := (hmove c1 c2)
    (format "c1  `-->  c2", at level 60).
Local Notation "c1 `-->* c2" := (hconnect c1 c2) 
    (format "c1  `-->*  c2", at level 60).
Local Notation "`c[ p ] " := (perfect p)
    (format "`c[ p ]", at level 60).

(*****************************************************************************)
(* Function that builds a path from a configuration to a peg                 *)
(*****************************************************************************)

Fixpoint rpeg {n : nat} : configuration _ n -> _ -> _ :=
  match n with
  | 0 => fun _ _ => [::] : seq (configuration _ 0)
  | n1.+1 =>
      fun c p =>
        let p1 := c ldisk in
        if p1 == p then [seq ↑[i]_p | i <- rpeg ↓[c] p] else
        let p2 := `p[p1, p] in
        [seq ↑[i]_p1 | i <- rpeg ↓[c] p2] ++
        [seq ↑[i]_p | i <- (`c[p2]) :: rpeg (`c[p2]) p]
  end.

Lemma rpeg_perfect n p : 
  rpeg (`c[p]) p = [::] :> seq (configuration 3 n).
Proof.
elim: n => //= n IH.
by rewrite ffunE eqxx perfect_unliftr IH.
Qed.

Lemma rpeg_nil_inv n c p : 
  rpeg c p = [::] -> c = `c[p] :> configuration _ n.
Proof.
elim: n c => [c _|n IH c] /=; first by apply/ffunP=> [] [].
case: eqP => [H | H] //=; last by case: map.
rewrite -{2}[c]cunliftrK.
case: rpeg (IH (↓[c])) => // -> // _.
by rewrite H perfect_liftr.
Qed.

Lemma rpeg_correct n c p (cs := rpeg c p) :
  path (@hmove n) c cs /\ last c cs = `c[p].
Proof.
have HH := @dirr 3.
rewrite /cs; elim: n c p {cs} => /= [c p| n IH c p].
  by split=> //; apply/ffunP=> [] [].
case: eqP => [Ho|/eqP Do].
  have [Hp Hl] := IH (↓[c]) p.
  split.
  rewrite -{1}[c](cunliftrK) Ho path_liftr //.
  by rewrite -{1}[c](cunliftrK) Ho last_map Hl perfect_liftr.
set c2 := perfect _.
split; last first.
  rewrite last_cat /= last_map.
  by have [_ ->] := IH c2 p; rewrite perfect_liftr.
have [IH1 IH2] := IH (↓[c]) (`p[c ldisk, p]).
have [IH3 IH4] := IH c2 p.
rewrite cat_path /= -{1}[c]cunliftrK !path_liftr // IH1 IH3 ?andbT /=.
rewrite -{1}[c]cunliftrK last_map IH2 -/c2.
apply: move_liftr_perfect => //.
  by rewrite eq_sym (opegDl _).
by rewrite eq_sym (opegDr _).
Qed.

(* We can go from any configuration to a perfect configuration *)
Lemma move_connect_rpeg n (c : configuration _ n) p : c `-->* `c[p].
Proof.
have [H1 H2] := rpeg_correct c p.
by apply/connectP; exists (rpeg c p).
Qed.

(* So we can also from a perfect configuration c to any configuration *)
Lemma move_connect_lpeg n (c : configuration _ n) p : `c[p] `-->* c.
Proof. 
rewrite [hconnect _ _]connect_sym //.
  by apply: move_connect_rpeg.
by exact: dsym.
Qed.

(* Two configurations are always connected *)
Lemma move_connect n (c1 c2 : configuration _ n) : c1 `-->* c2.
Proof.
by apply: connect_trans (move_connect_rpeg c1 (inord 1)) 
         (move_connect_lpeg c2 (inord 1)).
Qed.

Definition is_path n k (l : k.-tuple _) c1 c2 := 
   path (@hmove n) c1 l && ((last c1 l) == c2).


(*****************************************************************************)
(* Computes the size of rpeg                                            *)
(*****************************************************************************)

Fixpoint size_rpeg {n : nat} : (configuration _ n) -> _ -> nat :=
  match n with
  | 0 => fun _ _ => 0
  | n1.+1 =>
      fun c p =>
        let p1 := c ldisk in
        if p1 == p then size_rpeg ↓[c] p else
        let p2 := `p[p1, p] in
        size_rpeg ↓[c] p2 + 
        (size_rpeg (`c[p2] : configuration _ n1) p).+1
  end.

(* size on a perfect configuration is a power of 2 *)
Lemma size_rpeg_p n p1 p2 :
   size_rpeg (`c[p1] : _ _ n) p2  = (2^ n).-1 * (p1 != p2).
Proof.
elim: n p1 p2 => [p1 p2|n IH p1 p2] //=.
rewrite ffunE; case: eqP => [p1Ep2|/eqP p1Dp2].
  by rewrite perfect_unliftr IH p1Ep2 eqxx !muln0.
rewrite perfect_unliftr !IH eq_sym opegDl // opegDr // !muln1.
rewrite expnS mul2n -addnn.
by case: (2 ^n) (expn_gt0 2 n).
Qed.

(* size computes the size *)
Lemma size_rpegE n (c : _ _ n) p : size_rpeg c p = size (rpeg c p).
Proof.
elim: n c p => //= n IH c p.
case: eqP => [//|/eqP Hd]; first by rewrite size_map.
by rewrite size_cat /= !size_map !IH.
Qed.

(* Upper bound on the size *)
Lemma size_rpeg_up n (c : _ _ n) p : size_rpeg c p <= (2^ n).-1.
Proof.
elim: n c p => //= n IH c p.
case: eqP => _.
  apply: (leq_trans (IH _ _)).
  case: (_ ^ _) (expn_eq0 2 n) (expn_eq0 2 n.+1) 
              (leq_pexp2l (isT: 0 < 2) (ltnW (leqnn n.+1))) => //= n1 _.
  by case: (_ ^ _).
apply: leq_trans (_ : (2^n).-1 + (2^n).-1.+1  <= _).
  by apply: leq_add; apply: IH.
rewrite expnS mul2n -addnn.
by case: (2 ^ n)  (expn_eq0 2 n)  => [|n1]; rewrite ?addn0.
Qed.

(* rpeg gives the smallest path to a perfect configuration.     *)
(* This path is unique                                               *)
Lemma rpeg_min n c p cs :
  path (@hmove n) c cs -> last c cs = `c[p] ->
  size_rpeg c p <= size cs ?= iff (cs == rpeg c p).
Proof.
(* As we want this statememnt to hold for any configuration c1       *)
(* and not just for initial perfect configuration the proof is more  *)
(* intricate. We need a double  induction :                          *)
(* The first induction is used when the path has duplicates (1 case) *)
have [m sLm] := ubnP (size cs); elim: m => // m IHm in n c p cs sLm *.
(* The usual induction on the number of disks                       *)
elim : n c p cs sLm => [c1 p [|] //=|n IH c1 p cs Scs c1Pcs lc1csEp /=].
case: (_ =P p) => [c1nEp |/eqP c1nDp].
  (* the largest disk is already well-placed *)
  have lcsnEc1n : last c1 cs ldisk = c1 ldisk.
    by rewrite lc1csEp !ffunE.
  have [cs1 [c1Pcs1 lcsElcs1 /leqifP]] :=
    pathS_restrict (@dirr 3) c1Pcs.
  have lcs1P : last (↓[c1]) cs1 = `c[p].
    by rewrite lcsElcs1 lc1csEp perfect_unliftr.
  case: eqP=> [csEcs1 /eqP<- |/eqP csDcs1 scs1L].
    rewrite csEcs1 c1nEp eq_map_liftr.
    apply: IH => //.
    by move: Scs; rewrite csEcs1 size_map.
  apply/leqifP; case: eqP => [->|_].
    by rewrite size_map size_rpegE.
  apply: leq_ltn_trans (scs1L).
  apply: IH => //.
  by apply: ltn_trans Scs.
pose f (c : configuration 3 n.+1) := c ldisk.
have HHr := @dirr 3.
have HHs := @dsym 3.
(* We need to move the largest disk *)
case: path3SP c1Pcs => // [c1' cs' p1 csE c1'Pcs' _|
                           cs1 cs2 p1 p2 p3 c1' c2
                           p1Dp2 p1Rp2 lc1'cs1Epp3 csE c1'Pcs1 c2Pcs2 _].
  (* this case is impossible the largest disk has to move *)
  case/eqP: c1nDp.
  move : lc1csEp; rewrite csE -[c1](cunliftrK) last_map => /(congr1 f).
  by rewrite /f !cliftr_ldisk !ffunE.
(* c2 is the first configuration when the largest disk has moved *)
rewrite csE size_cat -/p1.
have p1Dp : p1 != p by [].
have Scs1 : size cs1 < m.+1.
  apply: ltn_trans Scs.
  by rewrite csE size_cat /= size_map addnS ltnS leq_addr.
have Scs2 : size cs2 < m.+1.
  apply: ltn_trans Scs.
  by rewrite csE size_cat /= size_map addnS ltnS leq_addl.
case: (p2 =P p) => [p2Ep|/eqP p2Dp].
  pose c2' := ↓[c2].
  have c2'Epp3 : c2' = `c[`p[p1, p2]] by rewrite [LHS]cliftrK.
  (* the first moves of largest disk of cs is the right one *)
  have/(pathS_restrict HHr)[cs2' [c2'Pcs2' lc2'cs2'E cs2'L]] := c2Pcs2.
  have Scs2' : size cs2' < m.+1.
    by apply: leq_ltn_trans Scs2; rewrite cs2'L.
  have /IH := lc1'cs1Epp3 => // /(_ Scs1 c1'Pcs1) IHc1.
  have /IH : last c2' cs2' = `c[p] => [| /(_ Scs2' c2'Pcs2') IHc2].
    rewrite lc2'cs2'E -perfect_unliftr.
    by move: lc1csEp; rewrite csE last_cat /= => ->.
  rewrite -p2Ep in IHc2.
  move /leqifP : cs2'L.
  case: eqP => [cs2E _ | /eqP cs2D Lcs2].
    (* there is only one move of the largest disk in cs *)
    rewrite cs2E size_map -p2Ep -/p3.
    have /leqifP := IHc1; case: eqP => [->_ |_ Lc1].
      (* the first part of cs is perfect *)
      have /leqifP := IHc2; case: eqP => [->_ |_ Lc2].
      (* the second part of cs is perfect, only case of equality *)
        apply/leqifP; case: eqP => [/(congr1 size)|[]].
          by rewrite !size_cat /= !size_map !addnS !size_rpegE c2'Epp3 => ->.
        congr (_ ++ _ :: _).
        by rewrite c2'Epp3 !cliftr_ldisk.
      apply/leqifP; case: eqP => [/(congr1 size)|_].
        by rewrite !size_cat /= !size_map !size_rpegE => ->.
      by rewrite /= size_rpegE ltn_add2l ltnS size_map -c2'Epp3.
    apply/leqifP; case: eqP => [/(congr1 size)|_].
      by rewrite !size_cat /= !size_map !size_rpegE => ->.
    by rewrite /= -addSn leq_add // ltnS size_map -c2'Epp3 IHc2.
  apply/leqifP; case: eqP => [/(congr1 size)|_].
    by rewrite !size_cat /= !size_map !size_rpegE => ->.
  rewrite -addnS leq_add //= ?ltnS -p2Ep.
    by rewrite size_map IHc1.
  by apply: leq_ltn_trans Lcs2; rewrite -c2'Epp3 IHc2.
(* The largest disk jumped to an intermediate peg *)
have p3Ep : p3 = p.
  by apply/eqP; rewrite opeg3E // p1Dp.
(* cs cannot be optimal *)
apply/leqifP; case: eqP => [/(congr1 size)|_].
  by rewrite !size_cat /= !size_map !size_rpegE => ->.
case: path3SP c2Pcs2 => // [c2' cs2'|cs3 cs4].
  (* this is impossible we need another move of the largest disk *)  
  rewrite !cliftr_ldisk /= => cs2E c2'Pcs2'.
  case/eqP: p2Dp.
  have := lc1csEp.
  rewrite csE last_cat /= => /(congr1 f).
  by rewrite /f cs2E last_map !cliftr_ldisk !ffunE.
rewrite !cliftr_ldisk => p2'.
rewrite {}/p2' => p4.
set p5 := `p[p2, p4]; set c2' := ↓[c2].
move=> p2Dp4 p2Rp4 c2'cs5Epp5 cs2E c2'Pcs3 pp5p4Pcs4 _.
case: (p5 =P p3) => [p5Ep3 /= | /eqP p5Dp3].
  (* the path has a duplicate use the induction hypothesis *)
  have p4Ep1: p4 = p1.
    move/eqP : p5Ep3; rewrite eq_sym // opeg3E // eq_sym //.
    by rewrite opeg3E  // negb_and !negbK eq_sym (negPf p1Dp2) 
          => /andP[/eqP] .
  pose cs5 := [seq ↑[i]_p1 | i <- cs1] ++ cs4.
  have scs5Lscs : size cs5 < size cs.
    rewrite /cs5 csE cs2E !size_cat /= !size_cat /= !size_map.
    rewrite ltn_add2l // !addnS! ltnS -addSn leq_addl //.
  have c1Mcs5 : path hmove c1 cs5.
    rewrite cat_path -[c1](cunliftrK) !path_liftr //=.
    rewrite c1'Pcs1.
    by rewrite last_map lc1'cs1Epp3 -/p1 -p5Ep3 -p4Ep1.
  have lc1cs5E : last c1 cs5 = `c[p].
    rewrite last_cat -[c1](cunliftrK) last_map lc1'cs1Epp3.
    rewrite -lc1csEp csE cs2E last_cat /= last_cat /= -/p1.
    by rewrite p5Ep3 p4Ep1.
  apply: leq_trans (_ : size cs5 < _); last first.
    by rewrite cs2E /= !size_cat !size_map /= 
               ltn_add2l // ltnS -addSnnS leq_addl.
  rewrite ltnS.    
  have /IHm : size cs5 < m.
    rewrite -ltnS.
    by apply: leq_ltn_trans Scs.
  move=> /(_ c1 p c1Mcs5 lc1cs5E) /=.
  by rewrite -/p1 (negPf p1Dp) => ->.
(* now we just need to use the induction principle on the two subpath        *)
have [cs4' [pp5p4Pcs4' lpp5p4cs4'Elpp5p4cs4 scs4'L]] := 
  pathS_restrict HHr pp5p4Pcs4.
rewrite cliftrK in lpp5p4cs4'Elpp5p4cs4 pp5p4Pcs4'.
have Scs3 : size cs3 < m.+1.
  apply: ltn_trans Scs2.
  by rewrite cs2E size_cat /= size_map addnS ltnS leq_addr.
have Scs4 : size cs4 < m.+1.
  apply: ltn_trans Scs2.
  by rewrite cs2E size_cat /= size_map addnS ltnS leq_addl.
have Scs4' : size cs4' < m.+1.
  by apply: leq_ltn_trans Scs4; rewrite scs4'L.
rewrite cs2E /= size_cat /= !size_map.
rewrite size_rpeg_p opegDr // muln1.
have /IH := c2'cs5Epp5 => /(_ Scs3 c2'Pcs3) IHc1.
have c2'E : c2' = `c[p3] by rewrite [LHS]cliftrK.
rewrite c2'E size_rpeg_p eq_sym p5Dp3 muln1 in IHc1.
have p6Dp : p5 != p.
  by apply: contra p5Dp3 => /eqP->; apply/eqP.
move: lc1csEp; rewrite csE cs2E.
rewrite last_cat /= last_cat /= => lpp5p4cs4Epp.
have lpp5cs4'Epp : last (`c[p5]) cs4' = `c[p].
  by rewrite lpp5p4cs4'Elpp5p4cs4 lpp5p4cs4Epp perfect_unliftr.
have /IH : last (`c[p5]) cs4' = `c[p] => 
       [//| /(_ Scs4' pp5p4Pcs4') IHc2].
rewrite size_rpeg_p p6Dp muln1 in IHc2.
rewrite !addnS !ltnS.
apply: leq_trans (leq_addl _ _).
apply: leq_add.
  by apply: leq_trans (size_rpeg_up _ _) _; rewrite IHc1.
apply: leq_trans scs4'L.
by rewrite IHc2.
Qed.

Lemma gdist_size_rpeg n (c1 : _ _ n) p : 
  `d[c1, `c[p]]_hmove = size_rpeg c1 p.
Proof.
apply/eqP; rewrite eqn_leq [size_rpeg _ _]size_rpegE.
have [H1 H2] := rpeg_correct c1 p.
rewrite gdist_path_le //.
have /gpath_connect [p1 p1H] : hconnect c1 (`c[p]).
  by apply: move_connect_rpeg.
rewrite -size_rpegE (gpath_dist p1H) /=.
apply: (rpeg_min (gpath_path p1H)) => //.
by apply: gpath_last p1H.
Qed.

Lemma gdist_perfect n p1 p2 :
   `d[`c[p1], `c[p2]]_(@hmove n) = (2^ n).-1 * (p1 != p2).
Proof. by rewrite gdist_size_rpeg; apply: size_rpeg_p. Qed.

Lemma gdist_perfect_le n c p :
   `d[c, `c[p]]_(@hmove n) <= (2^ n).-1.
Proof. by rewrite gdist_size_rpeg; apply: size_rpeg_up. Qed.

(******************************************************************************)
(* Function that builds a path from a peg to a configuration                  *)
(******************************************************************************)

Definition lpeg n p (c : _ _ n) := rev (belast c (rpeg c p)).

Lemma lpeg_perfect n p : 
  lpeg p (`c[p])  = [::] :> seq (configuration 3 n).
Proof. by rewrite /lpeg rpeg_perfect. Qed.

Lemma lpeg_nil_inv n c p : 
  lpeg p c = [::] -> c = `c[p] :> configuration _ n.
Proof.
have := @rpeg_nil_inv _ c p.
rewrite /lpeg; case: rpeg => //= a l.
by rewrite rev_cons; case: rev.
Qed.

Lemma lpeg_correct n c p (cs := lpeg p c) :
  path (@hmove n) (`c[p]) cs /\ last c cs = c.
Proof.
have HHs := @dsym 3.
have [cMrp lcrpEp] := rpeg_correct c p.
rewrite {}/cs /lpeg -lcrpEp path_move_rev //; split=> //.
case: rpeg => //= c1 cs.
by rewrite rev_cons last_rcons.
Qed.

Lemma size_lpegE n (c : _ _ n) p :
  size_rpeg c p = size (lpeg p c).
Proof. by rewrite size_rev size_belast size_rpegE. Qed.

Lemma lpeg_min n c p cs :
  path (@hmove n) (`c[p]) cs -> last (`c[p]) cs = c ->
  size_rpeg c p <= size cs ?= iff (cs == lpeg p c).
Proof.
(* why this is so complicated???? *)
move=> pPcs lccsEc.
have HHs := @dsym 3.
have cPr : path hmove c (rev (belast (`c[p]) cs)).
  by rewrite -{1}lccsEc path_move_rev.
have lcrEp : last c (rev (belast (`c[p]) cs)) = (`c[p]).
  rewrite -lccsEc; case: (cs)=> //= c3 cs1.
  by rewrite rev_cons last_rcons.
have := rpeg_min cPr lcrEp.
rewrite /lpeg size_rev size_belast.
set u := rev _ ; set v := rpeg _ _.
have -> : (u == v) = (rev (c :: u) == rev (c :: v)).
  rewrite !rev_cons eqseq_rcons eqxx andbT.
  apply/eqP/eqP=> [->//|].
  by rewrite -{2}[u]revK => ->; rewrite revK.
rewrite [c :: v]lastI -/v rev_rcons.
rewrite rev_cons revK -{2}lccsEc -lastI eqseq_cons andbC.
case: eqP=> //; case: eqP => // pDl Hcs; case: pDl.
by have [] := rpeg_correct c p.
Qed.

Fixpoint hanoi {n : nat} : configuration _ n -> configuration _ n -> _ :=
  if n is n1.+1 then
      fun (c1 c2 : configuration _ n1.+1) =>
       let p1 := c1 ldisk in
       let p2 := c2 ldisk in
       let c1' := ↓[c1] in
       let c2' := ↓[c2] in
       if p1 == p2 then [seq ↑[i]_p1 | i <- hanoi c1' c2'] else
       let p := `p[p1, p2] in
       (* one jump *)
       let m1 := size_rpeg c1' p + size_rpeg c2' p in 
       (* two jumps *)
       let m2 := size_rpeg c1' p2 + 2 ^ n1 + size_rpeg c2' p1
       in if m1 <= m2 then 
            [seq ↑[i]_p1 | i <- rpeg c1' p] ++
            [seq ↑[i]_p2 | i <- (`c[p]) :: lpeg p c2'] 
          else
            [seq ↑[i]_p1 | i <- rpeg c1' p2] ++
            [seq ↑[i]_p | i <- (`c[p2]) :: rpeg (`c[p2]) p1] ++
            [seq ↑[i]_p2 | i <- (`c[p1]) :: lpeg p1 c2']
  else fun _ _ => [::].

Lemma hanoi_correct n (c1 c2 : _ _ n) (cs := hanoi c1 c2) :
  path hmove c1 cs /\ last c1 cs = c2.
Proof.
have HHr := @dirr 3.
rewrite {}/cs.
elim: n c1 c2 => /= [c1 c2 |n IH c1 c2].
  by split=> //; apply/ffunP=> [] [].
set p1 := _ ldisk; set p2 := _ ldisk.
set c3 := cliftr _ _; set c4 := cliftr _ _; set c5 := cliftr _ _.
set p := `p[_, _].
case: eqP => [p1Ep2|/eqP p1Dp2].
  have [c1Ph lc1hEc2] := IH (↓[c1]) (↓[c2]).
  rewrite -{1 3}[c1]cunliftrK.
  split; first by rewrite path_liftr.
  by rewrite last_map lc1hEc2 -/p1 p1Ep2 cunliftrK.
case: leqP => _; rewrite !cat_path !last_cat {IH}/= ?cat_path ?last_cat /=.
  split; first (apply/and3P; split).
  - have [c1Pr lc1rEp] := rpeg_correct (↓[c1]) p.
    by rewrite -{1}[c1]cunliftrK path_liftr.
  - rewrite -{1}[c1]cunliftrK last_map.
    have [_ ->] := rpeg_correct (↓[c1]) p.
    apply/moveP; exists ldisk.
    split => // [|d dmDd||].
    - by rewrite !cliftr_ldisk.
    - rewrite !ffunE; case: tsplitP => [j|j jE]; first by rewrite !ffunE.
      by case/eqP: dmDd; apply/val_eqP; rewrite /= jE; case: (j) => [] [].
    - apply/on_topP=> d; rewrite !cliftr_ldisk !ffunE.
      case: tsplitP => [j _ /eqP|j jE].
        by rewrite !ffunE -/p1 eq_sym (negPf (opegDl _ _)).
      by rewrite /= !ffunE jE /= leq_addl. 
    apply/on_topP=> d; rewrite /= !cliftr_ldisk !ffunE.
    case: tsplitP => [j _ /eqP|j ->]; last by case: j => [] [].
    by rewrite !ffunE eq_sym (negPf (opegDr _ _)).  
  - have [cPl Hlc2lEc2] := lpeg_correct (↓[c2]) p.
    by rewrite -[c3]cunliftrK !cliftr_ldisk /= path_liftr // cliftrK.
  have [cPl lc2lEc2] := lpeg_correct (↓[c2]) p.
  rewrite last_map -/p.
  case: lpeg lc2lEc2 (@lpeg_nil_inv _ (↓[c2]) p) => /= [|a l -> _].
    by move=> _ <- //; rewrite cunliftrK.
  by rewrite cunliftrK.
split; first (apply/and5P; split).
- have [c1Pr lc1rEp2] := rpeg_correct (↓[c1]) p2.
  by rewrite -{1}[c1]cunliftrK path_liftr.
- rewrite -{1}[c1]cunliftrK last_map.
  have [_ ->]:= rpeg_correct (↓[c1]) p2.
  apply/moveP; exists ldisk; split => // [|d2||]; 
         rewrite ?cliftr_ldisk ?ffunE //=.
  - by rewrite /drel /= eq_sym opegDl.
  - case: tsplitP => //= j d2E /eqP[].
    by apply/val_eqP; rewrite /= d2E; case: (j) => [] [].
  - apply/on_topP=> d2.
    rewrite cliftr_ldisk /= !ffunE.
    case: tsplitP => [k _ /eqP | [[]] // j -> //].
    by rewrite ?ffunE (negPf p1Dp2).
  apply/on_topP=> d2.
  rewrite cliftr_ldisk /= !ffunE.
  case: tsplitP => [k _ /eqP | [[]] // j -> //].
  by rewrite !ffunE (negPf (opegDr _ _)).
- have [c4Pr lc4rEp1] := rpeg_correct (↓[c4]) p1.
  by rewrite path_liftr //; rewrite cliftrK in c4Pr.
- rewrite -[c4]cunliftrK !cliftr_ldisk /= last_map 
          -[perfect _](cliftrK p).
  have [_ ->]:= rpeg_correct (↓[c4]) p1.
  apply/moveP; exists ldisk; split => // [|d2||]; 
         rewrite ?cliftr_ldisk ?ffunE /=.
  - by rewrite /drel /= opegDr.
  - case: tsplitP => [j | j d2E /eqP[]] //=.
    by apply/val_eqP => /=; rewrite d2E; case: (j) => [] [].
  - apply/on_topP=> d2.
    rewrite cliftr_ldisk /= !ffunE.
    case: tsplitP => [k _ /eqP | [[]] // j -> //].
    by rewrite !ffunE (negPf (opegDl _ _)).
  apply/on_topP=> d2.
  rewrite cliftr_ldisk /= !ffunE.
  case: tsplitP => [k _ /eqP | [[]] // j -> //].
  by rewrite !ffunE eq_sym (negPf p1Dp2).
- have [p1Pl lc2lEc2] := lpeg_correct (↓[c2]) p1.
  by rewrite path_liftr.
have [cPl lc2lEc2] := lpeg_correct (↓[c2]) p1.
rewrite last_map.
case: lpeg lc2lEc2 (@lpeg_nil_inv _ (↓[c2]) p1) => /= [|a l -> _].
  by move=> _ <- //; rewrite cunliftrK.
by rewrite cunliftrK.
Qed.

Lemma hanoi_min n c1 c2 cs :
  path (@hmove n) c1 cs -> last c1 cs = c2 ->
  size (hanoi c1 c2) <= size cs.
Proof.
have HHr := @dirr 3.
have HHs := @dsym 3.
elim: n c1 c2 cs => [p c1 [|]//|n IH c1 c2 cs /=].
set p := `p[_, _]; set p1 := _ ldisk; set p2 := _ ldisk.
case: eqP => [p1Ep2 c1Pcs lc1csEc2|/eqP p1Dp2 c1Pcs lc1csEc2].
  have lcsmEc1m : last c1 cs ldisk = p1 by rewrite lc1csEc2.
  have [cs1 [c1Pcs1 lc1csElcs1 /leq_of_leqif/(leq_trans _)->//]] := 
      pathS_restrict (@dirr 3) c1Pcs.
  by rewrite size_map IH // lc1csElcs1 lc1csEc2.
set u := _ + _; set v := _ + _.
suff : minn u v < size cs.
  rewrite minnC /minn; case: (leqP u) => H1;
      rewrite !size_cat /= ?size_cat /= !addnS ?ltnS
              !size_map -size_rpegE -size_lpegE -/u => Lscs.
    by apply: leq_trans Lscs.
  apply: leq_ltn_trans _ Lscs.
  rewrite -addnS -addSn !addnA !leq_add //.
  rewrite -[2 ^ _]prednK ?expn_gt0 // ltnS.
  by rewrite -size_rpegE; apply: size_rpeg_up.
pose f (c : configuration 3 n.+1) := c ldisk.
have [m Lcs] := ubnP (size cs); elim: m => // m IH1 in cs Lcs c1Pcs lc1csEc2 *.
case: path3SP c1Pcs => // [c1' cs' /= csE c1'Pcs' _|
                           cs1 cs2 p1' p3 p4 c1' c3 p1Dp3 p1Rp3 lc1'cs1Epp4 csE
                          c1'Pcs1 c3Pcs2 _].
  case/eqP: p1Dp2.
  have := congr1 f lc1csEc2.
  rewrite /f  csE -{1}[c1](cunliftrK) last_map.
  by rewrite !cliftr_ldisk.
have p1'Ep1 : p1' = p1 by [].
move: Lcs; rewrite csE size_cat size_map /= addnS ltnS => Lcs.
move: lc1csEc2; rewrite csE last_cat /= => lc3cs2Ec2.
have [/eqP p3Ep2 | p3Dp2] := boolP (p3 == p2).
  have p4Ep : p4 = p.
    apply/eqP; rewrite opeg3E // eq_sym opeg3E // negb_and !negbK eqxx /=.
    by rewrite eq_sym opeg3E // p1Dp3 eq_sym p3Ep2 eqxx.
  have [cs2' [pp4Pcs2' pp4cs2'E scs2'Lscs2]]:= pathS_restrict HHr c3Pcs2.
  rewrite cliftrK in pp4Pcs2' pp4cs2'E.
  apply: leq_trans (leq_add (leqnn _) scs2'Lscs2).
  apply: leq_trans (geq_minl _ _) _.
  apply: leq_add.
    apply: leq_of_leqif (rpeg_min _ _ ) => //.
      by rewrite lc1'cs1Epp4; congr (perfect (`p[_, _])).
  apply: leq_of_leqif (lpeg_min _ _ ); rewrite -p4Ep //.
  by rewrite pp4cs2'E lc3cs2Ec2.
have p3Ep : p3 = p.
  by apply/eqP; rewrite eq_sym opeg3E // -/p1 -p1'Ep1 p1Dp3 eq_sym.
have p4Ep2 : p4 = p2.
  apply/eqP.
  rewrite /p4 p3Ep /p -/p1 -/p2 p1'Ep1 !opeg3E //.
    by rewrite p1Dp2 negbK eqxx.
  by rewrite eq_sym opeg3E // eqxx eq_sym.
case: path3SP c3Pcs2=> // [c3' cs2' p5 cs2E c3'Pcs2' _|
                          cs3 cs4 p5 p6 p7 c3' c4 p5Dp6 p5p6
                          c3'cs3Epp7 cs2E c3'Pcs3 c4Pcs4 _].
  have  := congr1 f lc3cs2Ec2.
  rewrite cs2E /f -[c3]cunliftrK last_map !cliftr_ldisk -/p2 /= 
        => p3Ep2.
  by case/eqP: p3Dp2.
have p5Ep: p5 = p by rewrite /p5 /c3 !cliftr_ldisk.
move: lc3cs2Ec2 Lcs; rewrite cs2E last_cat /= size_cat /= size_map => 
           lc6cs4Ec2 Lcs.
rewrite -addSnnS ltnS.
have [/eqP p6Ep1|p6Dp1] := boolP (p6 == p1).
  have p7Ep2 : p7 = p2.
    apply/eqP.
    by rewrite opeg3E // p5Ep p6Ep1 opeg3E // p1Dp2 eqxx.
  apply: leq_trans (_ : size (map (cliftr p1) cs1 ++ cs4) <= _).
    apply/ltnW/IH1.
    - by rewrite size_cat !size_map (leq_trans _ Lcs) // ltnS;
         rewrite leq_add2l -addSnnS leq_addl.
    - rewrite cat_path -{1}[c1]cunliftrK path_liftr //=.
      rewrite c1'Pcs1.
      by rewrite -{1}[c1]cunliftrK last_map lc1'cs1Epp4 
                 -/p1 -p6Ep1 p4Ep2 -p7Ep2.
    rewrite last_cat -{1}[c1]cunliftrK last_map.
    by rewrite lc1'cs1Epp4 -/p1 -p6Ep1 p4Ep2 -p7Ep2.
  by rewrite size_cat size_map leq_add2l leq_addl.
have p6Ep2 : p6 = p2.
  case: (p6 =P p2) => // /eqP p6Dp2.
  case/negP:  p5Dp6.
  by rewrite p5Ep opeg3E // eq_sym p6Dp1 eq_sym.
have p7Ep1 : p7 = p1.
  apply/eqP.
  by rewrite opeg3E // p5Ep opeg3E // eqxx.
apply: leq_trans (geq_minr _ _) _.
rewrite -[v]addnA leq_add //.
  apply: leq_of_leqif (rpeg_min _ _ ) => //.
  by rewrite lc1'cs1Epp4 p4Ep2.
apply: leq_add.
  rewrite -[2 ^ _]prednK ?expn_gt0 // ltnS.
  have <-: size_rpeg (↓[c3]) p1 = (2 ^ n).-1.
    by rewrite cliftrK size_rpeg_p p4Ep2 eq_sym p1Dp2 muln1.
  apply: leq_of_leqif (rpeg_min _ _) => //.
  by rewrite c3'cs3Epp7 p7Ep1.
have [cs4' [c4'Pcs4' lc4'cs4'Elc4cs4 /leq_of_leqif Lcs4']] := 
      pathS_restrict HHr c4Pcs4.
rewrite cliftrK p7Ep1 in c4'Pcs4'.
rewrite cliftrK p7Ep1 in lc4'cs4'Elc4cs4.
apply: leq_trans Lcs4'.
apply: leq_of_leqif (lpeg_min _ _) => //.
by rewrite lc4'cs4'Elc4cs4 lc6cs4Ec2.
Qed.

Fixpoint size_hanoi {n : nat} : _ _ n -> _ _ n ->  nat :=
  if n is n1.+1 then
      fun c1 c2 : configuration 3 n1.+1 =>
       let p1 := c1 ldisk in
       let p2 := c2 ldisk in
       let c1' := ↓[c1] in
       let c2' := ↓[c2] in
       if p1 == p2 then size_hanoi c1' c2' else
       (* one jump *)
       let p := `p[p1, p2] in
       let m1 := size_rpeg c1' p + size_rpeg c2' p in 
       (* two jumps *)
       let m2 := size_rpeg c1' p2 + 2 ^ n1 + size_rpeg c2' p1
       in (minn m1 m2).+1
  else fun _ _ => 0.

(* size computes the size *)
Lemma size_hanoiE n (c1 c2 : _ _ n) : size_hanoi c1 c2 = size (hanoi c1 c2).
Proof.
elim: n c1 c2 => //= n IH c1 c2.
case: eqP => [E|/eqP NE].
  by rewrite size_map; apply: IH.
set p := `p[_, _].
set x := size_rpeg _ _; set y := size_rpeg _ _.
set z := size_rpeg _ _; set t := size_rpeg _ _.
rewrite fun_if.
rewrite size_cat /= size_cat /= size_cat /= !size_map.
rewrite -!(size_rpegE, size_lpegE) /=.
rewrite -/x -/y -/z -/t.
rewrite size_rpeg_p eq_sym NE muln1 -[_ + t.+1]addSnnS prednK ?expn_gt0 //.
rewrite !addnS.
rewrite /minn !addnA.
case: leqP => LL1; case: leqP => LL2 //.
  by congr (_.+1); apply/eqP; rewrite eqn_leq LL1.
by congr (_.+1); apply/eqP; rewrite eqn_leq ltnW // ltnW.
Qed.

Lemma gdist_hanoi n (c1 c2 : _ _ n) : `d[c1, c2]_hmove = size_hanoi c1 c2.
Proof.
apply/eqP; rewrite eqn_leq.
have [H1 H2] := hanoi_correct c1 c2.
rewrite [size_hanoi _ _]size_hanoiE gdist_path_le //.
have /gpath_connect [p1 p1H] : hconnect c1 c2 by apply:  move_connect.
rewrite (gpath_dist p1H) hanoi_min //; first apply: gpath_path p1H.
by apply: gpath_last p1H.
Qed.

End Hanoi3.