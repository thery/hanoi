From mathcomp Require Import all_ssreflect finmap.
Require Import extra gdist ghanoi ghanoi4 shanoi.

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

Definition apeg n p1 p2 : peg 4 := if odd n then p1 else p2.

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

(* This is lemma 2.1 *)
Lemma sgdist_simple n (p1 p2 p3 : peg 4) (u v : configuration 4 n.+1) : 
   p1 != p2 -> p1 != p3 -> p2 != p3 -> 
   p1 != p0 -> p2 != p0 -> p3 != p0 ->
   u ldisk = p1 -> v ldisk = p3 -> 
   exists s : configuration 4 n, exists t : configuration 4 n, 
     [/\ (codom s) \subset [:: p2; p3], codom t \subset [:: p1; p2] & 
         d[u, v] = D[[:: cunliftr u; s; t; cunliftr v]].+2].
Proof.
move=> p1Dp2 p1Dp3 p2Dp3 p1Dp0 p2Dp0 p3Dp0 uld vld.
have pE p : [\/ p = p0, p = p1, p = p2 | p = p3].
  move: p1Dp2 p1Dp3 p2Dp3 p1Dp0 p2Dp0 p3Dp0; rewrite /p0.
  by case: (peg4E p1) => ->; rewrite ?eqxx //; 
     case: (peg4E p2) => ->; rewrite ?eqxx //; 
     case: (peg4E p3) => ->; rewrite ?eqxx //; 
     case: (peg4E p) => ->; rewrite ?eqxx // => *; 
     try ((by apply: Or41) || (by apply: Or42) || 
          (by apply: Or43) || (by apply: Or44)).
have [cs /= csH] := gpath_connect (shanoi_connect u v).
have vIcs : v \in cs.
  have := mem_last u cs; rewrite (gpath_last csH).
  rewrite inE; case: eqP => //  vEu.
  by case/eqP : p1Dp3; rewrite -vld vEu.
case: (@split_first _ cs (fun c => c ldisk != p1)) => 
     [|sp [cs1 [cs2 ]]].
  apply/negP=> /allP /(_ _ vIcs).
  rewrite /= -topredE /= negbK.
  by rewrite eq_sym vld (negPf p1Dp3).
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
    by move=> /spH; rewrite /= -topredE negbK vld eq_sym (negPf p1Dp3).
  by case/eqP : p3Dp0; rewrite -vld vEs.
case: (@split_last _ (sp :: cs2) (fun c => c ldisk != p3)) => 
     [|/= t [cs3 [cs4 ]]].
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
exists (cunliftr s); exists (cunliftr t); split => //=.
rewrite addn0.
move: csH; rewrite csE => csH.
rewrite (gdist_cat csH) -[@move _ _ _]/smove -/s.
move: csH => /gpath_catr; rewrite -/s => csH.
rewrite gdist_cunlift_eq //; last 2 first.
- by apply: shanoi_connect.
- by rewrite sLp1.
rewrite -!addnS.
congr (_ + _)%N.
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
  by rewrite vld.
move: csH; rewrite cs2E -cat_rcons => csH.
rewrite (gdist_cat csH) last_rcons.
rewrite gdist_cunlift_eq //; last 2 first.
- by apply: shanoi_connect.
- by rewrite tLp0.
congr (_ + _)%N.
move: csH => /gpath_catr; rewrite last_rcons => csH.
rewrite (gdist_cons csH); congr (_).+1.
move: csH => /gpath_consr csH.
rewrite ctEctp gdist_cunlift_eq //.
- by apply: shanoi_connect.
by rewrite vld.
Qed.

End sHanoi4.


