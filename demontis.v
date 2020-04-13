(* Formalisation of the paper by Roberto Demontis                             *)
From mathcomp Require Import all_ssreflect all_fingroup.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Hanoi.

(* the number of disks *)
Variable n : nat.

(* disk 0, 1, ... n (at least one disk) *)
Definition disk := 'I_n.+1.

Implicit Type d : disk.

(* the disk just one unit larger *)
Definition ndisk d : disk := inord (d + 1).

Lemma val_ndisk d : d < n -> ndisk d = d.+1 :> nat.
Proof. by move=> dLn; rewrite inordK addn1. Qed.

Lemma ltn_ndisk d1 d2 : d1 < d2 -> ((d2 == ndisk d1) || (ndisk d1 < d2)).
Proof.
case: d1 => n1 /= n1Ln.
case: d2 => n2 /= n2Ln.
  rewrite leq_eqVlt => /orP[/eqP n1En2 |n1Ln2].
  apply/orP; left; apply/eqP/val_eqP/eqP=> /=.
  by rewrite val_ndisk //= -ltnS n1En2.
apply/orP; right.
by rewrite val_ndisk //= -ltnS (leq_trans _ n2Ln) // ltnS ltnW.
Qed.

(* smallest disk *)
Definition sdisk : disk := ord0.

Lemma val_sdisk : sdisk = 0 :>  nat.
Proof. by []. Qed.

(* largest disk *)
Definition ldisk : disk := ord_max.

Lemma val_ldisk : ldisk = n :>  nat.
Proof. by []. Qed.

(* the number of pegs *)
Variable k : nat.

(* peg 0, 1, ... k (at least one peg) *)
Definition peg := 'I_k.+1.

Implicit Type p : peg.

(* Configuration : function from disk to peg *)
Definition configuration := {ffun disk -> peg}.

Implicit Type c : configuration.

(* All the disks are on the same peg *)
Definition perfect p : configuration := [ffun => p].

Notation "`c[ p ]" := (perfect p).

(* Test if a configuration is perfect *)
Definition is_perfect (c : configuration) := 
  [forall d1 : disk, forall d2 : disk, c d1 == c d2].

Lemma is_perfectP c :
  reflect (forall d1 d2 : disk, c d1 = c d2) (is_perfect c).
Proof.
apply: (iffP forallP) => [H d1 d2| H d1].
  by rewrite (eqP (forallP (H d1) d2)).
by apply/forallP => d2; rewrite (H d1 d2).
Qed.

Lemma perfect_is_perfect p : is_perfect (`c[p]).
Proof. by apply/is_perfectP => d1 d2; rewrite !ffunE. Qed.

(* p is free on c *)
Definition is_free (p : peg) (c : configuration) := 
  [forall d : disk, c d != p].

Lemma is_freeP p c:
  reflect (forall d : disk, c d != p) (is_free p c).
Proof. by apply: (iffP forallP). Qed.

(* c has a free peg *)
Definition has_free (c : configuration) : bool :=
  [exists p : peg, is_free p c].

Lemma has_freeP c :
  reflect (exists p : peg, forall d : disk, c d != p) (has_free c).
Proof.
apply: (iffP existsP) => [[p /is_freeP pH]| [p pH]]; first by exists p.
by exists p; apply/is_freeP.
Qed.

(* equivalent configuration *)

(* two configurations are equivalent if they differ by a permution of peg *)
Definition cequiv (c1 c2 : configuration) :=
  [exists s : 'S_k.+1, forall d : disk, c2 d == s (c1 d)].

Notation " c1 '=c=' c2 " := (cequiv c1 c2) (at level 30).

Lemma cequivP c1 c2 :
  reflect (exists s : 'S_k.+1, forall d : disk, c2 d = s (c1 d))
          (c1 =c= c2).
Proof.
apply: (iffP existsP) => [[s /forallP Hs]|[s sH]].
  by exists s => d; apply/eqP.
by exists s; apply/forallP=> d; apply/eqP.
Qed.

Lemma cequiv_ref : reflexive cequiv.
Proof. by move=> c; apply/cequivP; exists 1%g=> d; rewrite /= permE. Qed.

Lemma cequiv_sym : symmetric cequiv.
Proof.
by move=> c1 c2; apply/cequivP/cequivP => [] [s sH]; 
   exists (s^-1)%g=> d; rewrite sH (permK, permKV).
Qed.

Lemma cequiv_trans : transitive cequiv.
Proof.
move=> c1 c2 c3 /cequivP[s1 s1H] /cequivP[s2 s2H].
apply/cequivP; exists (s1 * s2)%g => d.
by rewrite !permE /= s2H s1H.
Qed.

Lemma cequiv_perfect p1 p2 : `c[p1] =c= `c[p2].
Proof.
by apply/cequivP; exists (tperm p1 p2) => d; rewrite !permE /= !ffunE eqxx.
Qed.

Lemma cequiv_is_perfect c1 c2 : c1 =c= c2 -> is_perfect c1 = is_perfect c2.
Proof.
move=> /cequivP[s sH].
apply/is_perfectP/is_perfectP => dH d1 d2; first by rewrite !sH; congr (s _).
by have := dH d1 d2; rewrite !sH; apply: perm_inj.
Qed.

Lemma cequiv_has_free c1 c2 : c1 =c= c2 -> has_free c1 = has_free c2.
Proof.
move=> /cequivP[s sH].
apply/has_freeP/has_freeP => [] [p pH].
  exists (s p)%g => d; rewrite sH.
  by apply: contraNN (pH d) => /eqP/perm_inj/eqP.
exists (s^-1 p)%g => d. 
have ->: c1 d = (s^-1)%g (s (c1 d)) by rewrite permK.
by apply: contraNN (pH d) => /eqP/perm_inj/eqP; rewrite sH.
Qed.

(* extension of disks with infinity *)
Definition edisk := option disk.

(* a disk is an edisk *)
Definition d2e (d : disk) : edisk := Some d.
Notation " `d[ d ] " := (d2e d).

(* infinity *)
Definition infinity : edisk := None.
Notation "'∞'" := infinity.

(* move is a triple *)
Definition move := (disk * edisk * edisk)%type.

(* default move : it will be used as a default element in search in sequence *)
Definition dmove : move := (sdisk, ∞, ∞).

(* Check if the disk d1 is on top of the disk ed2 in the configuration c
   if ed2 is a disk d2, we check that d1 and d2 are on the same peg in the right
                        order
   if ed2 is infinity, we checj that d is the only element of the peg.
*)
Definition on_top (d1 : disk) (ed2 : edisk) (c : configuration) :=
  let p := c d1 in
  if ed2 is (Some d2) then 
     [&& d1 < d2, c d2 == p & 
         [forall d, ((c d == p) && (d < d2)) ==> (d == d1)]]
  else
     [forall d, (c d == p) ==> (d == d1)].

Lemma on_topP (d1 : disk) (ed2 : edisk) (c : configuration) :
  reflect ( 
      let p := c d1 in
      if ed2 is (Some d2) then 
        [/\ d1 < d2, c d2 = p & forall d : disk, c d = p -> d < d2 -> d = d1]
      else forall d, c d = p -> d = d1)
     (on_top d1 ed2 c).
Proof.
rewrite /on_top; case: ed2 => [d2|].
  apply: (iffP and3P) => [] [H1 H2 H3]; split => //; try by apply/eqP.
    move=> d dH dLd2; have /(_ d) := forallP H3.
    by rewrite dH dLd2 eqxx /= => /eqP.
  apply/forallP => d; apply/implyP=> /andP[H4 H5]; apply/eqP.
  by apply: H3 => //; apply/eqP.
apply: (iffP forallP) => [H d dH | H d].
  by have := H d; rewrite dH eqxx /= => /eqP.
by apply/implyP => /eqP dH; apply/eqP/H.
Qed.

Lemma cequiv_on_top d1 ed2 c1 c2 :
  c1 =c= c2 -> on_top d1 ed2 c1 = on_top d1 ed2 c2.
Proof.
move=> /cequivP[s sH]; apply/on_topP/on_topP; case: ed2.
- move=> d [dH1 dH2 dH3] p; split => // [|d2 d2H d2Ld].
    by rewrite sH [p]sH dH2.
  apply: dH3 => //.
  by apply: (@perm_inj _ s); rewrite -!sH.
- move=> H1 p d dH; apply: H1.
  by apply: (@perm_inj _ s); rewrite -!sH.
- move=> d [dH1 dH2 dH3] p; split => // [|d2 d2H d2Ld].
    by apply: (@perm_inj _ s); rewrite -!sH dH2.
  by apply: dH3 => //; rewrite !sH d2H.
by move=> H1 p d dH; apply: H1; rewrite !sH dH.
Qed.

(* Check if the disk d1 could be put on top of the disk ed2 in the configuration
   c
   if ed2 is a disk d2, we check that d2 is on top of its peg and is bigger than
                        d1
   if ed2 is infinity, we check that there is an empty peg *)
   
Definition valid_top (d1 : disk) (ed2 : edisk) (c : configuration) :=
  if ed2 is (Some d2) then (d1 < d2) && [forall d, (c d == c d2) ==> (d2 <= d)]
  else has_free c.

Lemma valid_topP (d1 : disk) (ed2 : edisk) (c : configuration) :
  reflect (if ed2 is (Some d2) then d1 < d2 /\ forall d, c d = c d2 -> d2 <= d
           else has_free c)
           (valid_top d1 ed2 c).
Proof.
rewrite /on_top; case: ed2 => [d2|]; last by apply: (iffP idP).
apply: (iffP andP) => [] [H1 H2]; split => //.
  by move=> d dH; have := (forallP H2 d); rewrite dH eqxx.
by apply/forallP=> d; apply/implyP => /eqP /H2.
Qed.

Lemma cequiv_valid_top d1 ed2 c1 c2 :
  c1 =c= c2 -> valid_top d1 ed2 c1 = valid_top d1 ed2 c2.
Proof.
move=> c1H; have /cequivP[s sH] := (c1H).
apply/valid_topP/valid_topP; case: ed2.
- move=> d [dH1 dH2]; split => // d2 d1H.
  by apply: dH2; apply: (@perm_inj _ s); rewrite -!sH.
- by move=> c1F; rewrite -(cequiv_has_free c1H).
- move=> d [dH1 dH2]; split => // d2 d1H.
  by apply: dH2; rewrite !sH d1H.
by move=> c1F; rewrite (cequiv_has_free c1H).
Qed.

(* a move is valid, *)
Definition valid_move (m : move) (c : configuration) :=
  let: (d1, ed2, ed3) := m in (on_top d1 ed2 c) && (valid_top d1 ed3 c).

Lemma valid_moveP m c : 
  reflect (let: (d1, ed2, ed3) := m in on_top d1 ed2 c /\ valid_top d1 ed3 c)
          (valid_move m c).
Proof. by case: m => [] [d1 ed2] ed3; apply: (iffP andP). Qed.

Lemma cequiv_valid_move m c1 c2 :
  c1 =c= c2 -> valid_move m c1 = valid_move m c2.
Proof.
move=> c1H; case: m => [] [d1 ed2] ed3; 
  apply/valid_moveP/valid_moveP=> [] [H1 H2]; split.
- by rewrite -(cequiv_on_top _ _ c1H).
- by rewrite -(cequiv_valid_top _ _ c1H).
by rewrite (cequiv_on_top _ _ c1H).
by rewrite (cequiv_valid_top _ _ c1H).
Qed.

(* make a move in a configuration : 
   if ed2 is a disk d2, d1 goes to the same peg as d2
   if ed2 is infinity we pick a free peg, if there is no, d1 stays on its peg
    *)
Definition make_move (m : move) (c : configuration) : configuration := 
  let: (d1, ed2, ed3) := m in 
  let p := if ed2 is Some d2 then c d2 
         else odflt (c d1) (pick [pred p| is_free p c]) in
  [ffun d => if d == d1 then p else c d].

(* make move only change the value of d1 *)
Lemma make_move_diff d d1 ed2 ed3 (c : configuration) :
  d != d1 -> make_move (d1, ed2, ed3) c d = c d.
Proof. by move=> dDd1; rewrite /make_move ffunE (negPf dDd1). Qed.

(* The sequence s goes from c1 to c2 *)
Fixpoint valid_sequence c1 c2 (s : seq move) :=
  if s is m :: s1 then
    valid_move m c1 && valid_sequence (make_move m c1) c2 s1 
  else c1 == c2.

(* The sequence s goes from peg p1 to peg p2 *)
Definition solving_sequence (s : seq move) (p1 p2 : peg) :=
   valid_sequence `c[p1] `c[p2] s.

(* Find the index in the sequence where d appears first *)
Definition free_index (s : seq move) d := 
  find (fun m => let: (d1,_,_) := m in d == d1) s.

(* Before the index there is not d *)
Lemma before_free_index p1 p2 (s : seq move) d i d1 ed2 ed3 :
  i < free_index s d -> nth dmove s i = (d1, ed2, ed3) -> d1 != d.
Proof.
move=> iLf nE.
have := before_find dmove iLf.
by rewrite nE eq_sym => ->.
Qed.

(* In a solving sequence we always find an index *)
Lemma size_free_index p1 p2 (s : seq move) d :
  p1 != p2 -> solving_sequence s p1 p2 -> free_index s d < size s.
Proof.
move=> p1Dp2; rewrite /solving_sequence.
have: `c[p1] d = p1 by rewrite ffunE.
elim: s `c[p1] => /= [c1 c1dE /eqP c1E|
                      [] [s1 ed2 ed3] s IH c1 c1dE /andP[mH sH]].
  by case/negP: p1Dp2; rewrite -c1dE c1E ffunE.
case: eqP => // /eqP dDs1.
apply: IH sH.
by rewrite !ffunE (negPf dDs1).
Qed.

(* sanity check : search for the largest disk  *)
Lemma max_free_index p1 p2 (s : seq move) :
  p1 != p2 -> solving_sequence s p1 p2 -> 
  nth dmove s (free_index s ldisk) = (ldisk, ∞, ∞).
Proof.
move=> p1Dp2; rewrite /solving_sequence.
have: `c[p1] ldisk = p1 by rewrite ffunE.
elim: s `c[p1] => /= [c1 c1dE /eqP c1E|
                      [] [s1 ed2 ed3] s IH c1 c1dE /andP[mH sH]].
  by case/negP: p1Dp2; rewrite -c1dE c1E ffunE.
case: eqP => /= [dEs1| /eqP dDs1]; last first.
  apply: IH sH.
  by rewrite !ffunE (negPf dDs1).
move: mH; rewrite -dEs1 /valid_move /on_top /valid_top.
case: {sH}ed2 => /=; first by case => /= m i; rewrite ltnNge -ltnS i.
case: ed3 => //=. 
by case => /= m i; rewrite ltnNge -ltnS i andbF.
Qed.

(* sanity check : search for a smaller disk  *)
Lemma ndisk_free_index p1 p2 (s : seq move) d :
  p1 != p2 -> solving_sequence s p1 p2 ->  d < ldisk ->
  nth dmove s (free_index s d) = (d,`d[ndisk d], ∞).
Proof.
move=> p1Dp2; rewrite /solving_sequence.
have : forall d1, d <= d1 -> `c[p1] d1 = p1 by move=> d1; rewrite ffunE.
elim: s `c[p1] => /=  [c1 c1dE /eqP c1E dLn|
                      [] [d1 ed2 ed3] s IH c1 c1dE 
                           /andP[/valid_moveP[/on_topP oH /valid_topP vH] sH]
                            dLn].
  case/eqP: p1Dp2.
  by rewrite -(c1dE d) // c1E ffunE.
case: eqP => /= [dEd1| /eqP dDd1]; last first.
  apply: IH sH _ => //.
  move=> d2 dLd2.
  rewrite make_move_diff ?c1dE //.
  apply: contra_neq dDd1 => d2Ed1.
  case: ed2 oH => /= [d3 [H1 H2 H3] | H]; last first.
    by apply: H; rewrite !c1dE // -d2Ed1.
  apply: H3 => //.
  rewrite !c1dE // -d2Ed1 //.
  by apply: leq_trans H1; rewrite ltnS -d2Ed1.
rewrite -{d1}dEd1 in oH vH sH |- *. 
case: {sH}ed2 oH => /= [d1 [H1 H2 H3] | H]; last first.
  have dE : ldisk = d by apply: H; rewrite !c1dE //=ltnW.
  by move: dLn; rewrite -dE ltnn.
have /orP[/eqP d1E|ndLd1] := ltn_ndisk H1; last first.
  have /val_eqP/= : ndisk d = d. 
    apply: H3 => //.
    by rewrite !c1dE // val_ndisk.
  by rewrite val_ndisk // eqn_leq ltnn.
rewrite {d1}d1E in H1 H2 H3 |- *.
case: ed3 vH => // d1 [dLd1 d1H].
by move: (dLd1); rewrite ltnNge d1H // !c1dE // ltnW.
Qed.

End Hanoi.