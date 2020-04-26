(******************************************************************************)
(*                                                                            *)
(*                     Generalised Hanoi Problem                              *)
(*                                                                            *)
(******************************************************************************)
(*                                                                            *)
(*      We consider a generalisation of Hanoi problem :                       *)
(*        a parameter n : the number of pegs                                  *)
(*        a parameter r : r p1 p2 tells that a disk can go from p1 -> p2      *)
(*                                                                            *)
(*    peg n             == type for pegs  (there are n pegs)                  *)
(*    disk k            == type for disks (there are k disk)                  *)
(*    configuration k n == type for hanoi configuration with                  *)
(*                         k disks and n pegs                                 *)
(*    ldisk             == the largest disk                                   *)
(*    sdisk             == the smallest disk                                  *)
(*    d1 \larger d2     == disk d1 is larger than disk d2                     *)
(*    c d               == the peg on which the disk d in the configuration c *)
(*    perfect n p       == a configuration with n disk where all the disks    *)
(*    `p[p1, p2]        == pick a peg (if possible) that is diffenent from p1 *)
(*                         and p2                                             *)
(*                         are on peg p                                       *)
(*    on_top d c        == the disk c is on top of its peg on the             *)
(*                         configuration c                                    *)
(*    drel              == a diff relation between pegs, drel p1 p2 is true   *)
(*                         iff peg p1 is different from peg p2                *)
(*    lrel              == a linear relation between pegs, lrel p1 p2 is      *)
(*                         true iff peg p1 is next to peg p2                  *)
(*    move r c1 c2      == checks if going from configuration c1              *)
(*                         to configuration c2 is a move compatible with      *)
(*                         relation r (a relation over pegs)                  *)
(*   cdisjoint c1 c2    == configurations c1 and c2 are on different pegs     *) 
(*   cmerge c1 c2       == merge a configuration c1 with m disk and a         *)
(*                         a configuration with n disks to get a configuration*) 
(*                         with m + n disk                                    *)
(*   crshift c          == right shift a configuration c with m + n disks, to *)
(*                         get a configuration with n disks taking the disks  *)
(*                         larger than m                                      *)
(*   clshift c          == right shift a configuration c with m + n disks, to *)
(*                         get a configuration with n disks taking the disks  *)
(*                         smaller than m                                     *)
(*   ↑[c]_ p            == lift a configuration by adding a largest disk on   *)
(*                         peg p. This lifting is done from the largest one   *)
(*                         so to accomodate the usual induction               *)
(*   ↓[c]               == unlift a configuration by removing the largest     *)
(*                         disk                                               *)
(*   plift i p          == lift a configuration by adding a new empty peg i   *)
(*                                                                            *)
(******************************************************************************)

From mathcomp Require Import all_ssreflect.
Require Import tsplit gdist.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section GHanoi.

Variable q : nat.

(*****************************************************************************)
(*  The pegs are the elements of 'I_q                                        *)
(*****************************************************************************)

Definition peg := 'I_q.
Variable r : rel peg.
Hypothesis irH : irreflexive r.
Hypothesis symH : symmetric r.


Section Disk.
(*****************************************************************************)
(* The disks are represented with the element of 'I_n with                   *)
(* the idea that disk d1 is larger than disk d2 is d2 <= d1.                 *)
(*****************************************************************************)

Variable n : nat.
Definition disk := 'I_n.
Definition mk_disk m (H : m < n) : disk := Ordinal H.

(******************************************************************************)
(* Given a configuration c, the disks on the peg p can be reconstructed by    *)
(* the list in decreasing order of the disk d such that c d = p               *)
(******************************************************************************)

Definition configuration := {ffun disk -> peg}.

(* A perfect configuration is one where all the pegs are on a single peg p *)
Definition perfect p : configuration :=  [ffun d => p].

End Disk.

(* The smallest disk *)
Definition sdisk {n} : disk n.+1 := ord0.

(* The largest disk *)
Definition ldisk {n} : disk n.+1 := ord_max.

(******************************************************************************)
(* The disk d is on top of peg (c d)                                          *)
(******************************************************************************)

Definition on_top n (d : disk n) (c : configuration n) :=
   [forall d1 : disk n, (c d == c d1) ==> (d <= d1)].

Lemma on_topP n (d : disk n) (c : configuration n) :
  reflect (forall d1, c d = c d1 -> d <= d1) (on_top d c).
Proof.
apply: (iffP forallP) => [H d1 cdEcd1|H d1].
  by have /implyP->// := H d1; apply/eqP.
by apply/implyP=> /eqP /H.
Qed.

(******************************************************************************)
(* A move is a relation between two configurations c1 c2:                     *)
(* there must exist a disk d1, that is the only one that has changed of       *)
(* peg (c1 d1 != c2 d1) that is on top of c1 and c2                           *)
(******************************************************************************)


Definition move {n} : rel (configuration n) :=
   [rel c1 c2 | [exists d1 : disk n, 
                  [&& r ((c1 : configuration n) d1) (c2 d1),
                      [forall d2, (d1 != d2) ==> (c1 d2 == c2 d2)],
                      on_top d1 c1 & 
                      on_top d1 c2]]].

Lemma moveP n (c1 c2 : configuration n) :
  reflect 
    (exists d1, 
         [/\ r (c1 d1) (c2 d1),
             forall d2, d1 != d2 -> c1 d2 = c2 d2,
             on_top d1 c1 &
             on_top d1 c2])
    (move c1 c2).
Proof.
apply: (iffP existsP) =>
  [[d /and4P[H1 /forallP H2 H3 H4]]|[d [H1 H2 H3 H4]]]; exists d.
  by split => // d1 H; apply/eqP/(implyP (H2 _)).
rewrite H1 H3 H4 ! andbT /=; apply/forallP => d1; apply/implyP => H.
by rewrite H2.
Qed.

Lemma move_on_topl n d (c1 c2 : configuration n) : 
  move c1 c2 -> c1 d != c2 d -> on_top d c1.
Proof.
case/moveP => d1 [H1 H2 H3 H4 H5].
rewrite (_ : d = d1); first by apply: H3.
apply/eqP; case: eqP => /eqP H //.
by case/eqP: H5; apply: H2; rewrite eq_sym.
Qed.

Lemma move_on_topr n d (c1 c2 : configuration n) : 
  move c1 c2 -> c1 d != c2 d -> on_top d c2.
Proof.
case/moveP => d1 [H1 H2 H3 H4 H5].
rewrite (_ : d = d1); first by apply: H4.
apply/eqP; case: eqP => /eqP H //.
by case/eqP: H5; apply: H2; rewrite eq_sym.
Qed.

(* this holds if r is symmetric *)
Lemma move_sym n (c1 c2 : configuration n) : move c1 c2 = move c2 c1.
Proof.
by apply/moveP/moveP=> [] [d [H1 H2 H3 H4]];
   exists d; split; rewrite 1?symH 1?eq_sym // => e dDe; apply/sym_equal/H2.
Qed.

(* In a move, the disk that moves accomodates r                              *)
Lemma move_diskr n (d : disk n) (c1 c2 : configuration n) : 
  move c1 c2 -> c1 d != c2 d -> r (c1 d) (c2 d).
Proof.
case/moveP=> d1 [H1 H2 H3 H4] /eqP c1dDc2d.
by have [/eqP<-|/H2] := boolP (d1 == d).
Qed.

(* In a move, only one disk moves *)
Lemma move_disk1 n (d1 d2 : disk n) (c1 c2 : configuration n) : 
  move c1 c2 -> c1 d1 != c2 d1 -> d1 != d2 -> c1 d2 = c2 d2.
Proof.
case/moveP=> d3 [H1 H2 H3 H4] c1d1Dc2d1 d1Dd2.
have [/eqP d3Ed1|d3Dd1] := boolP (d3 == d1); last first.
  by case/eqP: c1d1Dc2d1; apply: H2.
by apply: H2; rewrite d3Ed1.
Qed.

Lemma move_on_toplDl n (d d1 : disk n) (c1 c2 : configuration n) : 
  move c1 c2 -> c1 d != c2 d -> d1 < d -> c1 d1 != c1 d.
Proof.
move=> c1Mc2 c1Dc2; rewrite  eq_sym ltnNge; apply: contra => /eqP.
by have /on_topP := move_on_topl c1Mc2 c1Dc2; apply.
Qed.

Lemma move_on_toplDr n (d d1 : disk n) (c1 c2 : configuration n) : 
  move c1 c2 -> c1 d != c2 d -> d1 <= d -> c1 d1 != c2 d.
Proof.
move=> c1Mc2 c1Dc2; rewrite leq_eqVlt => /orP[/val_eqP->//|dLd1].
move: (dLd1); rewrite eq_sym ltnNge (move_disk1 c1Mc2 c1Dc2) //; last first.
  by rewrite neq_ltn dLd1 orbT.
apply: contra => /eqP.
by have /on_topP := move_on_topr c1Mc2 c1Dc2; apply.
Qed.

Lemma move_on_toprDr n (d d1 : disk n) (c1 c2 : configuration n) : 
  move c1 c2 -> c1 d != c2 d -> d1 < d -> c2 d1 != c2 d.
Proof.
move=> c1Mc2 c1Dc2; rewrite  eq_sym ltnNge; apply: contra => /eqP.
by have /on_topP := move_on_topr c1Mc2 c1Dc2; apply.
Qed.

Lemma move_on_toprDl n (d d1 : disk n) (c1 c2 : configuration n) : 
  move c1 c2 -> c1 d != c2 d -> d1 <= d -> c2 d1 != c1 d.
Proof.
move=> c1Mc2 c1Dc2; rewrite leq_eqVlt => /orP[/val_eqP->//|dLd1].
  by rewrite eq_sym.
move: (dLd1); rewrite ltnNge -(move_disk1 c1Mc2 c1Dc2) eq_sym //; last first.
  by rewrite neq_ltn dLd1.
apply: contra => /eqP.
have /on_topP := move_on_topl c1Mc2 c1Dc2; apply.
Qed.

(* configuration on different pegs *)
Definition cdisjoint m n (c1 : configuration m) (c2 : configuration n) :=
  [forall i, [forall j, c1 i != c2 j]].

Lemma cdisjointP m n (c1 : configuration m) (c2 : configuration n) :
  reflect (forall i j, c1 i != c2 j) (cdisjoint c1 c2).
Proof.
apply: (iffP forallP) => [H i j| H i].
  by move/forallP : (H i); apply.
by apply/forallP=> j; apply: H.
Qed.

(* merging two configurations : c1 for the small disks, c2 for the big ones *)
Definition cmerge m n (c1 : configuration m) (c2 : configuration n) :=
  [ffun i => match tsplit i with inl j => c1 j | inr j => c2 j end].

(* right shifting a configuration : taking the disks smaller than n *)
Definition crshift m n (c : configuration (m + n)) : configuration n := 
   [ffun i => c (trshift m i)].

(* left shifting a configuration : taking the disks larger than n *)
Definition clshift m n (c : configuration (m + n)) : configuration m := 
   [ffun i => c (tlshift n i)].

(* Sanity check *)
Lemma cmergeK m n (c : configuration (m + n)) :
  cmerge (clshift c) (crshift c) = c.
Proof.
apply/ffunP=> i; rewrite !ffunE.
by case: tsplitP => [] j iE; rewrite !ffunE /=;
   congr fun_of_fin; apply/val_eqP/eqP.
Qed.

Lemma tsplit_tlshift k m (x : 'I_k) : tsplit (tlshift m x) = inl x.
Proof.
case: tsplitP=> [j /= jE|k1 /= /eqP].
  by have := ltn_ord j; rewrite -jE ltnNge leq_addl.
rewrite eqn_add2r => /eqP H.
by congr (inl _); apply: val_inj.
Qed.

Lemma tsplit_trshift k m (x : 'I_k) : tsplit (trshift m x) = inr x.
Proof.
case: tsplitP => [j /= jE|k1 /= xE].
  by congr (inr _); apply: val_inj.
by have := ltn_ord x; rewrite xE ltnNge leq_addl.
Qed.

Lemma on_top_merger m n x (c1 : configuration m) (c2 : configuration n) : 
  on_top (trshift m x) (cmerge c1 c2) = on_top x c2.
Proof.
apply/on_topP/on_topP.
  move=> Hx d2 cxEcd2.
  have := Hx (trshift m d2).
  by rewrite !ffunE !tsplit_trshift => /(_ cxEcd2).
move=> H d; rewrite !ffunE tsplit_trshift /=.
case: tsplitP => [j -> H1 | k -> _].
  by apply: H.
by apply: leq_trans (ltnW _) (leq_addl _ _).
Qed.

Lemma move_merger m n (c : configuration n) (c1 c2 : configuration m) :
    move (cmerge c c1) (cmerge c c2) = move c1 c2.
Proof.
apply/moveP/moveP => [] [d1 [H1d1 H2d1 H3d1 H4d1]]; last first.
  exists (trshift n d1); split => //; try by rewrite on_top_merger.
    by rewrite !ffunE /= tsplit_trshift.
  move=> d2; rewrite !ffunE; case: tsplitP => // k d2E H.
  apply: H2d1 => //; apply: contra H => /eqP->.
  by apply/eqP/val_eqP/eqP.
move: H1d1; rewrite !ffunE.
case: tsplitP => [j jE H1x|k _]; last by rewrite irH.
have d1E : (trshift n j) = d1 by apply/val_eqP/eqP.
rewrite -d1E in H3d1 H4d1.
exists j; split => //; try by rewrite -(on_top_merger _ c).
move=> d2 kDd2.
have := H2d1 (trshift n d2).
rewrite !ffunE tsplit_trshift => H.
apply: H.
apply: contra kDd2 => /eqP/val_eqP /=.
by rewrite jE.
Qed.

Lemma path_merger m n (c1 : configuration m)
         (c2 : configuration n) (cs : seq (configuration _)) :
    path move (cmerge c1 c2) [seq cmerge c1 c | c <- cs]  = 
    path move c2 cs.
Proof. by elim: cs c2 => //= c3 cs IH c2; rewrite move_merger IH. Qed.

Lemma connect_merger m n (c : configuration m) (c1 c2 : configuration n) : 
  connect move c1 c2 -> connect move (cmerge c c1) (cmerge c c2).
Proof.
move=> /connectP[x]; rewrite -(path_merger c) => Hp Hl.
apply/connectP; eexists; first exact: Hp.
by rewrite Hl [RHS]last_map.
Qed.

(* this should be equality *)
Lemma gdist_merger m n (c: configuration m) (c1 c2 : configuration n) : 
  connect move c1 c2 ->
  `d[cmerge c c1, cmerge c c2]_move <= `d[c1, c2]_move.
Proof.
move=> /gpath_connect[p1 p1H].
rewrite (gpath_dist p1H) -(size_map (cmerge c)).
apply: gdist_path_le; first by rewrite path_merger (gpath_path p1H).
by rewrite [LHS]last_map (gpath_last p1H).
Qed.

Lemma on_top_mergel m n (c1 : configuration m) (c2 : configuration n) d :
  cdisjoint c1 c2 -> on_top d c1 -> on_top (tlshift n d) (cmerge c1 c2).
Proof.
move=> c1Dc2 /on_topP dTc; apply/on_topP => d1.
rewrite !ffunE tsplit_tlshift /=.
case: tsplitP => j -> c1dc1j; last first.
  by rewrite leq_add2r; apply: dTc.
by have /cdisjointP/(_ d j)/eqP[] := c1Dc2.
Qed.

Lemma on_top_mergel_inv m n (c1 : configuration m) (c2 : configuration n) d :
  on_top (tlshift n d) (cmerge c1 c2) -> on_top d c1.
Proof.
move=> /on_topP dTc; apply/on_topP => d1 Hc.
have := dTc (tlshift n d1).
by rewrite !ffunE !tsplit_tlshift /= leq_add2r; apply.
Qed.

Lemma move_mergel m n (c1 c2 : configuration m) (c : configuration n) :
  move (cmerge c1 c) (cmerge c2 c) -> move c1 c2.
Proof.
move=> /moveP [x [H1x H2x H3x H4x]]; apply/moveP.
move: H1x; rewrite !ffunE.
case: tsplitP => [j | k kE J1x]; first by rewrite irH.
have xE : (tlshift n k) = x by apply/val_eqP/eqP.
rewrite -xE in H3x H4x.
exists k; split => //; try by apply: on_top_mergel_inv; eassumption.
move=> d2 kDd2.
have := H2x (tlshift n d2).
rewrite !ffunE tsplit_tlshift => H.
apply: H.
apply: contra kDd2 => /eqP/val_eqP /=.
by rewrite kE eqn_add2r.
Qed.

Lemma move_mergel_inv m n (c1 c2 : configuration m) 
                          (c : configuration n) :
  cdisjoint c1 c -> cdisjoint c2 c ->
  move c1 c2 -> move (cmerge c1 c) (cmerge c2 c).
Proof.
move=> c1Dc c2Dc /moveP[x [H1x H2x H3x H4x]]; apply/moveP.
exists (tlshift n x); split => //; try by apply/on_top_mergel.
  by rewrite !ffunE /= tsplit_tlshift.
move=> d2; rewrite !ffunE; case: tsplitP => // k d2E H.
apply: H2x => //; apply: contra H => /eqP->.
by apply/eqP/val_eqP/eqP.
Qed.

Lemma path_mergel m n (c1 : configuration m)
         (c2 : configuration n) (cs : seq (configuration _)) :
    path move (cmerge c1 c2) [seq cmerge i c2 | i <- cs] -> 
    path move c1 cs.
Proof. by elim: cs c1 => //= c3 cs IH c1 /andP[/move_mergel-> /IH]. Qed.

Lemma path_mergel_inv m n (c1 : configuration m)
         (c2 : configuration n) (cs : seq (configuration _)) :
    all (fun i => cdisjoint i c2) (c1 :: cs) ->
    path move c1 cs ->
    path move (cmerge c1 c2) [seq cmerge i c2 | i <- cs].
Proof.
elim: cs c1 => //= c3 cs IH c1 /and3P[c1Dc2 c3Dc2 Dcs] 
                               /andP[/move_mergel_inv ->// /IH->//].
by rewrite c3Dc2.
Qed.

Lemma on_top_shift m n (c : configuration (m + n)) d :
  on_top d c -> 
  match tsplit d with
  | inl d1 => on_top d1 (clshift c)
  | inr d2 => on_top d2 (crshift c)
  end.
Proof.
rewrite -{1}[d](tsplitK d).
case: tsplitP => /= j dE /on_topP /= dT; 
    apply/on_topP => d1; rewrite !ffunE /= => H.
 by apply: dT H.
by have /= := dT _ H; rewrite leq_add2r.
Qed.

Lemma move_clshift m n (c1 c2 : configuration (m + n)) : 
  move c1 c2 -> (clshift c1) != (clshift c2) ->
  move (clshift c1) (clshift c2).
Proof.
move=> /moveP [x].
rewrite -(tsplitK x).
have := @on_top_shift _ _ c1 x.
have := @on_top_shift _ _ c2 x.
case: tsplitP => /= [j xE c2H c1H [H1j H2j H3j H4j] c1Dc2|
                      k xE c2H c1H [H1k H2k H3k H4k] c1Dc2].
  case/eqP: c1Dc2; apply/ffunP => i.
  rewrite !ffunE.
  apply/H2j/eqP/val_eqP; rewrite eqn_leq /= negb_and.
  by rewrite orbC -ltnNge (leq_trans (ltn_ord _)) // leq_addl.
apply/moveP; exists k; split=> [|d2 kDd2||]; rewrite ?ffunE //.
- apply: H2k => /=.
  by apply/eqP/val_eqP; rewrite /= eqn_add2r; apply/val_eqP/eqP.
- apply: c1H; rewrite (_ : x = (tlshift n k)) //.
  by apply/val_eqP/eqP => /=.
apply: c2H; rewrite (_ : x = (tlshift n k)) //.
by apply/val_eqP/eqP => /=.
Qed.

Lemma move_crshift m n (c1 c2 : configuration (m + n)) : 
  move c1 c2 -> (crshift c1) != (crshift c2) ->
  move (crshift c1) (crshift c2).
Proof.
move=> /moveP [x].
rewrite -(tsplitK x).
have := @on_top_shift _ _ c1 x.
have := @on_top_shift _ _ c2 x.
case: tsplitP => /= [j xE c2H c1H [H1j H2j H3j H4j] c1Dc2|
                      k xE c2H c1H [H1k H2k H3k H4k] c1Dc2]; last first.
  case/eqP: c1Dc2; apply/ffunP => i.
  rewrite !ffunE.
  apply/H2k/eqP/val_eqP; rewrite eqn_leq /= negb_and.
  by rewrite -ltnNge  (leq_trans (ltn_ord _)) // leq_addl.
apply/moveP; exists j; split=> [|d2 kDd2||]; rewrite ?ffunE //.
- by apply: H2j.
- apply: c1H; rewrite (_ : x = (trshift m j)) //.
  by apply/val_eqP/eqP => /=.
apply: c2H; rewrite (_ : x = (trshift m j)) //.
by apply/val_eqP/eqP => /=.
Qed.

Fixpoint rm_dup (A : eqType) (a : A) (s : seq A) := 
  if s is b :: s1 then 
    if a == b then rm_dup b s1 else b :: rm_dup b s1 
  else [::].

Lemma size_rm_dup (A : eqType) (a : A) s : size (rm_dup a s) <= size s.
Proof.
elim: s a => //= b l IH a; case: (_ == _); first by apply: leq_trans (IH _) _.
by apply: IH.
Qed.

Lemma size_rm_dup_subset  (A : finType) (a : A) (s1 : {set A}) (s2 : seq A) : 
  {subset s1 <= s2} -> a \notin s1 -> #|s1| <= size (rm_dup a s2).
Proof.
elim: s2 s1 a => /= [s1 a aS _|b s2 IH s1 a s1S aNIs1].
  rewrite leqn0 cards_eq0; apply/eqP/setP=> i.
  by rewrite inE; apply/idP => /aS.
case: eqP=> [aEb|aDb].
  rewrite -aEb; apply: IH => //.
  move=> i is1; have := is1; have := s1S _ is1; rewrite inE.
  by case/orP=> [/eqP->|//]; rewrite -aEb => aIs1; case/negP: aNIs1. 
have [bIs1|bNIs1]/= := boolP (b \in s1); last first.
  apply: leq_trans (IH _ _ _ bNIs1) _ => //.
  move=> i is1; have := is1; have := s1S _ is1; rewrite inE.
  by case/orP=> [/eqP->|//] => bIs1; case/negP: bNIs1.
rewrite (cardsD1 b) bIs1 ltnS.
apply: IH => [i|].
  by rewrite !inE => /andP[iDb1 /s1S]; rewrite inE (negPf iDb1).
by rewrite !inE eqxx.
Qed.

Lemma last_rm_dup (A : eqType) (a : A) s : last a (rm_dup a s) = last a s.
Proof.
by elim: s a => //= b l IH a; case: (_ =P _) => /= [->|_]; apply: IH.
Qed.

Lemma cat_rm_dup (A : eqType) (a : A) s1 s2 : 
  rm_dup a (s1 ++ s2) = rm_dup a s1 ++ rm_dup (last a s1) s2.
Proof.
elim: s1 s2 a => //= b s1 IH s2 a.
case: eqP => [aEb|aDb] /=; first by apply: IH.
by congr (_ :: _); apply: IH.
Qed.

Lemma path_clshift m n (c : configuration (m + n)) cs :
    path move c cs ->
    path move (clshift c) (rm_dup (clshift c) [seq (clshift i) | i <- cs]).
Proof.
elim: cs c => //= c1 cs IH c => /andP[cMc1 c1Pcs].
case: eqP => [->|/eqP cDc1 /=]; first by apply: IH.
by rewrite move_clshift //=; apply: IH.
Qed.

Lemma path_crshift m n (c : configuration (m + n)) cs :
    path move c cs ->
    path move (crshift c) (rm_dup (crshift c) [seq (crshift i) | i <- cs]).
Proof.
elim: cs c => //= c1 cs IH c => /andP[cMc1 c1Pcs].
case: eqP => [->|/eqP cDc1 /=]; first by apply: IH.
by rewrite move_crshift //=; apply: IH.
Qed.

Lemma path_shift  m n (c : configuration (m + n)) cs :
    path move c cs ->
    size cs = size (rm_dup (clshift c) [seq (clshift i) | i <- cs]) +
               size(rm_dup (crshift c) [seq (crshift i) | i <- cs]).
Proof.
elim: cs c => //= c1 cs IH c /andP[/moveP[d [d2H d2H1 d2H2 d2H3]] c1Pcs].
case: (tsplitP d) => [j dE | k dE].
  rewrite ifT; last first.
    apply/eqP/ffunP=> i; rewrite !ffunE.
    apply: d2H1; apply/eqP => /val_eqP /=.
    by rewrite dE eqn_leq andbC leqNgt (leq_trans (ltn_ord _)) ?leq_addl.
  rewrite ifN /=; last first.
    apply/eqP => /ffunP /(_ j); rewrite !ffunE => cE.
    move: d2H; rewrite (_ : c d = c1 d) ?(irH) //.
    by rewrite (_ : d = (trshift m j)) //=; apply/val_eqP/eqP.
  rewrite addnS; congr _.+1.
  by apply: IH.
rewrite ifN /=; last first.
  apply/eqP => /ffunP /(_ k); rewrite !ffunE => cE.
  move: d2H; rewrite (_ : c d = c1 d) ?(irH) //.
  by rewrite (_ : d = (tlshift n k)) //=; apply/val_eqP/eqP.
rewrite ifT; last first.
  apply/eqP/ffunP=> i; rewrite !ffunE.
  apply: d2H1; apply/eqP => /val_eqP /=.
  by rewrite dE eqn_leq leqNgt (leq_trans (ltn_ord _)) ?leq_addl.
congr _.+1.
by apply: IH.
Qed.
    
Lemma gdist_clshift n m (c1 c2 : configuration (m + n)) : 
  connect move c1 c2 ->
  `d[clshift c1, clshift c2]_move <= `d[c1, c2]_move.
Proof.
move=> /gpath_connect[p pH].
have := size_rm_dup (clshift c1) [seq (clshift i) | i <- p].
rewrite (gpath_dist pH) size_map; move/(leq_trans _); apply.
apply: gdist_path_le; first by apply/path_clshift/(gpath_path pH).
by rewrite last_rm_dup last_map (gpath_last pH).
Qed.

Lemma gdist_crshift n m (c1 c2 : configuration (m + n)) : 
  connect move c1 c2 ->
  `d[crshift c1, crshift c2]_move <= `d[c1, c2]_move.
Proof.
move=> /gpath_connect[p pH].
have := size_rm_dup (crshift c1) [seq (crshift i) | i <- p].
rewrite (gpath_dist pH) size_map; move/(leq_trans _); apply.
apply: gdist_path_le; first by apply/path_crshift/(gpath_path pH).
by rewrite last_rm_dup last_map (gpath_last pH).
Qed.

Lemma gdist_cshift n m (c1 c2 : configuration (m + n)) : 
  connect move c1 c2 ->
  `d[clshift c1, clshift c2]_move + `d[crshift c1, crshift c2]_move 
       <= `d[c1, c2]_move.
Proof.
move=> /gpath_connect[p pH].
rewrite (gpath_dist pH) (path_shift (gpath_path pH)).
apply: leq_add.
  apply: gdist_path_le; first by apply/path_clshift/(gpath_path pH).
    by rewrite last_rm_dup last_map (gpath_last pH).
apply: gdist_path_le; first by apply/path_crshift/(gpath_path pH).
by rewrite last_rm_dup last_map (gpath_last pH).
Qed.

Definition cliftrn m n p (c : configuration n) : configuration (m + n) :=
  cmerge (perfect m p) c.
Definition cliftr n : _ -> _ -> configuration n.+1 := @cliftrn 1 n.
Notation " ↑[ c ]_ p" := (cliftr p c) (at level 5, format "↑[ c ]_ p").

Definition cliftln m n p (c : configuration m) : configuration (m + n) :=
  cmerge c (perfect n p).

Definition cliftl n c p : configuration (n + 1) := (@cliftln n 1 c p).

Lemma cliftr_ldisk n p (c : configuration n) : ↑[c]_p ldisk = p.
Proof. 
rewrite ffunE; case: tsplitP => /= [j nE|t].
  by have := ltn_ord j; rewrite {2}nE ltnn.
by rewrite ffunE.
Qed.

Lemma on_top_liftrn n m p x (c : configuration n) : 
  on_top (trshift m x) (cliftrn m p c) = on_top x c.
Proof. exact: on_top_merger. Qed.

Lemma move_liftrn n m p (c1 c2 : configuration n) :
    move (cliftrn m p c1) (cliftrn m p c2) = move c1 c2.
Proof. exact: move_merger. Qed.

Lemma path_liftrn n m p (c : configuration n) (cs : seq (configuration _)) :
    path move (cliftrn m p c) (map (cliftrn m p) cs) = 
    path move c cs.
Proof. exact: path_merger. Qed.

Lemma connect_liftrn n m p (c1 c2 : configuration n) : 
  connect move c1 c2 -> connect move (cliftrn m p c1) (cliftrn m p c2).
Proof. exact: connect_merger. Qed.

Lemma gdist_liftrn n m p (c1 c2 : configuration n) : 
  connect move c1 c2 ->
  `d[cliftrn m p c1, cliftrn m p c2]_move <= `d[c1, c2]_move.
Proof. exact: gdist_merger. Qed.

Lemma move_liftr n p (c1 c2 : configuration n) :
  move ↑[c1]_p ↑[c2]_p = move c1 c2.
Proof. by exact: move_liftrn 1 p c1 c2. Qed.

Lemma perfect_liftr n p : ↑[perfect n p]_p = perfect n.+1 p.
Proof.
apply/ffunP => i; rewrite !ffunE.
by case: tsplitP => [j|k]; rewrite !ffunE.
Qed.

Definition cunliftr {n} (c : configuration n.+1) : configuration n :=
  @crshift 1 n c.

Notation " ↓[ c ]" := (cunliftr c) (at level 5, format "↓[ c ]").

Lemma cliftrK n p : cancel (cliftr p) (cunliftr : _ -> configuration n).
Proof. by move=> c; apply/ffunP => i; rewrite !ffunE tsplit_trshift. Qed.

Lemma cunliftrK n (c : configuration n.+1) : ↑[↓[c]]_(c ldisk) = c.
Proof.
apply/ffunP => i; rewrite !ffunE.
case: tsplitP => [] j iE; rewrite !ffunE; congr fun_of_fin;
  apply/val_eqP/eqP => //=.
by rewrite iE; case: (j) => [] [].
Qed.

Lemma cliftr_inj n p : injective (@cliftr n p).
Proof. by move=> c1 c2 c1Ec2; rewrite -[c1](cliftrK p) c1Ec2 cliftrK. Qed.

Lemma map_eqr (T1 T2 : eqType) (f : T1 -> T2) (s1 s2 : seq T1) :
   injective f ->
   ([seq f i | i <- s1] == [seq f i | i <- s2]) = (s1 == s2).
Proof.
elim: s1 s2 => [[|] //|a s1 IH [|b s2]//=] fInj.
rewrite !eqseq_cons IH //.
case: (a =P b) => [->//|]; first by rewrite eqxx.
by case: (f a =P f b) => [/fInj|//].
Qed.

Lemma eq_map_liftr n p (cs1 cs2 : seq (configuration n)) :
 ([seq ↑[i]_p | i <- cs1] == [seq ↑[i]_p | i <- cs2]) = (cs1 == cs2).
Proof. by apply/map_eqr/cliftr_inj. Qed.

Lemma perfect_unliftr n p : ↓[perfect n.+1 p] = perfect n p.
Proof. by apply/ffunP => i; rewrite !ffunE. Qed.

Lemma move_ldisk n (c1 c2 : configuration n.+1) : 
  move c1 c2 -> c1 ldisk != c2 ldisk -> ↓[c1] = ↓[c2].
Proof.
move=> c1Mc2 c10Dc20.
apply/ffunP=> i; rewrite !ffunE /=.
apply: move_disk1 c1Mc2 c10Dc20 _.
apply/eqP/val_eqP => /=.
by rewrite eqn_leq negb_and -ltnNge ltn_ord.
Qed.

Lemma move_unliftr n (c1 c2 : configuration n.+1) :
  c1 ldisk = c2 ldisk -> move ↓[c1] ↓[c2] = move c1 c2.
Proof.
by move=> c1lEc2l; rewrite -(@move_liftr _ (c1 ldisk)) {2}c1lEc2l !cunliftrK.
Qed.

Lemma path_move_rev (n : nat) (c : configuration n) cs : 
  path move (last c cs) (rev (belast c cs)) = path move c cs.
Proof.
by rewrite rev_path; apply: eq_path => c1 c2; exact: move_sym. 
Qed.

Lemma path_liftr n p (c : configuration n) (cs : seq (configuration _)) :
  path move ↑[c]_p [seq ↑[i]_p | i <- cs] = path move c cs.
Proof. by apply: (@path_merger 1). Qed.

Lemma connect_liftr n p (c1 c2 : configuration n) : 
  connect move c1 c2 -> connect move ↑[c1]_p ↑[c2]_p.
Proof. by apply: (@connect_merger 1). Qed.

Lemma gdist_liftr n p (c1 c2 : configuration n) : 
  connect move c1 c2 ->  `d[↑[c1]_p, ↑[c2]_p]_move <= `d[c1, c2]_move .
Proof. by apply: (@gdist_merger 1). Qed.

Lemma path_unlift_eq n (c : configuration n.+1) (cs : seq (configuration _)) :
   (forall c1, c1 \in cs -> c1 ldisk = c ldisk)-> 
    path move ↓[c] [seq ↓[i] | i <- cs] = path move c cs.
Proof.
move=> H.
rewrite -(@path_liftr _  (c ldisk)).
rewrite cunliftrK -map_comp.
congr path.
elim: cs H => //= a cs IH H.
rewrite -{1}(H a).
  by rewrite cunliftrK IH // => v Hv; apply: H; rewrite inE orbC Hv.
by rewrite inE eqxx.
Qed.

Lemma path_unlift n (c : configuration n.+1) (cs : seq (configuration _)) :
  path move c cs ->
  path move ↓[c] (rm_dup ↓[c] [seq ↓[i] | i <- cs]).
Proof. by move=> H; apply: path_crshift. Qed.

Lemma gdist_cunlift n (c1 c2 : configuration n.+1) : 
  connect move c1 c2 -> `d[↓[c1], ↓[c2]]_move <= `d[c1, c2]_move.
Proof. by move=> H; apply: gdist_crshift. Qed.

Lemma perfect_liftrn m n p : cliftrn m p (perfect n p) = perfect (m + n) p.
Proof.
by apply/ffunP => i; rewrite !ffunE; case: tsplitP => j; rewrite !ffunE.
Qed.

(* case distinction that depends if the largest disk has move                 *)
(*  if it has not moved, we get the path on the unlifted configuration        *)
(*  uf it has moved, we get the decomposition till the first move             *)
Inductive pathS_spec (n : nat)  (c : configuration n.+1) 
                                (cs : seq (configuration n.+1)) :
   forall (b : bool), Type
  :=
  pathS_specW : 
    forall (p := c ldisk) (c1 := ↓[c]) (cs1 := [seq ↓[i] | i <- cs]),
      cs = [seq ↑[i]_p | i <- cs1] -> path move c1 cs1 -> pathS_spec c cs true |
  pathS_spec_move : 
    forall (p1 := c ldisk) p2 cs1 cs2
           (c1 := ↓[c])
           (c2 := ↑[last c1 cs1]_p2),
        p1 != p2 -> r p1 p2 -> 
        cs = [seq ↑[i]_p1 | i <- cs1] ++ c2 :: cs2 ->
        path move c1 cs1 -> move ↑[last c1 cs1]_p1 c2 ->
        path move c2 cs2 ->
        pathS_spec c cs true |
  pathS_spec_false : pathS_spec c cs false.

(* Inversion theorem on a path for disk n.+1 *)
Lemma pathSP  n (c : configuration n.+1) cs : pathS_spec c cs (path move c cs).
Proof.
have [Hp|_] := boolP (path _ _ _); last by apply: pathS_spec_false.
pose f (c1 : configuration n.+1) := c1 ldisk != c ldisk.
have [Hh|/hasPn Hn] := boolP (has f cs); last first.
  have csE : cs = [seq ↑[i]_(c ldisk) | i <- [seq ↓[i] | i <- cs]].
    rewrite -map_comp -[LHS]map_id.
    apply/eq_in_map => x /Hn; rewrite negbK => /eqP <-/=.
    by rewrite cunliftrK.
  apply: pathS_specW csE _.
  by rewrite path_unlift_eq // => c1 /Hn; rewrite negbK => /eqP.
pose n1 := find f cs; pose lc1 := nth c cs n1.
pose p1 := c ldisk; pose p2 := lc1 ldisk.
have p1Dp2 : p1 != p2.
  by have := nth_find c Hh; rewrite eq_sym.
pose c1 :=  ↓[c].
pose lcs1 := take n1 cs; pose cs2 := drop n1.+1 cs.
have slcs1 : size lcs1 = n1 by rewrite size_take -has_find Hh.
have Plcs1 c2 : c2 \in lcs1 -> c2 ldisk = p1.
  move=> c2Ilcs1p; move: (c2Ilcs1p).
  rewrite -index_mem slcs1 => /(before_find c) /idP /negP.
  rewrite negbK => /eqP.
  by rewrite -[cs](cat_take_drop n1) nth_cat index_mem c2Ilcs1p nth_index.
pose cs1 := map cunliftr lcs1.
have lcs1E : lcs1 = [seq ↑[i]_p1 | i <- cs1].
  rewrite -map_comp -[LHS]map_id.
  apply/eq_in_map => x /Plcs1 H.
  by rewrite /= -H cunliftrK.
have csE : cs = [seq ↑[i]_p1 | i <- cs1] ++ lc1 :: cs2.
  by rewrite -[cs](cat_take_drop n1.+1)  -cat_rcons -lcs1E 
             (take_nth c) // -has_find.
have Hm : move (last c lcs1) lc1.
 by move: Hp; rewrite csE lcs1E cat_path /= => /and3P[].
have lc1E : lc1 = cliftr p2 (last c1 cs1).
  rewrite /p2.
  have Hd : (last c lcs1) ldisk != lc1 ldisk.
    case: (lcs1) Plcs1 => //= a l -> //.
    by apply: mem_last.
  rewrite last_map -[LHS]cunliftrK.
  congr cliftr.
  apply/ffunP=> i; rewrite !ffunE /=.
  apply/sym_equal/(move_disk1 Hm Hd).
  apply/eqP/val_eqP => /=.
  by rewrite eqn_leq negb_and -ltnNge ltn_ord.
have Hm1 : move ↑[last c1 cs1]_p1 ↑[last c1 cs1]_p2.
  have ->: ↑[last ↓[c] cs1]_p1 = last c lcs1.
    by rewrite -[in LHS]last_map -lcs1E cunliftrK.
  by rewrite -lc1E.
apply: pathS_spec_move (p1Dp2) _ _ _ (Hm1) _ => //.
-  have := @move_diskr _ ldisk _ _ Hm1.
   by rewrite !cliftr_ldisk; apply.
- by rewrite csE lc1E lcs1E.
- rewrite path_unlift_eq => //.
  by move: Hp; rewrite -[cs](cat_take_drop n1) cat_path => /andP[].
rewrite -lc1E.
by move: Hp; rewrite csE cat_path /= => /and3P[].
Qed.

(* we can restrict a path from n.+1 to n by removing all the moves of the     *)
(* largest disk                                                               *)
Lemma pathS_restrict n (c : configuration n.+1) cs :
   path move c cs -> 
   {cs'|
    [/\ path move ↓[c] cs',
        last ↓[c] cs' = ↓[last c cs] &
        size cs' <= size cs ?= 
          iff (cs ==  [seq ↑[i]_(c ldisk) | i <- cs'])]}.
Proof.
elim: cs c => /= [c _|c1 cs IH c /andP[cMc1 /IH[cs1 [c1Pcs1 lccs1Mlc1cs S]]]].
  by exists [::]; split; rewrite ?setd_id //; apply: leqif_refl; rewrite !eqxx.
have [/eqP c1dEcd|c1dDcd] := boolP (c ldisk == c1 ldisk).
  exists (cunliftr c1 :: cs1); split=> //=.
    by rewrite move_unliftr // cMc1.
  by rewrite eqseq_cons c1dEcd cunliftrK eqxx.
have -> : cunliftr c = cunliftr c1 by apply: move_ldisk.
exists cs1; split=> //=.
apply/leqifP; case: eqP=> [H|/= _]; last by rewrite ltnS S.
by rewrite -[_.+1]/(size (c1 :: cs)) H size_map.
Qed.

(* we can restrict a path from n.+1 to n *)
Lemma pathS_restrictD n (c : configuration n.+1) c1 cs :
   path move c cs -> c1 \in cs -> c1 ldisk != c ldisk ->
   {cs'| [/\ path move ↓[c] cs', 
             last ↓[c] cs' = ↓[last c cs] & size cs' < size cs]}.
Proof.
move=> cPcs c1Ics c1dDcd.
have [cs1 [H1 H2 H3]] := pathS_restrict cPcs.
exists cs1; split => //.
move/leqifP : H3; case: eqP => // cs1Ecs.
case/eqP: c1dDcd.
move: c1Ics; rewrite cs1Ecs => /mapP[x xIcs1 ->].
by rewrite cliftr_ldisk.
Qed.

(* connect is symmetric *)
(* there should be a shorter proof since move n is symmetric *)
Lemma connect_sym n : connect_sym (@move n).
Proof.
move=> c1 c2.
apply/connectP/connectP=> [] [p H1 H2].
  exists (rev (belast c1 p)); first by rewrite H2 path_move_rev.
  by case: (p) H2 => [->//|c3 p1 _]; rewrite rev_cons last_rcons.
exists (rev (belast c2 p)); first by rewrite H2 path_move_rev.
by case: (p) H2 => [->//|c3 p1 _]; rewrite rev_cons last_rcons.
Qed.

End GHanoi.

Arguments perfect {q n}.
Arguments cunliftr {q n}.

Notation " ↑[ c ]_ p" := (cliftr p c) (at level 5, format "↑[ c ]_ p").
Notation " ↓[ c ]" := (cunliftr c) (at level 5, format "↓[ c ]").

Lemma on_top1 k (d : disk 1) (c : configuration k 1) : on_top d c.
Proof. by apply/on_topP=> [] [] [] //=; case: d => [] []. Qed.

Section PLift.

Variables n q : nat.
Variables i : disk q.+1.
Variable r1 : rel (disk q).
Variable r2 : rel (disk q.+1).

Let p := lift i.

Hypothesis r2Rr1 : forall i j, r2 (p i) (p j) = r1 i j.

Definition plift (c : configuration q n) : configuration q.+1 n := 
  [ffun j => p (c j)].

Lemma plift_on_top c1 x : on_top x (plift c1) = on_top x c1.
Proof.
apply/on_topP/on_topP => H d; have := H d; rewrite !ffunE => H1 H2; apply: H1.
  by rewrite H2.
by apply: lift_inj H2.
Qed.

Lemma plift_move (c1 c2 : configuration q n) :
  move r2 (plift c1) (plift c2) = move r1 c1 c2.
Proof.
apply/moveP/moveP => [] [x [H1x H2x H3x H4x]]; exists x; split => //.
- by rewrite !ffunE in H1x; rewrite -r2Rr1.
- by move=> d2 xDd2; have := H2x _ xDd2; rewrite !ffunE => /lift_inj.
- by rewrite plift_on_top in H3x.
- by rewrite plift_on_top in H4x.
- by rewrite !ffunE r2Rr1.
- by move=> d2 /H2x; rewrite !ffunE => ->.
- by rewrite plift_on_top.
by rewrite plift_on_top.
Qed.

Lemma plift_path (c1 : configuration q n) cs :
  path (move r2) (plift c1) [seq plift i | i <- cs] =
  path (move r1) c1 cs. 
Proof.
elim: cs c1 => //= c2 cs IH c1.
by rewrite plift_move IH.
Qed.

Lemma gdist_plift (c1 c2 : configuration q n) :
 connect (move r1) c1 c2 ->
  `d[plift c1, plift c2]_(move r2)  <=  `d[c1, c2]_(move r1).
Proof.
move=> /gpath_connect [p1 p1H].
rewrite (gpath_dist p1H) -(size_map plift).
apply: gdist_path_le; first by rewrite plift_path (gpath_path p1H).
by rewrite last_map (gpath_last p1H).
Qed.

Lemma plift_perfect p1 : plift (perfect p1) = perfect (lift i p1).
Proof. by apply/ffunP => j; rewrite !ffunE. Qed.

Lemma cdisjoint_plift_perfect m c : cdisjoint (plift c) (perfect i : _ _ m).
Proof.
apply/cdisjointP=> i1 j1; rewrite !ffunE /p; apply/eqP/val_eqP => /=.
by rewrite eq_sym neq_bump.
Qed.

End PLift.

Section Crlift.

Variable q : nat.
Variable p : peg q.+1.
Variable r1 : rel (disk q).
Variable r2 : rel (disk q.+1).

Hypothesis r2Irr : irreflexive r2.
Hypothesis r1Rr2 : forall i j : disk q, r1 i j = r2 (lift p i) (lift p j).

Lemma move_liftln m n (c1 c2 : configuration q m) :
    move r2 (cliftln n p (plift p c1)) (cliftln n p (plift p c2)) = 
    move r1 c1 c2.
Proof.
apply/idP/idP=> H; last first.
  apply: move_mergel_inv => //.
  - by apply: cdisjoint_plift_perfect.
  - by apply: cdisjoint_plift_perfect.
  by rewrite (@plift_move _ _ _ r1).
have := move_mergel r2Irr H.
by rewrite (@plift_move _ _ _ r1).
Qed.

Lemma path_liftln m n (c : configuration q m) (cs : seq (configuration _ _)) :
    path (move r2) (cliftln n p (plift p c)) (map (cliftln n p \o (plift p)) cs) = 
    path (move r1) c cs.
Proof. by elim: cs c => //= c1 cs1 IH c; rewrite move_liftln IH. Qed.

Lemma connect_liftln m n (c1 c2 : configuration q m) : 
  connect (move r1) c1 c2 -> 
  connect (move r2) (cliftln n p (plift p c1)) 
                    (cliftln n p (plift p c2)).
Proof.
move=> /connectP[x]; rewrite -(path_liftln n) => Hp Hl.
apply/connectP; eexists; first exact: Hp.
by rewrite Hl [RHS]last_map.
Qed.

Lemma gdist_liftln m n (c1 c2 : configuration q m) : 
  connect (move r1) c1 c2 ->
  gdist (move r2) (cliftln n p (plift p c1)) (cliftln n p (plift p c2)) <= 
  gdist (move r1) c1 c2.
Proof.
move=> /gpath_connect[p1 p1H].
rewrite (gpath_dist p1H) -(size_map (cliftln n p \o plift p)).
apply: gdist_path_le; first by rewrite path_liftln (gpath_path p1H).
by rewrite [LHS]last_map (gpath_last p1H).
Qed.

Lemma crliftn_perfect n m p1 :
  cliftln n p (perfect p1) = cliftrn m p1 (perfect p).
Proof. by []. Qed.

End Crlift.

(******************************************************************************)
(*  Other peg                                                                 *)
(******************************************************************************)

Definition opeg n (p1 p2 : peg n.+1) :=
  odflt ord0 [pick i | (i != p1) && (i != p2)].

Lemma opeg_sym n (p1 p2 : peg n.+1) : opeg p1 p2 = opeg p2 p1.
Proof. by congr odflt; apply: eq_pick => p; rewrite andbC. Qed.

Lemma opegDl n (p1 p2 : peg n.+3) : opeg p1 p2 != p1.
Proof.
rewrite /opeg; case: pickP => [x /andP[]//| HD].
have D (p3 p4 : peg n.+3) : (p3 == p4) = (val p3 == val p4).
  by apply/eqP/idP => /val_eqP.
have := HD ldisk; have := HD (inord 1); have := HD (inord 2).
rewrite !D /= !inordK //.
by case: {HD}p1 => [] [|[|[|p1 Hp1]]] /=;
   case: p2 => [] [|[|[|p2 Hp2]]].
Qed.

Lemma opegDr n (p1 p2 : peg n.+3) : opeg p1 p2 != p2.
Proof.
rewrite /opeg; case: pickP => [x /andP[]//| HD].
have D (p3 p4 : peg n.+3) : (p3 == p4) = (val p3 == val p4).
  by apply/eqP/idP => /val_eqP.
have := HD ldisk; have := HD (inord 1); have := HD (inord 2).
rewrite !D /= !inordK //.
by case: {HD}p1 => [] [|[|[|p1 Hp1]]] /=;
   case: p2 => [] [|[|[|p2 Hp2]]].
Qed.

Notation "`p[ p1 , p2 ] " := (opeg p1 p2)
    (format "`p[ p1 ,  p2 ]", at level 60).

Lemma move_liftr_perfect q n (hrel : rel (peg q)) p1 p2 p3 :
  hrel p1 p2 -> p1 != p3 -> p2 != p3 ->
 move hrel ↑[perfect p3 : configuration q n]_p1 ↑[perfect p3]_p2.
Proof.
move=> p1Rp2 p1Dp3 p2Dp3.
apply: (@move_mergel_inv _ _ 1).
- by apply/cdisjointP => i j; rewrite !ffunE.
- by apply/cdisjointP => i j; rewrite !ffunE.
apply/moveP; exists ldisk; split; try by apply: on_top1.
  by rewrite !ffunE.
by case => [] [].
Qed.

Lemma gdist_liftr_perfect q n (hrel : rel (peg q)) p1 p2 p3 :
  irreflexive hrel -> hrel p1 p2 -> p1 != p3 -> p2 != p3 ->
  `d[↑[perfect p3 : configuration q n]_p1, ↑[perfect p3]_p2]_(move hrel) = 1.
Proof.
move=> hirr p1Rp2 p1Dp3 p2Dp3.
apply/eqP; rewrite eqn_leq; apply/andP; split.
  rewrite -[1]/(size [:: cliftr p2 (perfect p3 : _ _ n)]).
  apply: gdist_path_le => //=.
  by rewrite move_liftr_perfect.
case E : gdist => //.
move/eqP: E; rewrite gdist_eq0 => /eqP E.
have := cliftr_ldisk p1 (perfect p3 : _ _ n).
rewrite E cliftr_ldisk => p2Ep1.
by have := hirr p1; rewrite -{2}p2Ep1 p1Rp2.
Qed.

(*****************************************************************************)
(*  Difference relation                                                      *)
(*****************************************************************************)

Section Drel.

Variable n : nat.

Definition drel : rel (peg n) := [rel x  y | x != y].

Definition dirr : irreflexive drel.
by move=> x; apply/eqP.
Qed.

Definition dsym : symmetric drel.
by move=> x y; rewrite /drel /= eq_sym.
Qed.

End Drel.

(*****************************************************************************)
(*  Linear relation                                                          *)
(*****************************************************************************)

Section Lrel.

Variable n : nat.

Definition lrel : rel (peg n) := 
  [rel x y | ((nat_of_ord x).+1 == y) || (y.+1 == x)].

Definition lirr : irreflexive lrel.
Proof. by move=> k; rewrite /lrel /= (gtn_eqF (leqnn _)). Qed.

Definition lsym : symmetric lrel.
Proof. by move=> x y; rewrite /lrel /= orbC.
Qed.

End Lrel.

Lemma connect_move p n (c1 c2 : configuration p.+3 n) : 
   connect (move (@drel p.+3)) c1 c2.
Proof.
elim: n c1 c2 => [c1 c2 | n IH c1 c2].
  rewrite (_ : c1 = c2) ?connect0 //.
  by apply/ffunP=> [] [].
rewrite -[c1]cunliftrK -[c2]cunliftrK.
set p1 := c1 ldisk; set p2 := c2 ldisk.
have [<-|/eqP p1Dp2] := p1 =P p2.
  by apply: connect_liftr => // i; rewrite dirr.
pose p3 := opeg p1 p2.
apply: connect_trans (_ : connect _ (cliftr p1 (perfect p3)) _).
  apply: connect_liftr; first by apply: dirr.
  by apply: IH.
apply: connect_trans (_ : connect _ (cliftr p2 (perfect p3)) _); last first.
  apply: connect_liftr; first by apply: dirr.
  by apply: IH.
apply: connect1.
apply: move_liftr_perfect => //.
  rewrite eq_sym; apply: opegDl.
rewrite eq_sym; apply: opegDr.
Qed.

Lemma gdist_leq_move p n (c1 c2 : configuration p.+3 n) : 
   `d[c1, c2]_(move (@drel _)) <= (2 ^ n).-1.
Proof.
elim: n c1 c2 => [c1 c2 | n IH c1 c2].
  rewrite (_ : c1 = c2) ?gdist0 //.
  by apply/ffunP=> [] [] [].
rewrite -[c1]cunliftrK -[c2]cunliftrK.
set p1 := c1 ldisk; set p2 := c2 ldisk.
have [<-|/eqP p1Dp2] := p1 =P p2.
  apply: leq_trans.
    apply: gdist_liftr => [i|]; first by rewrite dirr.
    apply: connect_move.
  apply: leq_trans; first by apply: IH.
  rewrite -ltnS !prednK ?expn_gt0 //.
  by rewrite leq_exp2l.
pose p3 := opeg p1 p2.
apply: leq_trans.
  apply: (@gdist_triangular _ _ _ _ (cliftr p1 (perfect p3))).
rewrite expnS mul2n -addnn.
have tnP : 0 < 2 ^ n by rewrite expn_gt0.
rewrite -(prednK tnP) addSn /=.
apply: leq_add.
  apply: leq_trans.
    apply: gdist_liftr => [i|]; first by rewrite dirr.
    by apply: connect_move.
  by apply: IH.
apply: leq_trans.
  apply: (@gdist_triangular _ _ _ _ (cliftr p2 (perfect p3))).
rewrite gdist_liftr_perfect ?ltnS //; last 3 first.
- by apply: dirr.
- by rewrite eq_sym opegDl.
- by rewrite eq_sym opegDr.
apply: leq_trans.
  apply: gdist_liftr => [i|]; first by rewrite dirr.
  by apply: connect_move.
by apply: IH.
Qed.

Definition sorted (s : seq nat) := 
  forall i j, i < size s -> j < size s -> (nth 0 s i < nth 0 s j) = (i < j).

Lemma sorted_cons a s : sorted (a :: s) -> sorted s.
Proof. by move=> H i j iH jH; rewrite -[in RHS]ltnS -[in RHS]H.
Qed.

Lemma sorted_iota i j : sorted (iota i j).
Proof.
move=> i1 j1; rewrite size_iota => i1Lj j1Lj.
by rewrite !nth_iota // ltn_add2l.
Qed.

Lemma sorted_skip a b s : sorted (a :: b :: s) -> sorted (a :: s).
Proof.
move=> Hs [|i] [|j] iH jH //=; first by rewrite ltnn.
- by rewrite (Hs 0 j.+2).
- by rewrite (Hs i.+2 0).
by rewrite (Hs i.+2 j.+2).
Qed.

Lemma sorted_filter (s : seq nat) (p : pred nat) :
  sorted s -> sorted (filter p s).
Proof.
have F a s1 i :
   sorted (a :: s1) -> i < size (filter p s1) -> a < nth 0 (filter p s1) i.
  elim: s1 i => //= b s1 IH i abS.
  have [pbT|pbF] := boolP (p b).
    case: i => [|i1] /= sH; first by rewrite (abS 0 1).
    apply: IH => //.
    by apply: sorted_skip abS.
  apply: IH.
  by apply: sorted_skip abS.
elim: s => //= a s IH aS.
have sS := sorted_cons aS.
have [paT|paF] := boolP (p a); last by apply: IH.
move=> [|i] [|j] iH jH /=.
- by rewrite ltnn.
- by rewrite F.
- by rewrite ltnNge ltnW // F.
by rewrite ltnS (IH sS).
Qed.

Lemma enum_ord_inord m : (enum 'I_m.+1) = [seq inord i | i <- iota 0 m.+1].
Proof.
rewrite -val_ord_enum -map_comp /=.
rewrite enumT unlock /=.
elim: (ord_enum _) => //= a l <-.
by rewrite inord_val.
Qed.

(* To be reworked ! *)
Lemma sorted_enum_val (m : nat) (s : {set 'I_m}) (i j : 'I_#|s|) :
   (enum_val i) < (enum_val j) = (i < j).
Proof.
case: m s i j => [s|m s i j].
  rewrite (_ : s = set0).
    case=> m H j; apply: False_ind.
    by rewrite cards0 in H.
  by apply/setP=> [] []. 
have := ltn_ord i; have := ltn_ord j; rewrite {2 4}cardE.
rewrite /enum_val /= /(enum _) -enumT enum_ord_inord => iL jL.
have <-// := @nth_map ('I_m.+1) (enum_default i) nat 0 (@nat_of_ord m.+1).
have <-// := @nth_map ('I_m.+1) (enum_default j) nat 0 (@nat_of_ord m.+1).
have F k1 k2 :  k1 + k2 <= m.+1 ->
  [seq (nat_of_ord i) | i <- [seq inord i0 | i0 <- iota k1 k2] & mem s i] =
  (filter (fun i0 => mem s (inord i0))  (iota k1 k2)).
  elim: k2 k1 => //= k2 IH k1 k1k2Lm.
  case: (_ \in _) => //=.
  rewrite inordK //.
  rewrite IH //.
  by rewrite addSnnS.
  by apply: leq_trans k1k2Lm; rewrite -addSnnS leq_addr.
  apply: IH.
  by rewrite addSnnS.
rewrite F //.
have : j < size ([seq i0 <- iota 0 m.+1 | mem s (inord i0)]).
  by move: iL; rewrite -F // size_map.
have : i < size ([seq i0 <- iota 0 m.+1 | mem s (inord i0)])
  by move: jL; rewrite -F // size_map.
apply: sorted_filter => //.
by apply: sorted_iota.
Qed.

Section ISetd.

(* Number of disks *)
Variable n : nat.
(* Subset of disks *)
Variable sd : {set disk n}.
(* Number of pegs *)
Variable k : nat.

(* relations on peg *)
Variable rel : rel (peg k). 

Definition cprojd (c : configuration k n) : configuration k #|sd| := 
  [ffun i => c (enum_val i)].

Lemma on_top_cprojd c d (dIsd : d \in sd) : 
  on_top d c -> on_top (enum_rank_in dIsd d) (cprojd c).
Proof.
move=> /= /on_topP dO.
apply/on_topP => /= d1 H.
rewrite leq_eqVlt; case: eqP => //= /eqP dDd1.
rewrite -[d1](enum_valK_in dIsd) -sorted_enum_val !enum_rankK_in //; last first.
  by apply: enum_valP.
rewrite ltn_neqAle.
case: eqP => [/eqP /val_eqP dEd1 | /eqP dDd1' /=].
  by case/eqP: dDd1; rewrite {2}dEd1 enum_valK_in.
rewrite !ffunE enum_rankK_in // in H.
by apply: dO.
Qed.

Lemma move_cprojd (c1 c2 : configuration k n) : 
  move rel c1 c2 -> (cprojd c1) != (cprojd c2) ->
  move rel (cprojd c1) (cprojd c2).
Proof.
move => /moveP [d [dH1 dH2 dH3 dH4]] c1Dc2.
have [dIsd|dNIsd] := boolP (d \in sd); last first.
  case/eqP: c1Dc2.
  apply/ffunP => i; rewrite !ffunE.
  apply: dH2.
  apply: contra dNIsd => /eqP->.
  by apply: enum_valP.
apply/moveP; exists (enum_rank_in dIsd d); split => /=.
- by rewrite !ffunE !enum_rankK_in //.
- move=> /= d2 dDd2.
  rewrite !ffunE.
  apply: dH2.
  rewrite -[d](enum_rankK_in dIsd) //.
  by apply /eqP => /enum_val_inj /eqP; rewrite (negPf dDd2).
- by apply: on_top_cprojd.
by apply: on_top_cprojd.
Qed.

Lemma path_cprojd (c : configuration _ _) cs :
    path (move rel) c cs ->
    path (move rel) (cprojd c) (rm_dup (cprojd c) [seq (cprojd i) | i <- cs]).
Proof.
elim: cs c => //= c1 cs IH c => /andP[cMc1 c1Pcs].
case: eqP => [->|/eqP cDc1 /=]; first by apply: IH; rewrite ?c2V.
by rewrite move_cprojd => //=; first by apply: IH; rewrite ?c2V.
Qed.

Lemma gdist_cprojd c1 c2 cs : 
    last c1 cs = c2 -> path (move rel) c1 cs ->
   `d[cprojd c1, cprojd c2]_(move rel) <= size cs.
Proof.
move=> cL cPcs.
have := size_rm_dup (cprojd c1) [seq (cprojd i) | i <- cs].
rewrite size_map; move/(leq_trans _); apply.
apply: gdist_path_le; first by apply: path_cprojd.
by rewrite last_rm_dup last_map cL.
Qed.

Lemma gpath_cprojd c1 c2 cs : 
    gpath (move rel) c1 c2 cs ->
   `d[cprojd c1, cprojd c2]_(move rel) <= `d[c1, c2]_(move rel).
Proof.
move=> gH.
rewrite (gpath_dist gH); apply: gdist_cprojd => //; first apply: gpath_last gH.
by apply: gpath_path gH.
Qed.

End ISetd.

Section CSet.

(* Number of disks *)
Variable n : nat.
(* cut limit *)
Variable t : nat.
Variable tLn : t <= n.
(* Number of pegs *)
Variable k : nat.

(* relations on peg *)
Variable rel : rel (peg k).

Definition ccut (c : configuration k n) : configuration k t := 
  [ffun i => c (widen_ord tLn i)].

Lemma ordinalK (d : disk n) (dLt : d < t) : widen_ord tLn (Ordinal dLt) = d.
Proof. by apply: val_inj. Qed.

Lemma on_top_ccut c (d : disk n) (dLr : d < t) : 
  on_top d c -> on_top (Ordinal dLr) (ccut c).
Proof.
move=> /= /on_topP dO.
apply/on_topP => /= d1 H.
rewrite leq_eqVlt; case: eqP => //= /eqP dDd1.
rewrite ltn_neqAle dDd1 /=.
apply: (dO (widen_ord tLn d1)) => //.
by move: H; rewrite !ffunE ordinalK.
Qed.

Lemma move_ccut (c1 c2 : configuration k n) : 
  move rel c1 c2 -> (ccut c1) != (ccut c2) ->
  move rel (ccut c1) (ccut c2).
Proof.
move => /moveP [d [dH1 dH2 dH3 dH4]] c1Dc2.
have [dLt|tLd] := leqP t d.
  case/eqP: c1Dc2.
  apply/ffunP => i; rewrite !ffunE.
  apply: dH2.
  by rewrite -val_eqE /= neq_ltn (leq_trans _ dLt) // orbT.
apply/moveP; exists (Ordinal tLd); split => /=.
- by rewrite !ffunE // ordinalK.
- move=> /= d2; rewrite !ffunE -val_eqE /= => dDd2.
  by apply: dH2; rewrite -val_eqE /=.
- by apply: on_top_ccut.
by apply: on_top_ccut.
Qed.

Lemma path_ccut (c : configuration _ _) cs :
    path (move rel) c cs ->
    path (move rel) (ccut c) (rm_dup (ccut c) [seq (ccut i) | i <- cs]).
Proof.
elim: cs c => //= c1 cs IH c => /andP[cMc1 c1Pcs].
case: eqP => [->|/eqP cDc1 /=]; first by apply: IH; rewrite ?c2V.
by rewrite move_ccut => //=; first by apply: IH; rewrite ?c2V.
Qed.

Lemma gdist_ccut c1 c2 cs : 
    last c1 cs = c2 -> path (move rel) c1 cs ->
   `d[ccut c1, ccut c2]_(move rel) <= size cs.
Proof.
move=> cL cPcs.
have := size_rm_dup (ccut c1) [seq (ccut i) | i <- cs].
rewrite size_map; move/(leq_trans _); apply.
apply: gdist_path_le; first by apply: path_ccut.
by rewrite last_rm_dup last_map cL.
Qed.

Lemma gpath_ccut c1 c2 cs : 
    gpath (move rel) c1 c2 cs ->
   `d[ccut c1, ccut c2]_(move rel) <= `d[c1, c2]_(move rel).
Proof.
move=> gH.
rewrite (gpath_dist gH); apply: gdist_ccut => //; first apply: gpath_last gH.
by apply: gpath_path gH.
Qed.

End CSet.


Section ISet.


(* Number of disks *)
Variable n : nat.
(* Subset of disks *)
Variable sd : {set disk n}.
(* Number of pegs *)
Variable k : nat.
(* Subset of pegs *)
Variable sp : {set peg k}.
(* The subset is non empty *)
Variable p0 : peg k.
Variable p0Isp : p0 \in sp.

(* relations on peg *)
Variable rel1 : rel (peg k). 
Variable rel2 : rel (peg #|sp|). 
Hypothesis rel_compat : 
  forall p1 p2, p1 \in sp -> p2 \in sp ->
    rel1 p1 p2 -> rel2 (enum_rank_in p0Isp p1) (enum_rank_in p0Isp p2).

(* Valid conf : disk in sd are on pegs in sp *)
Definition cvalid (c : configuration k n) :=
  [forall i, (i \in sd) ==> (c i \in sp)].

Lemma cvalidP (c : configuration k n) :
  reflect (forall i, i \in sd -> c i \in sp)
          (cvalid c).
Proof.
apply: (iffP forallP) => [H d|H d]; first by have /implyP := H d.
by apply/implyP/H.
Qed.


Definition cproj (c : configuration k n) : configuration #|sp| #|sd| := 
  [ffun i => enum_rank_in p0Isp (c (enum_val i))].

Lemma on_top_cproj c d (dIsd : d \in sd) : 
  cvalid c -> on_top d c -> on_top (enum_rank_in dIsd d) (cproj c).
Proof.
move=> /= /cvalidP cV /on_topP dO.
apply/on_topP => /= d1 H.
rewrite leq_eqVlt; case: eqP => //= /eqP dDd1.
rewrite -[d1](enum_valK_in dIsd) -sorted_enum_val !enum_rankK_in //; last first.
  by apply: enum_valP.
rewrite ltn_neqAle.
case: eqP => [/eqP /val_eqP dEd1 | /eqP dDd1' /=].
  by case/eqP: dDd1; rewrite {2}dEd1 enum_valK_in.
rewrite !ffunE enum_rankK_in // in H.
apply: dO.
apply: (@enum_rank_in_inj _ _ _ _ p0Isp p0Isp) => //.
  by apply: cV.
by apply/cV/enum_valP.
Qed.

Lemma move_cproj(c1 c2 : configuration k n) : 
  all cvalid [::c1; c2] ->
  move rel1 c1 c2 -> (cproj c1) != (cproj c2) ->
  move rel2 (cproj c1) (cproj c2).
Proof.
rewrite /=.
move=> /= /and3P[c1V c2V _]  /moveP [d [dH1 dH2 dH3 dH4]] c1Dc2.
have [dIsd|dNIsd] := boolP (d \in sd); last first.
  case/eqP: c1Dc2.
  apply/ffunP => i; rewrite !ffunE.
  apply: enum_val_inj.
  rewrite !enum_rankK_in ?(cvalidP _ c1V) ?(cvalidP _ c2V) ?enum_valP //.
  apply: dH2.
  apply: contra dNIsd => /eqP->.
  by apply: enum_valP.
apply/moveP; exists (enum_rank_in dIsd d); split => /=.
- rewrite !ffunE !enum_rankK_in //.
  by apply: rel_compat=> //; [apply: (cvalidP _ c1V) | 
                              apply: (cvalidP _ c2V)].
- move=> /= d2 dDd2.
  rewrite !ffunE.
  congr (enum_rank_in _ _).
  apply: dH2.
  rewrite -[d](enum_rankK_in dIsd) //.
  by apply /eqP => /enum_val_inj /eqP; rewrite (negPf dDd2).
- by apply: on_top_cproj.
by apply: on_top_cproj.
Qed.

Lemma path_cproj (c : configuration _ _) cs :
    all cvalid (c :: cs) ->
    path (move rel1) c cs ->
    path (move rel2) (cproj c) (rm_dup (cproj c) [seq (cproj i) | i <- cs]).
Proof.
elim: cs c => //= c1 cs IH c => /and3P[c1V c2V c3V] /andP[cMc1 c1Pcs].
case: eqP => [->|/eqP cDc1 /=]; first by apply: IH; rewrite ?c2V.
rewrite move_cproj => //=; first by apply: IH; rewrite ?c2V.
by rewrite c1V c2V.
Qed.

Lemma gdist_cproj c1 c2 cs : 
    all cvalid (c1 :: cs) -> last c1 cs = c2 -> path (move rel1) c1 cs ->
   `d[cproj c1, cproj c2]_(move rel2) <= size cs.
Proof.
move=> cV cL cPcs.
have := size_rm_dup (cproj c1) [seq (cproj i) | i <- cs].
rewrite size_map; move/(leq_trans _); apply.
apply: gdist_path_le; first by apply: path_cproj.
by rewrite last_rm_dup last_map cL.
Qed.

Lemma gpath_cproj c1 c2 cs : 
    all cvalid (c1 :: cs) -> gpath (move rel1) c1 c2 cs ->
   `d[cproj c1, cproj c2]_(move rel2) <= `d[c1, c2]_(move rel1).
Proof.
move=> cV gH.
rewrite (gpath_dist gH); apply: gdist_cproj => //; first apply: gpath_last gH.
by apply: gpath_path gH.
Qed.

End ISet.


Section ISet2.

(* Number of disks *)
Variable n : nat.
(* Subset of disks *)
Variable sd : {set disk n}.
(* Number of pegs *)
Variable k : nat.
(* Subsets of pegs *)
Variables sp1 sp2 : {set peg k}.
(* The subsets are non empty *)
Variable p1 p2 : peg k.
Variable p1Isp1 : p1 \in sp1.
Variable p2Isp2 : p2 \in sp2.

(* relations on peg *)
Variable rel1 : rel (peg k). 
Variable rel2 : rel (peg #|sp1|). 
Variable rel3 : rel (peg #|sp2|). 
Hypothesis irH : irreflexive rel1.
Hypothesis rel2_compat : 
  forall pi pj, pi \in sp1 -> pj \in sp1 ->
    rel1 pi pj -> rel2 (enum_rank_in p1Isp1 pi) (enum_rank_in p1Isp1 pj).
Hypothesis rel3_compat : 
  forall pi pj, pi \in sp2 -> pj \in sp2 ->
    rel1 pi pj -> rel3 (enum_rank_in p2Isp2 pi) (enum_rank_in p2Isp2 pj).

Lemma size_cproj (c : configuration _ _) cs :
    all (cvalid sd sp1) (c :: cs) ->
    all (cvalid (~: sd) sp2) (c :: cs) ->
    path (move rel1) c cs ->
    size cs = 
      size (rm_dup (cproj sd p1Isp1 c) [seq (cproj sd  p1Isp1 i) | i <- cs]) +
      size (rm_dup (cproj (~: sd) p2Isp2 c)
             [seq (cproj (~: sd) p2Isp2 i) | i <- cs]).
    
Proof.
elim: cs c => //= c1 cs IH c => /and3P[c1V1 c2V1 c3V1] 
                                /and3P[c1V2 c2V2 c3V2] 
                                /andP[/moveP[d [dH1 dH2 dH3 dH4]] c1Pcs].
have cdDc1d : c d != c1 d.
  by have /idP/negP := irH (c d); apply: contra => /eqP {2}->.
have [dIsd|dNIsd] := boolP (d \in sd).
  rewrite ifN /= ?addSn; last first.
    apply/eqP => /ffunP /(_ (enum_rank_in dIsd d)).
    rewrite !ffunE enum_rankK_in // => /enum_rank_in_inj => H.
    case/eqP : cdDc1d; apply: H; first by have /cvalidP := c1V1; apply.
    by have /cvalidP := c2V1; apply.
  rewrite ifT; last first.
    apply/eqP/ffunP=> i; rewrite !ffunE dH2 //.
    have := enum_valP i; rewrite inE.
    by apply: contra => /eqP<-.
  by congr (_.+1); apply: IH; rewrite ?c2V1 ?c2V2.
rewrite ifT; last first.
  apply/eqP/ffunP=> i; rewrite !ffunE dH2 //.
  apply: contra dNIsd => /eqP->.
  by have := enum_valP i.
have dd : d \in ~: sd by rewrite inE.
rewrite ifN /= ?addSn; last first.
  apply/eqP => /ffunP /(_ (enum_rank_in dd d)).
  rewrite !ffunE enum_rankK_in // => /enum_rank_in_inj => H.
  case/eqP : cdDc1d; apply: H.
    by have /cvalidP := c1V2; apply.
  by have /cvalidP := c2V2; apply.
by rewrite addnS; congr (_.+1); apply: IH; rewrite ?c2V1 ?c2V2.
Qed.

Lemma gdist_cproj2 c1 c2 cs : 
    all (cvalid sd sp1) (c1 :: cs) -> all (cvalid (~: sd) sp2) (c1 :: cs) ->
    last c1 cs = c2 -> path (move rel1) c1 cs ->
   `d[cproj sd p1Isp1 c1, cproj sd p1Isp1 c2]_(move rel2) +
   `d[cproj (~: sd) p2Isp2 c1, cproj (~: sd) p2Isp2  c2]_(move rel3)
      <= size cs.
Proof.
move=> cV1 cV2 cL cPcs.
rewrite (size_cproj cV1 cV2) //.
apply: leq_add.
  apply: gdist_path_le; first by apply: path_cproj rel2_compat _ _ _ _.
  by rewrite last_rm_dup last_map cL.
apply: gdist_path_le; first by apply: path_cproj rel3_compat _ _ _ _.
by rewrite last_rm_dup last_map cL.
Qed.

Lemma gpath_cproj2 c1 c2 cs : 
    all (cvalid sd sp1) (c1 :: cs) -> all (cvalid (~: sd) sp2) (c1 :: cs) ->
    gpath (move rel1) c1 c2 cs ->
   `d[cproj sd p1Isp1 c1, cproj sd p1Isp1 c2]_(move rel2) +
   `d[cproj (~: sd) p2Isp2 c1, cproj (~: sd) p2Isp2  c2]_(move rel3)
      <= `d[c1,c2]_(move rel1).
Proof.
move=> cV1 cV2 gH.
rewrite (gpath_dist gH).
apply: gdist_cproj2 => //; first apply: gpath_last gH.
by apply: gpath_path gH. 
Qed.

End ISet2.

