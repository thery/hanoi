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
Require Import gdist.

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


Definition dlarger : rel disk := [rel d1 d2 | (d1 : disk) <= (d2 : disk)].

(******************************************************************************)
(* Given a configuration c, the disks on the peg p can be reconstructed by    *)
(* the list in decreasing order of the disk d such that c d = p               *)
(******************************************************************************)

Definition configuration := {ffun disk -> peg}.

(* A perfect configuration is one where all the pegs are on a single peg p *)
Definition perfect p : configuration :=  [ffun d => p].

End Disk.

Notation " d1 \larger d2 " := (dlarger d1 d2) (at level 60).

(* The smallest disk *)
Definition sdisk {n} : disk n.+1 := ord_max.

(* The largest disk *)
Definition ldisk {n} : disk n.+1 := ord0.

Lemma split_ldisk n : @split 1 _ (ldisk : 'I_(n.+1)) = inl ord0.
Proof.
by case: splitP => // [] [[]] // i _; congr inl; apply/val_eqP.
Qed.

(******************************************************************************)
(* The disk d is on top of peg (c d)                                          *)
(******************************************************************************)

Definition on_top n (d : disk n) (c : configuration n) :=
   [forall d1 : disk n, (c d == c d1) ==> (dlarger d1 d)].

Lemma on_topP n (d : disk n) (c : configuration n) :
  reflect (forall d1, c d = c d1 -> d1 \larger d) (on_top d c).
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
  [ffun i => match split i with inl j => c1 j | inr j => c2 j end].

(* right shifting a configuration : taking the disks larger than m *)
Definition crshift m n (c : configuration (m + n)) : configuration n := 
   [ffun i => c (rshift m i)].

(* left shifting a configuration : taking the disks smaller than m *)
Definition clshift m n (c : configuration (m + n)) : configuration m := 
   [ffun i => c (lshift n i)].

(* Sanity check *)
Lemma cmergeK m n (c : configuration (m + n)) :
  cmerge (clshift c) (crshift c) = c.
Proof.
apply/ffunP=> i; rewrite !ffunE.
by case: splitP => [] j iE; rewrite !ffunE /=;
   congr fun_of_fin; apply/val_eqP/eqP.
Qed.

Lemma split_lshift k m (x : 'I_k) : split (lshift m x) = inl x.
Proof.
case: splitP => [j /= /eqP/val_eqP-> //|k1 /= xE].
by have := ltn_ord x; rewrite xE ltnNge leq_addr.
Qed.

Lemma split_rshift k m (x : 'I_k) : split (rshift m x) = inr x.
Proof.
case: splitP => [j /= jE|k1 /= /eqP].
  by have := ltn_ord j; rewrite -jE ltnNge leq_addr.
by rewrite eqn_add2l => /val_eqP->.
Qed.

Lemma on_top_merger m n x (c1 : configuration m) (c2 : configuration n) : 
  on_top (rshift m x) (cmerge c1 c2) = on_top x c2.
Proof.
apply/on_topP/on_topP.
  move=> Hx d2 cxEcd2.
  have := Hx (rshift m d2).
  rewrite !ffunE !split_rshift => /(_ cxEcd2).
  by rewrite [_ \larger _]leq_add2l.
move=> H d; rewrite !ffunE split_rshift /dlarger /=.
case: splitP => [j -> _ | k -> H1].
  by apply: leq_trans (ltnW _) (leq_addr _ _).
by rewrite leq_add2l; apply: H.
Qed.

Lemma move_merger m n (c : configuration m) (c1 c2 : configuration n) :
    move (cmerge c c1) (cmerge c c2) = move c1 c2.
Proof.
apply/moveP/moveP => [] [d1 [H1d1 H2d1 H3d1 H4d1]]; last first.
  exists (rshift m d1); split => //; try by rewrite on_top_merger.
    by rewrite !ffunE /= split_rshift.
  move=> d2; rewrite !ffunE; case: splitP => // k d2E H.
  apply: H2d1 => //; apply: contra H => /eqP->.
  by apply/eqP/val_eqP/eqP.
move: H1d1; rewrite !ffunE.
case: splitP => [j _|k kE H1x]; first by rewrite irH.
have d1E : (rshift m k) = d1 by apply/val_eqP/eqP.
rewrite -d1E in H3d1 H4d1.
exists k; split => //; try by rewrite -(on_top_merger _ c).
move=> d2 kDd2.
have := H2d1 (rshift m d2).
rewrite !ffunE split_rshift => H.
apply: H.
apply: contra kDd2 => /eqP/val_eqP /=.
by rewrite kE eqn_add2l.
Qed.

Lemma path_merger m n (c1 : configuration m)
         (c2 : configuration n) (cs : seq (configuration _)) :
    path move (cmerge c1 c2) (map (cmerge c1) cs) = 
    path move c2 cs.
Proof. by elim: cs c2 => //= c3 cs IH c2; rewrite move_merger IH. Qed.

Lemma connect_merger m n (c : configuration m) (c1 c2 : configuration n) : 
  connect move c1 c2 -> connect move (cmerge c c1) (cmerge c c2).
Proof.
move=> /connectP[x]; rewrite -(path_merger c) => Hp Hl.
apply/connectP; eexists; first exact: Hp.
by rewrite Hl [RHS]last_map.
Qed.

Lemma gdist_merger m n (c: configuration m) (c1 c2 : configuration n) : 
  connect move c1 c2 ->
  `d[cmerge c c1, cmerge c c2]_move <= `d[c1, c2]_move.
Proof.
move=> /gdist_path[p1 [H1p1 H2p1 H3p1 <-]].
rewrite -(size_map (cmerge c)).
apply: gdist_path_le; first by rewrite path_merger.
by rewrite [LHS]last_map H2p1.
Qed.

Lemma on_top_mergel m n (c1 : configuration m) (c2 : configuration n) d :
  cdisjoint c1 c2 -> on_top d c1 -> on_top (lshift n d) (cmerge c1 c2).
Proof.
move=> c1Dc2 /on_topP dTc; apply/on_topP => d1.
rewrite !ffunE split_lshift /dlarger /=.
case: splitP => j -> c1dc1j; first by apply: dTc.
by have /cdisjointP/(_ d j)/eqP[] := c1Dc2.
Qed.

Lemma on_top_mergel_inv m n (c1 : configuration m) (c2 : configuration n) d :
  on_top (lshift n d) (cmerge c1 c2) -> on_top d c1.
Proof.
move=> /on_topP dTc; apply/on_topP => d1 Hc.
have := dTc (lshift n d1).
by rewrite !ffunE !split_lshift /=; apply.
Qed.

Lemma move_mergel m n (c1 c2 : configuration m) (c : configuration n) :
  move (cmerge c1 c) (cmerge c2 c) -> move c1 c2.
Proof.
move=> /moveP [x [H1x H2x H3x H4x]]; apply/moveP.
move: H1x; rewrite !ffunE.
case: splitP => [j jE J1x | k]; last by rewrite irH.
have xE : (lshift n j) = x by apply/val_eqP/eqP.
rewrite -xE in H3x H4x.
exists j; split => //; try by apply: on_top_mergel_inv; eassumption.
move=> d2 kDd2.
have := H2x (lshift n d2).
rewrite !ffunE split_lshift => H.
apply: H.
apply: contra kDd2 => /eqP/val_eqP /=.
by rewrite jE.
Qed.

Lemma move_mergel_inv m n (c1 c2 : configuration m) 
                          (c : configuration n) :
  cdisjoint c1 c -> cdisjoint c2 c ->
  move c1 c2 -> move (cmerge c1 c) (cmerge c2 c).
Proof.
move=> c1Dc c2Dc /moveP[x [H1x H2x H3x H4x]]; apply/moveP.
exists (lshift n x); split => //; try by apply/on_top_mergel.
  by rewrite !ffunE /= split_lshift.
move=> d2; rewrite !ffunE; case: splitP => // k d2E H.
apply: H2x => //; apply: contra H => /eqP->.
by apply/eqP/val_eqP/eqP.
Qed.

Lemma path_mergel m n (c1 : configuration m)
         (c2 : configuration n) (cs : seq (configuration _)) :
    path move (cmerge c1 c2) (map (fun c => cmerge c c2) cs) -> 
    path move c1 cs.
Proof. by elim: cs c1 => //= c3 cs IH c1 /andP[/move_mergel-> /IH]. Qed.

Lemma path_mergel_inv m n (c1 : configuration m)
         (c2 : configuration n) (cs : seq (configuration _)) :
    all (fun c1 => cdisjoint c1 c2) (c1 :: cs) ->
    path move c1 cs ->
    path move (cmerge c1 c2) (map (fun c => cmerge c c2) cs).
Proof.
elim: cs c1 => //= c3 cs IH c1 /and3P[c1Dc2 c3Dc2 Dcs] 
                               /andP[/move_mergel_inv ->// /IH->//].
by rewrite c3Dc2.
Qed.

Definition cliftrn m n p (c : configuration n) : configuration (m + n) :=
  cmerge (perfect m p) c.
Definition cliftr n : _ -> _ -> configuration n.+1 := @cliftrn 1 n.


Definition cliftln m n p (c : configuration m) : configuration (m + n) :=
  cmerge c (perfect n p).

Notation " ↑[ c ]_ p" := (cliftr p c) (at level 5, format "↑[ c ]_ p").

Definition cliftl n : _ -> _ -> configuration (n + 1) := @cliftln n 1.

Lemma cliftr_ldisk n p (c : configuration n) : ↑[c]_p ldisk  = p.
Proof. by rewrite ffunE; case: splitP => [j|//]; rewrite ffunE. Qed.

Lemma on_top_liftrn n m p x (c : configuration n) : 
  on_top (rshift m x) (cliftrn m p c) = on_top x c.
Proof. by exact: on_top_merger. Qed.

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
by case: splitP => [j|k]; rewrite !ffunE.
Qed.

Definition cunliftr {n} (c : configuration n.+1) : configuration n :=
  @crshift 1 n c.

Notation " ↓[ c ]" := (cunliftr c) (at level 5, format "↓[ c ]").

Lemma cliftrK n p : cancel (cliftr p) (cunliftr : _ -> configuration n).
Proof. by move=> c; apply/ffunP => i; rewrite !ffunE split_rshift. Qed.

Lemma cunliftrK n (c : configuration n.+1) : ↑[↓[c]]_(c ldisk) = c.
Proof.
apply/ffunP => i; rewrite !ffunE.
case: splitP => [] j iE; rewrite !ffunE; congr fun_of_fin;
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
apply/ffunP=> i; rewrite !ffunE.
apply: move_disk1 c1Mc2 c10Dc20 _.
by apply/eqP/val_eqP.
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

Lemma path_unlift n (c : configuration n.+1) (cs : seq (configuration _)) :
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

Lemma perfect_liftrn m n p : cliftrn m p (perfect n p) = perfect (m + n) p.
Proof.
by apply/ffunP => i; rewrite !ffunE; case: splitP => j; rewrite !ffunE.
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
  by rewrite path_unlift // => c1 /Hn; rewrite negbK => /eqP.
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
  by apply/eqP/val_eqP/neq_bump.
have Hm1 : move ↑[last c1 cs1]_p1 ↑[last c1 cs1]_p2.
  have ->: ↑[last ↓[c] cs1]_p1 = last c lcs1.
    by rewrite -[in LHS]last_map -lcs1E cunliftrK.
  by rewrite -lc1E.
apply: pathS_spec_move (p1Dp2) _ _ _ (Hm1) _ => //.
-  have := @move_diskr _ ldisk _ _ Hm1.
   by rewrite !cliftr_ldisk; apply.
- by rewrite csE lc1E lcs1E.
- rewrite path_unlift => //.
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
have -> : cunliftr c = cunliftr c1.
  apply/ffunP=> d1; rewrite !ffunE.
  by apply: move_disk1 c1dDcd _.
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
Proof. by apply/on_topP=> [] [] []. Qed.

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
move=> /gdist_path [p1 [c1Pp1 lc1p2Ec2 Uc1p1 <-]].
rewrite -(size_map plift).
apply: gdist_path_le; first by rewrite plift_path.
by rewrite last_map lc1p2Ec2.
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
move=> /gdist_path[p1 [H1p1 H2p1 H3p1 <-]].
rewrite -(size_map (cliftln n p \o plift p)).
apply: gdist_path_le; first by rewrite path_liftln.
by rewrite [LHS]last_map H2p1.
Qed.

Lemma crliftn_perfect n m p1 :
  cliftln n p (perfect p1) = cliftrn m p1 (perfect p).
Proof. by []. Qed.

End Crlift.

(******************************************************************************)
(*  Other peg                                                                 *)
(******************************************************************************)

Definition opeg n (p1 p2 : peg n.+1) :=
  odflt ldisk [pick i | (i != p1) && (i != p2)].

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
