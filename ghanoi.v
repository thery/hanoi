(*****************************************************************************)
(*                                                                           *)
(*                     Generalised Hanoi Problem                             *)
(*                                                                           *)
(*****************************************************************************)
(*                                                                           *)
(*      We consider a generalisation of Hanoi problem :                      *)
(*        a parameter n : the number of pegs                                 *)
(*        a parameter r : r p1 p2 tells that a disk can go from p1 -> p2     *)
(*                                                                           *)
(*****************************************************************************)

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

(*****************************************************************************)
(* Given a configuration c, the disks on the peg p can be reconstructed by   *)
(* the list in decreasing order of the disk d such that c d = p              *)
(*****************************************************************************)

Definition configuration := {ffun disk -> peg}.

(* A perfect configuration is one where all the pegs are on peg p *)
Definition perfect p : configuration :=  [ffun d => p].

End Disk.

(* The largest disk *)
Definition ldisk {n} : disk n.+1 := ord_max.

(*****************************************************************************)
(* A move is a relation between two configurations c1 c2:                    *)
(* there must exists a disk d1, that is the only one that has changed of     *)
(* peg (c1 d1 != c2 d1) and that was the minimum of the peg (c1 d1) and      *)
(* is the minimum of the peg (c2 d1).                                        *)
(* The parameter m is here to restrict the range on which one can select the *)
(* disk that has moved.                                                      *)
(* This is done to accomodate inductive which is the key of some proofs      *)
(*****************************************************************************)

Definition move {n} : rel (configuration n) :=
   [rel c1 c2 | [exists d1 : disk n, 
                  [&& r ((c1 : configuration n) d1) (c2 d1),
                      [forall d2, (d1 != d2) ==> (c1 d2 == c2 d2)],
                      [forall d2, (c1 d1 == c1 d2) ==> (d1 <= d2)] &
                      [forall d2, (c2 d1 == c2 d2) ==> (d1 <= d2)]]]].

(* The disk d is on top of peg (c d) *)
Definition on_top n (d : disk n) (c : configuration n) :=
   forall d1, c d = c d1 -> d <= d1.

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
  [[d /and4P[H1 /forallP H2 /forallP H3 /forallP H4]]|[d [H1 H2 H3 H4]]];
        exists d.
  split => // d1 H; first by apply/eqP/(implyP (H2 _)).
    by apply/(implyP (H3 _))/eqP.
  by apply/(implyP (H4 _))/eqP.
by rewrite H1 /=; apply/and3P; split; apply/forallP => d1; apply/implyP => H;
   rewrite ?H2 // ?(H3 _ (eqP H)) // (H4 _ (eqP H)).
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

Lemma move_sym n (c1 c2 : configuration n) : move c1 c2 = move c2 c1.
Proof.
by apply/moveP/moveP=> [] [d [H1 H2 H3 H4]];
   exists d; split; rewrite 1?symH 1?eq_sym // => e dDe; apply/sym_equal/H2.
Qed.

(* In a move, the disk that moves accomodates r *)
Lemma move_diskr n (d : disk n) (c1 c2 : configuration n) : 
  move c1 c2 -> c1 d != c2 d -> r (c1 d) (c2 d).
Proof.
case/moveP=> d1 [H1 H2 H3 H4] /eqP c1dDc2d.
by have [/eqP<-|/H2] := boolP (d1 == d).
Qed.

(* In a move only one disk moves *)
Lemma move_disk1 n (d1 d2 : disk n) (c1 c2 : configuration n) : 
  move c1 c2 -> c1 d1 != c2 d1 -> d1 != d2 -> c1 d2 = c2 d2.
Proof.
case/moveP=> d3 [H1 H2 H3 H4] c1d1Dc2d1 d1Dd2.
have [/eqP d3Ed1|d3Dd1] := boolP (d3 == d1); last first.
  by case/eqP: c1d1Dc2d1; apply: H2.
by apply: H2; rewrite d3Ed1.
Qed.

Definition clift n p (c : configuration n) :
   configuration n.+1 :=
  [ffun i => oapp c p (unlift ldisk i)].

Notation " ↑[ c ]_ p" := (clift p c) (at level 5, format "↑[ c ]_ p").

Lemma on_top_lift n p (d : disk n) (c : configuration n) :
  on_top d c -> on_top (lift ldisk d) (clift p c).
Proof.
move=> dTc d1.
rewrite !ffunE liftK /=.
case: unliftP => [k1 -> /=|/= -> _].
  by rewrite /bump ![n <= _]leqNgt !ltn_ord; apply: dTc.
by rewrite /bump /bump [n <= _]leqNgt ltn_ord ltnW // ltn_ord.
Qed.

Lemma move_lift n p (c1 c2 : configuration n) :
  move c1 c2 -> move (clift p c1) (clift p c2).
Proof.
move=> /moveP[d [H1 H2 H3 H4]].
apply/moveP; exists (lift ord_max d); split => [|d2||].
- by rewrite !ffunE liftK.
- rewrite !ffunE.
  case E : unlift => [k|] //= H.
  apply: H2; apply: contra_neq H => ->.
  by case: unliftP E => // j -> [->].
- by apply: on_top_lift.
by apply: on_top_lift.
Qed.

Lemma perfect_lift n p : clift p (perfect n p) = perfect n.+1 p.
Proof.
apply/ffunP => i; rewrite !ffunE.
by case: unlift => //= j; rewrite !ffunE.
Qed.

Definition cunlift {n} (c : configuration n.+1) :
   configuration n := [ffun i =>  c (lift ldisk i)].

Notation " ↓[ c ]" := (cunlift c) (at level 5, format "↓[ c ]").

Lemma cliftK n p : cancel (clift p) (cunlift : _ -> configuration n).
Proof. by move=> c; apply/ffunP => i; rewrite !ffunE liftK. Qed.

Lemma cunliftK n (c : configuration n.+1) : clift (c ldisk) (cunlift c) = c.
Proof.
apply/ffunP => i; rewrite !ffunE.
by case: unliftP => /= [j -> | ->//]; rewrite ffunE.
Qed.

Lemma clift_inj n p : injective (@clift n p).
Proof.
by move=> c1 c2 c1Ec2; rewrite -[c1](cliftK p) c1Ec2 cliftK.
Qed.

Lemma map_eqr (T1 T2 : eqType) (f : T1 -> T2) (s1 s2 : seq T1) :
   injective f ->
   ([seq f i | i <- s1] == [seq f i | i <- s2]) = (s1 == s2).
Proof.
elim: s1 s2 => [[|] //|a s1 IH [|b s2]//=] fInj.
rewrite !eqseq_cons IH //.
case: (a =P b) => [->//|]; first by rewrite eqxx.
by case: (f a =P f b) => [/fInj|//].
Qed.

Lemma eq_map_clift n p (cs1 cs2 : seq (configuration n)) :
   ([seq (clift p) i | i <- cs1] == [seq (clift p) i | i <- cs2]) = (cs1 == cs2).
Proof. by apply/map_eqr/clift_inj. Qed.


Lemma perfect_unlift n p : cunlift (perfect n.+1 p) = perfect n p.
Proof. by apply/ffunP => i; rewrite !ffunE. Qed.

Lemma move_ldisk n (c1 c2 : configuration n.+1) : 
  move c1 c2 -> c1 ldisk != c2 ldisk -> cunlift c1 = cunlift c2.
Proof.
move=> c1Mc2 c1lDc2l.
apply/ffunP=> i; rewrite !ffunE.
by apply: move_disk1 c1Mc2 c1lDc2l _; apply: neq_lift.
Qed.

Lemma on_top_unlift n (d : disk n) (c : configuration n.+1) :
  on_top (lift ldisk d) c -> on_top d (cunlift c).
Proof.
move=> dTc d1.
rewrite !ffunE => /dTc.
by rewrite /= /bump ![n <= _]leqNgt !ltn_ord.
Qed.

Lemma move_unlift n (c1 c2 : configuration n.+1) :
  move c1 c2 -> c1 ldisk = c2 ldisk -> move (cunlift c1) (cunlift c2).
Proof.
case: n c1 c2 => [c1 c2|n c1 c2] /moveP[d [H1 H2 H3 H4]] c1Ec2.
  case/negP : (irH (c1 d)).
  have dE : d = ldisk by apply/val_eqP => /=; case: (d) => [] [].
  by rewrite {2}dE ?c1Ec2 -dE.
apply/moveP.
exists (odflt ldisk (unlift ldisk d)).
case: unliftP => [j dE /=|dE]; last first.
  case/negP: (irH (c1 d)).
  by rewrite {2}dE ?c1Ec2 -dE.
split => [|d2 jDd2||].
- by rewrite !ffunE -dE.
- rewrite !ffunE.
  apply: H2.
  apply: contra jDd2 => /eqP.
  by rewrite dE => /lift_inj->.
- by apply: on_top_unlift; rewrite -dE.
by apply: on_top_unlift; rewrite -dE.
Qed.

Lemma path_move_rev (n : nat) (c : configuration n) cs : 
  path move (last c cs) (rev (belast c cs)) = path move c cs.
Proof.
by rewrite rev_path; apply: eq_path => c1 c2; exact: move_sym. 
Qed.

Lemma path_lift n p (c : configuration n) (cs : seq (configuration _)) :
    path move c cs -> path move (clift p c) (map (clift p) cs).
Proof.
elim: cs c => //= c1 cs IH c /andP[H1 H2].
by rewrite move_lift //= IH.
Qed.

Lemma path_unlift n (c : configuration n.+1) (cs : seq (configuration _)) :
   (forall c1, c1 \in cs -> c1 ldisk = c ldisk)-> 
    path move c cs -> path move (cunlift c) (map cunlift cs).
Proof.
elim: cs c => //= c1 cs IH c Hc /andP[H1 H2].
by rewrite move_unlift ?IH // => [c2 Hc2|];
   rewrite ?[RHS]Hc ?[LHS]Hc ?inE ?eqxx ?Hc2 ?orbT.
Qed.

Inductive pathS_spec (n : nat)  (c : configuration n.+1) (cs : seq (configuration n.+1)) :
   forall (b : bool), Type
  :=
  pathS_specW : 
    forall (p := c ldisk) (c1 := cunlift c) (cs1 := map cunlift cs),
      cs = map (clift p) cs1 -> path move c1 cs1 -> pathS_spec c cs true |
  pathS_spec_move : 
    forall (p1 := c ldisk) p2 cs1 cs2
           (c1 := cunlift c)
           (c2 := clift p2 (last c1 cs1)),
        p1 != p2 -> r p1 p2 -> 
        cs = map (clift p1) cs1 ++ c2 :: cs2 ->
        path move c1 cs1 -> move (clift p1 (last c1 cs1)) c2 ->
        path move c2 cs2 ->
        pathS_spec c cs true |
  pathS_spec_false : pathS_spec c cs false.

(* Inversion theorem on a path for disk n.+1 *)
Lemma pathSP  n (c : configuration n.+1) cs : pathS_spec c cs (path move c cs).
Proof.
have [Hp|_] := boolP (path _ _ _); last by apply: pathS_spec_false.
pose f (c1 : configuration n.+1) := c1 ldisk != c ldisk.
have [Hh|/hasPn Hn] := boolP (has f cs); last first.
  have csE : cs = map (clift (c ldisk)) (map cunlift cs).
    rewrite -map_comp -[LHS]map_id.
    apply/eq_in_map => x /Hn; rewrite negbK => /eqP <-/=.
    by rewrite cunliftK.
  apply: pathS_specW csE _.
  by apply: path_unlift => // c1 /Hn; rewrite negbK => /eqP.
pose n1 := find f cs; pose lc1 := nth c cs n1.
pose p1 := c ldisk; pose p2 := lc1 ldisk.
have p1Dp2 : p1 != p2.
  by have := nth_find c Hh; rewrite eq_sym.
pose c1 := cunlift c.
pose lcs1 := take n1 cs; pose cs2 := drop n1.+1 cs.
have slcs1 : size lcs1 = n1 by rewrite size_take -has_find Hh.
have Plcs1 c2 : c2 \in lcs1 -> c2 ldisk = p1.
  move=> c2Ilcs1p; move: (c2Ilcs1p).
  rewrite -index_mem slcs1 => /(before_find c) /idP /negP.
  rewrite negbK => /eqP.
  by rewrite -[cs](cat_take_drop n1) nth_cat index_mem c2Ilcs1p nth_index.
pose cs1 := map cunlift lcs1.
have lcs1E :  lcs1 = map (clift p1) cs1.
  rewrite -map_comp -[LHS]map_id.
  apply/eq_in_map => x /Plcs1 H.
  by rewrite /= -H cunliftK.
have csE : cs = map (clift p1) cs1 ++ lc1 :: cs2.
  by rewrite -[cs](cat_take_drop n1.+1)  -cat_rcons -lcs1E 
             (take_nth c) // -has_find.
have Hm : move (last c lcs1) lc1.
 by move: Hp; rewrite csE lcs1E cat_path /= => /and3P[].
have lc1E : lc1 = clift p2 (last c1 cs1).
  rewrite /p2.
  have Hd : (last c lcs1) ldisk != lc1 ldisk.
    case: (lcs1) Plcs1 => //= a l -> //.
    by apply: mem_last.
  rewrite last_map -[LHS]cunliftK.
  congr clift.
  apply/ffunP=> i; rewrite !ffunE /=.
  apply/sym_equal/(move_disk1 Hm Hd).
  by apply/eqP/val_eqP/neq_bump.
have Hm1 : move ↑[last c1 cs1]_p1 ↑[last c1 cs1]_p2.
  have ->: clift p1 (last (cunlift c) cs1) = last c lcs1.
    by rewrite -[in LHS]last_map -lcs1E cunliftK.
  by rewrite -lc1E.
apply: pathS_spec_move p1Dp2 _ _ _ (Hm1) _ => //.
- case/moveP: Hm1 => x [].
  by rewrite !ffunE; case: unliftP => [j|]; rewrite //= irH.
- by rewrite csE lc1E lcs1E.
- apply: path_unlift => //.
  by move: Hp; rewrite -[cs](cat_take_drop n1) cat_path => /andP[].
rewrite -lc1E.
by move: Hp; rewrite csE cat_path /= => /and3P[].
Qed.

(* we can restrict a path from n.+1 to n *)
Lemma pathS_restrict n (c : configuration n.+1) cs :
   path move c cs -> 
   {cs'|
    [/\ path move (cunlift c) cs',
        last (cunlift c) cs' = cunlift (last c cs) &
        size cs' <= size cs ?= 
          iff (cs == map (clift (c ldisk)) cs')]}.
Proof.
elim: cs c => /= [c _|c1 cs IH c /andP[cMc1 /IH[cs1 [c1Pcs1 lccs1Mlc1cs S]]]].
  by exists [::]; split; rewrite ?setd_id //; apply: leqif_refl; rewrite !eqxx.
have [/eqP c1dEcd|c1dDcd] := boolP (c ldisk == c1 ldisk).
  exists (cunlift c1 :: cs1); split=> //=.
    by rewrite move_unlift.
  by rewrite eqseq_cons c1dEcd cunliftK eqxx.
have -> : cunlift c = cunlift c1.
  apply/ffunP=> d1; rewrite !ffunE.
  apply: move_disk1 c1dDcd _ => //.
  by apply/eqP/val_eqP/neq_bump.
exists cs1; split=> //=.
apply/leqifP; case: eqP=> [H|/= _]; last by rewrite ltnS S.
by rewrite -[_.+1]/(size (c1 :: cs)) H size_map.
Qed.

(* we can restrict a path from n.+1 to n *)
Lemma pathS_restrictD n (c : configuration n.+1) c1 cs :
   path move c cs -> c1 \in cs -> c1 ldisk != c ldisk ->
   {cs'|
    [/\ path move (cunlift c) cs',
        last (cunlift c) cs' = cunlift (last c cs) &
        size cs' < size cs]}.
Proof.
move=> cPcs c1Ics c1dDcd.
have [cs1 [H1 H2 H3]] := pathS_restrict cPcs.
exists cs1; split => //.
move/leqifP : H3; case: eqP => // cs1Ecs.
case/eqP: c1dDcd.
move: c1Ics; rewrite cs1Ecs => /mapP[x xIcs1 ->].
by rewrite !ffunE /= unlift_none.
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
Arguments cunlift {q n}.

Notation " ↑[ c ]_ p" := (clift p c) (at level 5, format "↑[ c ]_ p").
Notation " ↓[ c ]" := (cunlift c) (at level 5, format "↓[ c ]").

Section Projection.

Variables n q1 q2 : nat.
Variable c : {ffun 'I_n.+1 -> 'I_q2}.
Variable p : 'I_q1 -> 'I_q2.
Hypothesis p_inj : injective p.

Definition proj_list :=
      filter (fun i => c i \in codom p) 
                (map inord (iota 0 n.+1)).
Let L := proj_list.
Definition size_proj_list := (size L).-1.+1.
Let mcs := size_proj_list.
Let mds (i : 'I_n.+1)  : 'I_mcs := inord (index i L).
Let uds (i : 'I_mcs) := nth ord0 L i.

Let L_sorted : sorted (fun i j : 'I_ _ => i < j) L.
Proof.
apply: sorted_filter; first by apply: ltn_trans.
move: (leqnn n.+1); rewrite -{1}(addn0 n.+1).
elim: {1 9}_.+1 0 => //= m IH k.
rewrite addSnnS => H.
have H1 := IH _ H.
case: m {IH}H1 H => //= m -> H1.
rewrite !inordK ?leqnn ?(leq_trans _ H1) ?leq_addl //.
by rewrite -add1n leq_add2r.
Qed.

Let L_uniq : uniq L.
Proof.
apply: sorted_uniq L_sorted; last by apply: ltnn.
by apply: ltn_trans.
Qed.

Lemma mdsK i :  c i \in codom p -> uds (mds i) = i.
Proof.
move=> cIp.
have iIl : i \in L.
  rewrite mem_filter cIp.
  set l := map _ _ .
  have->: i = nth (inord 0) l i.
    by rewrite (nth_map 0) ?size_iota // nth_iota // inord_val.
  by rewrite mem_nth // size_map size_iota.
rewrite /uds /mds /= inordK.
  by apply: nth_index.
case: L iIl => // a l aIal; by rewrite index_mem.
Qed.

Lemma udsK i : mds (uds i) = i.
Proof.
move: i.
rewrite /mds /uds /mcs /size_proj_list.
case: L L_uniq => [_|a l Ual i].
  by case => [] [] // i; apply/val_eqP; rewrite /= inordK.
by rewrite index_uniq // inord_val.
Qed.

(* if mcs = 1 then L is empty ! *)
Lemma uds_codom i : 1 < mcs -> c (uds i) \in codom p.
Proof.
rewrite /mcs /uds /L /proj_list.
set u := map _ _; set v := filter _ _ => Hs.
have /allP := filter_all (fun i => c i \in codom p) u.
apply.
rewrite -/v mem_nth //.
have := ltn_ord i.
have := Hs.
rewrite /mcs /size_proj_list /L /proj_list -/u -/v.
by case: {1 3 5}(size _).
Qed.

Definition mask (c1 : {ffun 'I_mcs -> 'I_q1}) : {ffun 'I_n.+1 -> 'I_q2} :=
  [ffun i => if c i \in codom p then p (c1 (mds i)) else c i].

Variable r1 : rel 'I_q1.
Variable r2 : rel 'I_q2.
Hypothesis p_rel : forall i j, r1 i j -> r2 (p i) (p j).

Lemma path_nth  (T : Type) (e : rel T) (x : T) (l : seq T) (x0 : T)  i j :
  transitive e -> path e x l -> i < j <= size l ->
   e (nth x0 (x :: l) i) (nth x0 (x :: l) j).
Proof.
move=> eT /pathP eP.
elim: j => // j IH /andP[].
rewrite leq_eqVlt eqSS => /orP[/eqP<- |H1 H2]; first by apply: eP.
apply: eT (IH _) _; first by rewrite (ltnW H2) andbT.
by apply: eP.
Qed.

Lemma sorted_nth  (T : eqType) (e : rel T) (l : seq T) (x0 : T)  i j :
  transitive e -> sorted e l -> i < j <= (size l).-1 ->
   e (nth x0 l i) (nth x0 l j).
Proof.
case: l => [_ _ /=|*].
  by case: j; case: i => //= u v ; rewrite ltn0 andbF.
by apply: path_nth.
Qed.

(* to be cleaned *)
Lemma proj_path (c1 : configuration q1 mcs) cs :
  1 < mcs ->
  path (move r1) c1 cs -> 
  path (move r2) (mask c1) (map mask cs).
Proof.
move=> mcsG1 /(pathP c1) H.
apply/(pathP c) => i; rewrite size_map => Hi.
rewrite -map_cons !(nth_map c1) //=; last first.
  by apply: leq_trans Hi _. 
case/moveP: (H _ Hi) => d [H1d H2d H3d H4d].
apply/moveP.
have cu : c (uds d) \in codom p by apply: uds_codom.
exists (uds d); split => //=.
- rewrite !ffunE cu.
  by apply: p_rel; rewrite !udsK.
- move=> d2 dDd2.
  rewrite !ffunE; case: (boolP (_ \in _)) => // HI.
  rewrite H2d //.
  apply: contra dDd2 => /eqP->.
  by rewrite mdsK.
- move=> u; rewrite !ffunE cu.
  case: (boolP (_ \in _)) => // HI; last first.
    move=> Ecu; case/negP: HI.
    rewrite -Ecu.
    by apply/codomP; eexists.
  rewrite udsK => /p_inj /H3d.
  rewrite leq_eqVlt => /orP[/val_eqP->|].
    rewrite mdsK //.
  rewrite -{2}[u]mdsK // => HH.
  apply: ltnW.
  have := sorted_nth _ _ L_sorted _.
  apply; first exact: ltn_trans.
  rewrite HH -ltnS /=.
  by apply: ltn_ord.
move=> u; rewrite !ffunE cu.
case: (boolP (_ \in _)) => // HI; last first.
  move=> Ecu; case/negP: HI.
  rewrite -Ecu.
  by apply/codomP; eexists.
rewrite udsK => /p_inj /H4d.
rewrite leq_eqVlt => /orP[/val_eqP->|].
  rewrite mdsK //.
rewrite -{2}[u]mdsK // => HH.
apply: ltnW.
have := sorted_nth _ _ L_sorted _.
apply; first exact: ltn_trans.
rewrite HH -ltnS /=.
by apply: ltn_ord.
Qed.

Lemma gdist_mask (c1 c2 : configuration q1 mcs) :
 1 < mcs ->
 connect (move r1) c1 c2 ->
 gdist (move r2) (mask c1) (mask c2) <=
 gdist (move r1) c1 c2.
Proof.
move=> mcsG1 /gdist_path [p1 [c1Pp1 lc1p2Ec2 Uc1p1 <-]].
pose p2 := map mask p1.
rewrite -(size_map mask).
apply: gdist_path_le; first by apply: proj_path.
by rewrite last_map lc1p2Ec2.
Qed.

End Projection.
 

