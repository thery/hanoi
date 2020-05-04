From mathcomp Require Import all_ssreflect.

(******************************************************************************)
(*             Definition of a distance on graph                              *)
(*   connectn r n x == the set of all the elements connected to x in n steps  *)
(*                                                                            *)
(*   `d[t1, t2]_r   == the distance between t1 and t2 in r                    *)
(*                     if they are not connected returns the cardinal of the  *)
(*                     the subtype                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section gdist.

Variable T : finType.
Variable r : rel T.

Fixpoint connectn n x :=
  if n is n1.+1 then \bigcup_(y in (rgraph r x)) connectn n1 y
  else [set x].

Lemma connectnP n x y :
  reflect 
    (exists p : seq T, [/\ path r x p, last x p = y & size p = n])
    (y \in connectn n x).
Proof.
elim: n x y =>  [x y|n IH x y /=].
  rewrite inE; apply: (iffP idP) => [/eqP->|[[|a l] [] //= _ ->//]].
  by exists [::].
apply: (iffP idP) => [/bigcupP[i]|[[|i p]//= [H1 H2 H3]]].
- rewrite [i \in _]rgraphK => iRk /IH [p [H1 H2 H3]].
  by exists (i :: p); split; rewrite /= ?(iRk, H3).
- by [].
case/andP: H1 => H11 H12.
have F : i \in rgraph r x by rewrite [_ \in _]rgraphK. 
apply: (subsetP (bigcup_sup _ F)).
by apply/IH; exists p; split => //; case: H3.
Qed.

Definition gdist t1 t2 :=
  find (fun n => t2 \in connectn n t1) (iota 0 #|T|).

Local Notation " `d[ t1 , t2 ] " := (gdist t1 t2)
  (format " `d[ t1 ,  t2 ] ").

Lemma gdist_eq0 t1 t2 : (`d[t1, t2] == 0) = (t1 == t2).
Proof.
have tG : #|T| > 0 by rewrite (cardD1 t1).
rewrite /gdist.
case: #|_| tG => // n _.
rewrite (iota_add _ 1) /= inE [t2 == _]eq_sym.
by case: (t1 =P t2).
Qed.

Lemma gdist_gt0 t1 t2 : (0 < `d[t1, t2]) = (t1 != t2).
Proof. by rewrite ltnNge leqn0 gdist_eq0. Qed.

Lemma gdist0 t : `d[t, t] = 0.
Proof. by apply/eqP; rewrite gdist_eq0. Qed.

Lemma gdist_card_le t1 t2 : `d[t1, t2] <= #|T|.
Proof.
rewrite -[#|T|](size_iota 0).
apply: find_size.
Qed.

Lemma gdist_path_le t1 t2 p :
  path r t1 p -> last t1 p = t2 -> `d[t1, t2] <= size p.
Proof.
move=> Hp Hl.
have [tLp|pLt] := leqP #|T| (size p).
  apply: leq_trans tLp.
  by apply: gdist_card_le.
have F : t2 \in connectn (size p) t1.
  by apply/connectnP; exists p.
case: leqP => // /(before_find _) // /(_ 0).
by rewrite seq.nth_iota // F.
Qed.

Lemma gdist_connect t1 t2 : connect r t1 t2 = (`d[t1,t2] < #|T|).
Proof.
apply/connectP/idP=> [[p /shortenP[p' Hp' Hu _ Ht]]|].
  apply: leq_trans (_ : size p' < _).
    by apply: gdist_path_le.
  rewrite -[_.+1]/(size (t1 :: p')) cardE.
  apply: uniq_leq_size => // i.
  by rewrite mem_enum.
rewrite -[#|_|](size_iota 0) -has_find.
move => /hasP[n _ /connectnP [p [H1p H2p H3p]]].
by exists p.
Qed.

Lemma gdist_nconnect t1 t2 : ~~ connect r t1 t2 -> `d[t1,t2] = #|T|.
Proof.
move=> H; apply/eqP.
have := gdist_card_le t1 t2.
by rewrite leq_eqVlt -gdist_connect (negPf H) orbF.
Qed.

(* geodesic path *)
Definition gpath t1 t2 p :=
  [&& path r t1 p, last t1 p == t2 & `d[t1, t2] == size p].

Lemma gpathP t1 t2 p :
  reflect ([/\ path r t1 p, last t1 p = t2 & `d[t1, t2] = size p])
          (gpath t1 t2 p).
Proof.
apply: (iffP and3P) => [[t1Pp /eqP t1pLt2 /eqP t1t2D]|
                        [t1Pp t1pLt2 t1t2D]]; first by split.
by split => //; apply/eqP.
Qed.

Lemma gpath_connect t1 t2 : connect r t1 t2 -> {p | gpath t1 t2 p}.
Proof.
move=> t1Ct2.
case: (pickP [pred p | gpath t1 t2 (p : `d[t1, t2].-tuple T)]) => [p Hp|HC].
  by exists p.
move: (t1Ct2); rewrite gdist_connect => dLT.
absurd False => //.
move: (dLT); rewrite -[#|_|](size_iota 0) -has_find.
move => /(nth_find 0).
rewrite -[find _ _]/`d[t1, t2].
rewrite nth_iota // add0n => /connectnP[p [H1p H2p /eqP H3p]].
have /idP[] := HC (Tuple H3p).
by apply/and3P; split=> //=; apply/eqP=> //; rewrite (eqP H3p).
Qed.

Lemma gpath_last t1 t2 p : gpath t1 t2 p -> last t1 p = t2.
Proof. by case/gpathP. Qed.

Lemma gpath_dist t1 t2 p : gpath t1 t2 p -> `d[t1, t2] = size p.
Proof. by case/gpathP. Qed.

Lemma gpath_path t1 t2 p : gpath t1 t2 p -> path r t1 p.
Proof. by case/gpathP. Qed.

Lemma last_take (A : Type) (p : seq A) t t1 j : 
  j <= size p -> last t1 (take j p) = nth t (t1 :: p) j.
Proof.
elim: p t1 j => [t1 [|] //| a l IH t1 [|j]] //= H.
by apply: IH.
Qed.

(* ugly proof !! *)
Lemma gpath_uniq t1 t2 p : gpath t1 t2 p ->  uniq (t1 :: p).
Proof.
move=> gH; apply/(uniqP t1) => i j iH jH.
wlog : i j iH jH / i <= j.
  move=> H; case: (leqP i j) => [iLj|jLi]; first by apply: H.
  by move=> /(@sym_equal _ _ _) /H->; rewrite // ltnW.
rewrite leq_eqVlt => /orP[/eqP->//|iLj].
case/gpathP : gH  => t1Pp t1pLt2 dt1t2E.
case: j jH iLj => j // jH iLj.
case: i iH iLj => [_ _ t1E | ] //.
  pose p1 := drop j.+1 p.
  have t1Pp1 : path r t1 p1.
    move: (t1Pp); rewrite -[p](cat_take_drop j.+1) cat_path.
    rewrite /= in t1E.
    by rewrite (last_take t1) //= -t1E => /andP[].
  have t1p1L : last t1 p1 = t2.
    move: (t1pLt2); rewrite -[p](cat_take_drop j.+1) last_cat.
    rewrite /= in t1E.
    by rewrite (last_take t1) //= -t1E.
  have [] := boolP (`d[t1, t2] <= size p1) => [|/negP[]]; last first.
    by apply: gdist_path_le.
  rewrite leqNgt => /negP[]. 
  rewrite size_drop dt1t2E.
  rewrite /= in t1E.
  by rewrite -{2}[size p](subnK (_ : j < size p)) // addnS ltnS leq_addr.
move=> i iH; rewrite ltnS => iLj nE.
pose p1 := take i.+1 p ++ drop j.+1 p.
have [] := boolP (`d[t1, t2] <= size p1) => [|/negP[]].
  rewrite leqNgt => /negP[].
  rewrite size_cat size_take size_drop ifT //; last first.
    by rewrite -ltnS in iLj; apply: leq_trans iLj _.
  rewrite dt1t2E -{2}[size p](subnK (_ : j < size _)) //.
  by rewrite addnC ltn_add2l.
apply: gdist_path_le.
  move: t1Pp; rewrite -[p](cat_take_drop i.+1).
  rewrite -[drop _ _](cat_take_drop (j - i)) !cat_path.
  case/and3P => [-> _] /=.
  rewrite !(last_take t1) /=; last first.
  - rewrite size_drop -subSS.
    by apply: leq_sub2r.
  - by apply: leq_trans iLj _; rewrite ltnW //.
  rewrite drop_drop addnS subnK; last by rewrite ltnW.
  congr path.
  move: (nE) => /= ->.
  rewrite -[j - i]prednK //.
  by rewrite /= nth_drop -subnS addnC subnK //.
  by rewrite subn_gt0.
rewrite last_cat (last_take t1) // nE.
by rewrite -t1pLt2 -{3}[p](cat_take_drop j.+1) last_cat (last_take t1).
Qed.


Lemma gpath_catl t1 t2 p1 p2 : 
   gpath t1 t2 (p1 ++ p2) -> gpath t1 (last t1 p1) p1.
Proof.
move=> /gpathP[].
rewrite cat_path last_cat => /andP[t1Pp1 t1p1LPp2] t1p1Lp2Lt2 dt1t2E.
apply/gpathP; split => //. 
have : `d[t1, last t1 p1] <= size p1 by rewrite gdist_path_le.
rewrite leq_eqVlt => /orP[/eqP//|dLSp1].
have /gpath_connect[p3 /gpathP[H1 H2 H3]] : 
   connect r t1 (last t1 p1) by apply/connectP; exists p1.
have : size (p3 ++ p2) < `d[t1, t2] by rewrite dt1t2E !size_cat -H3 ltn_add2r.
rewrite ltnNge => /negP[].
apply: gdist_path_le; first by rewrite cat_path H1 // H2.
by rewrite last_cat H2.
Qed.

Lemma gpath_catr t1 t2 p1 p2 : 
   gpath t1 t2 (p1 ++ p2) -> gpath (last t1 p1) t2 p2.
Proof.
move=> /gpathP[].
rewrite cat_path last_cat => /andP[t1Pp1 t1p1LPp2] t1p1Lp2Lt2 dt1t2E.
apply/gpathP; split => //. 
have : `d[last t1 p1, t2] <= size p2 by rewrite gdist_path_le.
rewrite leq_eqVlt => /orP[/eqP//|dLSp1].
have /gpath_connect[p3 /gpathP[H1 H2 H3]] : 
   connect r (last t1 p1) t2 by apply/connectP; exists p2.
have : size (p1 ++ p3) < `d[t1, t2] by rewrite dt1t2E !size_cat -H3 ltn_add2l.
rewrite ltnNge => /negP[].
apply: gdist_path_le; first by rewrite cat_path H1 andbT.
by rewrite last_cat.
Qed.

Lemma gdist_cat t1 t2 p1 p2 : 
   gpath t1 t2 (p1 ++ p2) -> 
   `d[t1,t2] = `d[t1, last t1 p1] + `d[last t1 p1, t2].
Proof.
move=> gH.
rewrite (gpath_dist gH).
rewrite (gpath_dist (gpath_catl gH)) (gpath_dist (gpath_catr gH)) //.
by rewrite size_cat.
Qed. 

Lemma gpath_consl t1 t2 t3 p :  gpath t1 t2 (t3 :: p) -> `d[t1, t3] = 1.
Proof. by move=> /(@gpath_catl _ _ [::t3]) /= /gpathP[]. Qed.

Lemma gpath_consr t1 t2 t3 p : gpath t1 t2 (t3 :: p) -> gpath t3 t2 p.
Proof. by move=> /(@gpath_catr _ _ [::t3]). Qed.

Lemma gdist_cons t1 t2 t3 p : 
   gpath t1 t2 (t3 :: p) -> `d[t1,t2] = `d[t3, t2].+1.
Proof.
move=> gH.
by rewrite (@gdist_cat _ _ [::t3] p) // (gpath_consl gH).
Qed. 

Lemma gdist_triangular t1 t2 t3 : `d[t1, t2] <= `d[t1, t3] + `d[t3, t2].
Proof.
have [/gpath_connect[p pH]|/gdist_nconnect->] 
         := boolP (connect r t1 t3); last first.
  by apply: leq_trans (gdist_card_le _ _) (leq_addr _ _).
have [/gpath_connect [p2 p2H] |/gdist_nconnect->] 
         := boolP (connect r t3 t2); last first.
  by apply: leq_trans (gdist_card_le _ _) (leq_addl _ _).
rewrite (gpath_dist pH) (gpath_dist p2H) -size_cat.
apply: gdist_path_le.
  rewrite cat_path (gpath_path pH).
  by rewrite (gpath_last pH) (gpath_path p2H).
by rewrite last_cat (gpath_last pH) (gpath_last p2H).
Qed.

Lemma gdist1 t1 t2 : r t1 t2 -> `d[t1, t2] = (t1 != t2).
Proof.
move=> Hr; apply/eqP.
case: (t1 =P t2) => [<-|/eqP HE]; first by rewrite gdist_eq0.
rewrite eqn_leq -{1}[nat_of_bool _]/(size [::t2]) gdist_path_le /= ?andbT //.
by case: gdist (gdist_eq0 t1 t2); rewrite (negPf HE) .
Qed.

Lemma gdist_succ t1 t2 : 
  0 < `d[t1, t2] < #|T| -> {t3 | r t1 t3 /\ `d[t3, t2] = `d[t1, t2].-1}.
Proof.
case/andP => dP dT.
move: dT dP.
rewrite -gdist_connect => /gpath_connect[[|t3 p] pH].
  by rewrite (gpath_dist pH).
exists t3; split.
  by have /andP[] := gpath_path (@gpath_catl _ _ [::t3] _ pH).
by rewrite (gdist_cons pH). 
Qed.

Lemma gdist_neighboor t1 t2 t3 : r t1 t2 ->
  r t2 t1 -> [|| `d[t2, t3] == `d[t1, t3].-1,
                 `d[t2, t3] == `d[t1, t3] |
                 `d[t2, t3] == `d[t1, t3].+1].
Proof.
move=> t1Rt2 t2Rt1.
have : `d[t1, t3] - `d[t1, t2] <= `d[t2, t3] <= `d[t2, t1] + `d[t1, t3].
  by rewrite leq_subLR !gdist_triangular.
rewrite (gdist1 t1Rt2) (gdist1 t2Rt1).
(do 2 case: eqP) => //= E1 E2; rewrite ?subn0.
- by rewrite -eqn_leq => /eqP->; rewrite eqxx orbT.
- case/andP=> E3.
  rewrite leq_eqVlt => /orP[/eqP->|].
    by rewrite eqxx !orbT.
  rewrite ltnS => E4.
  by rewrite [`d[_, _] == `d[_, _]]eqn_leq E3 E4 orbT.
- case/andP=> E3.
  rewrite leq_eqVlt => /orP[/eqP->|].
    by rewrite eqxx !orbT.
  case: (`d[t1, t3]) E3 => //= d.
  rewrite subSS subn0 ltnS => E3 E4.
  by rewrite [_ == d]eqn_leq E3 E4.
case/andP=> E3.
rewrite leq_eqVlt => /orP[/eqP->|].
  by rewrite eqxx !orbT.
rewrite ltnS leq_eqVlt => /orP[/eqP->|].
  by rewrite eqxx !orbT.
case: (`d[t1, t3]) E3 => //= d.
rewrite subSS subn0 ltnS => E3 E4.
by rewrite [_ == d]eqn_leq E3 E4.
Qed.

End gdist.

Notation " `d[ t1 , t2 ]_ r " := (gdist r t1 t2) (at level 10,
  format "`d[ t1 ,  t2 ]_ r").

Section gdistProp.

Variable T : finType.
Variable r : rel T.

Lemma eq_connectn (r1 r2 : rel T) : r1 =2 r2 -> connectn r1 =2 connectn r2.
Proof.
move=> r1Er2.
elim => //= n IH y; apply: eq_big => // i.
by rewrite ![_ \in _]rgraphK r1Er2.
Qed.

Lemma eq_dist (r1 r2 : rel T) : r1 =2 r2 -> gdist r1 =2 gdist r2.
Proof.
move=> r1Er2 t1 t2.
apply: eq_find => n.
by rewrite (eq_connectn r1Er2).
Qed.

Lemma gdist_sym t1 t2 :
 `d[t1, t2]_r  =  `d[t2, t1]_(fun z : T => r^~ z).
Proof.
apply: eq_find => i.
apply/connectnP/connectnP => /= [] [p [H1p H2p H3p]].
  exists (rev (belast t1 p)); split => //.
  - by rewrite -H2p rev_path.
  - rewrite -H2p; case: (p) => //= a p1.
    by rewrite rev_cons last_rcons.
  by rewrite size_rev size_belast.
exists (rev (belast t2 p)); split => //.
- by rewrite -H2p rev_path.
- rewrite -H2p; case: (p) => //= a p1.
  by rewrite rev_cons last_rcons.
by rewrite size_rev size_belast.
Qed.

Lemma gpath_rev t1 t2 p : gpath r t1 t2 p -> gpath (fun z : T => r^~ z) t2 t1 (rev (belast t1 p)).
Proof.
move=> /gpathP[H1 H2] H3.
apply/gpathP; split => //.
- by rewrite -rev_path H2 in H1.
- case: (p) H2 => //= a p1.
  by rewrite /= rev_cons last_rcons.
by rewrite size_rev size_belast -gdist_sym.
Qed.

Lemma gdistC t1 t2 : symmetric r -> `d[t1, t2]_r  =  `d[t2, t1]_r.
Proof.
move=> rSym; rewrite gdist_sym.
by apply: eq_dist.
Qed.

Lemma eq_gpath (e1 e2 : rel T) t1 t2 c :
    e1 =2 e2 -> gpath e1 t1 t2 c = gpath e2 t1 t2 c.
Proof.
by move=> e1Ee2; apply/gpathP/gpathP; rewrite (eq_path e1Ee2) (eq_dist e1Ee2).
Qed.

Lemma gpathC t1 t2 p : 
 symmetric r -> gpath r t1 t2 p -> gpath r t2 t1 (rev (belast t1 p)).
Proof.
move=> hIrr /gpath_rev.
by rewrite (@eq_gpath _ _ _ _ _ (_ : _ =2 r)).
Qed.

End gdistProp.
