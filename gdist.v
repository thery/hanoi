From mathcomp Require Import all_ssreflect.

(******************************************************************************)
(*             Definition of a distance on graph                              *)
(* sconnect_n r n x == the set of all the elements connected to x in n steps  *)
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

Fixpoint sconnect_n n x :=
  if n is n1.+1 then
    \bigcup_(y in (rgraph r x)) sconnect_n n1 y
  else [set x].

Lemma sconnect_nP n x y :
  reflect 
    (exists p : seq T, [/\ path r x p, last x p = y & size p = n])
    (y \in sconnect_n n x).
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
  find (fun n => t2 \in sconnect_n n t1) (iota 0 #|T|).

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
have F : t2 \in sconnect_n (size p) t1.
  by apply/sconnect_nP; exists p.
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
move => /hasP[n _ /sconnect_nP [p [H1p H2p H3p]]].
by exists p.
Qed.

Lemma gdist_nconnect t1 t2 : ~~ connect r t1 t2 -> `d[t1,t2] = #|T|.
Proof.
move=> H; apply/eqP.
have := gdist_card_le t1 t2.
by rewrite leq_eqVlt -gdist_connect (negPf H) orbF.
Qed.

Lemma gdist_path t1 t2 : 
  connect r t1 t2 -> {p |  [/\  path r t1 p,
                                last t1 p = t2,
                                uniq (t1 :: p) &
                                size p = `d[t1, t2]]}. 
Proof.
move=> t1Ct2.
case: (pickP [pred p |
        [&& path r t1 (p : `d[t1, t2].-tuple T), 
            uniq (t1 :: p) & last t1 p == t2]]) =>
      [p /and3P[H1P H2P /eqP H3P]|HC].
  exists p; split => //.
  by rewrite size_tuple.
move: (t1Ct2); rewrite gdist_connect => dLT.
absurd False => //.
move: (dLT); rewrite -[#|_|](size_iota 0) -has_find.
move => /(nth_find 0).
rewrite -[find _ _]/`d[t1, t2].
rewrite nth_iota // add0n => /sconnect_nP[p [H1p H2p H3p]].
case/shortenP: H1p H2p  => p' H1p' H2p' H3p' H2p.
have Hs : size p' == `d[t1, t2].
  rewrite eqn_leq gdist_path_le // andbT -H3p.
  apply: uniq_leq_size => //.
  by case/andP: H2p'.
have /idP[] := HC (Tuple Hs).
apply/and3P; split=> //.
by rewrite H2p.
Qed.

Lemma gdist_catl t1 t2 p1 p2 : 
   size (p1 ++ p2) = `d[t1, t2] ->
   path r t1 (p1 ++ p2) ->
   last t1 (p1 ++ p2) = t2 ->
   size p1 = `d[t1, last t1 p1].
Proof.
move => sp1p2D t1Pp1p2 t1p1p2Lt2.
move: t1Pp1p2; rewrite cat_path => /andP[t1Pp1 tlLp1Pp2].
have /gdist_path[p3 [t1Pp3 t1p3L _ p3SE]] : connect r t1 (last t1 p1).
  by apply/connectP; exists p1.
have : `d[t1, last t1 p1] <= size p1 by rewrite gdist_path_le.
rewrite leq_eqVlt => /orP[/eqP//|dLSp1].
have : size(p3 ++ p2) < `d[t1, t2] by rewrite -sp1p2D !size_cat ltn_add2r p3SE.
rewrite ltnNge => /negP[].
apply: gdist_path_le; first by rewrite cat_path t1Pp3 t1p3L.
by rewrite last_cat t1p3L -last_cat.
Qed.

Lemma gdist_catr t1 t2 p1 p2 : 
   size (p1 ++ p2) = `d[t1, t2] ->
   path r t1 (p1 ++ p2) ->
   last t1 (p1 ++ p2) = t2 ->
   size p2 = `d[last t1 p1, t2].
Proof.
move => sp1p2D t1Pp1p2 t1p1p2Lt2.
move: t1Pp1p2; rewrite cat_path => /andP[t1Pp1 tlLp1Pp2].
have /gdist_path[p3 [t1Lp1Pp3 t1Lp1p3L _ p3SE]] : connect r (last t1 p1) t2.
  by apply/connectP; exists p2 => //; rewrite -last_cat.
have : `d[last t1 p1, t2] <= size p2 by rewrite gdist_path_le // -last_cat.
rewrite leq_eqVlt => /orP[/eqP//|dLSp1].
have : size(p1 ++ p3) < `d[t1, t2] by rewrite -sp1p2D !size_cat ltn_add2l p3SE.
rewrite ltnNge => /negP[].
apply: gdist_path_le; first by rewrite cat_path t1Pp1.
by rewrite last_cat.
Qed.

Lemma gdist_cons t1 t2 a p  : 
  size (a :: p) = `d[t1, t2] -> path r t1 (a :: p) -> 
  last a p = t2 -> size p = `d[a, t2].
Proof. by exact: (@gdist_catr t1 t2 [::a]). Qed. 

Lemma gdist_triangular t1 t2 t3 : `d[t1, t2] <= `d[t1, t3] + `d[t3, t2].
Proof.
have [/gdist_path[p1 [H1p1 H2p1 H3p1 <-]] |/gdist_nconnect->] 
         := boolP (connect r t1 t3); last first.
  by apply: leq_trans (gdist_card_le _ _) (leq_addr _ _).
have [/gdist_path[p2 [H1p2 H2p2 H3p2 <-]] |/gdist_nconnect->] 
         := boolP (connect r t3 t2); last first.
  by apply: leq_trans (gdist_card_le _ _) (leq_addl _ _).
rewrite -size_cat.
apply: gdist_path_le.
  by rewrite cat_path H1p1 H2p1.
by rewrite last_cat H2p1.
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
rewrite -gdist_connect => /gdist_path[[|t3 p] [H1p H2p H3p H4p]].
  by rewrite -H4p.
exists t3; split; first by case/andP: H1p.
apply/eqP; rewrite eqn_leq; apply/andP; split; last first.
 rewrite -subn1 leq_subLR (_ : 1 = `d[t1, t3]).
   by apply: gdist_triangular.
 rewrite gdist1; last by case/andP: H1p.
 by case/andP: H3p; rewrite inE negb_or => /andP[->].
rewrite (_ : _.-1 = size p); last by rewrite -H4p.
by apply: gdist_path_le => //; case/andP: H1p.
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

Lemma eq_sconnect (r1 r2 : rel T) : r1 =2 r2 -> sconnect_n r1 =2 sconnect_n r2.
Proof.
move=> r1Er2.
elim => //= n IH y; apply: eq_big => // i.
by rewrite ![_ \in _]rgraphK r1Er2.
Qed.

Lemma eq_dist (r1 r2 : rel T) : r1 =2 r2 -> gdist r1 =2 gdist r2.
Proof.
move=> r1Er2 t1 t2.
apply: eq_find => n.
by rewrite (eq_sconnect r1Er2).
Qed.

Lemma gdist_sym t1 t2 :
 `d[t1, t2]_r  =  `d[t2, t1]_(fun z : T => r^~ z).
Proof.
apply: eq_find => i.
apply/sconnect_nP/sconnect_nP => /= [] [p [H1p H2p H3p]].
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

Lemma gdistC t1 t2 : symmetric r -> `d[t1, t2]_r  =  `d[t2, t1]_r.
Proof.
move=> rSym; rewrite gdist_sym.
by apply: eq_dist.
Qed.

End gdistProp.
