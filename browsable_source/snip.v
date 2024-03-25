(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require tacticext.
Require boolprop.
Require funs.
Require dataset.
Require natprop.
Require seq.
Require finset.
Require paths.
Require connect.
Require hypermap.
Require jordan.
Require color.
Require geometry.
Require patch.

Set Implicit Arguments.

Section Snip.

Variable g : hypermap.
Hypothesis Hpg : (planar g).

(* Cutting a planar graph along a ring (i.e., a simple rlink cycle r).   *)

Variable r : (seq g).

Hypothesis HUr : (scycle rlink r).
Local Hr := (scycle_cycle HUr).
Local UrF := (scycle_simple HUr).
Local Ur := (scycle_uniq HUr).

(* The disk defined by the ring is defined by the darts that can be      *)
(* reached from the ring by a clink path that starts with a inverse node *)
(* step and that does not cross the contour. That disk is node-closed.   *)
(* Because a planar g has the Jordan property, the edge-interior of that *)
(* disk is simply g with r removed (assuming we're not in the trivial    *)
(* case where r is an edge 2-cycle). For the face interior there we need *)
(* to remove all of (fband r).                                           *)

Definition dlink [x, y : g] : bool := (andb (negb (r x)) (clink x y)).

Definition dconnect [x, y : g] : bool := (connect dlink (finv node y) x).

Definition diskN [x : g] : bool := (has (dconnect x) r).

Definition diskE : (set g) := (setD diskN r).

Definition diskF : (set g) := (setD diskN (fband r)).

Definition diskFC : (set g) := (setD (setC diskN) (fband r)).

Lemma diskN_node : (fclosed node diskN).
Proof.
Cut (fclosed (finv node) diskN).
  Move=> Hn; Apply: (intro_closed (Snode g)) => [x y Dy Hx].
  By Rewrite: (fclosed1 Hn y) -(eqP Dy) (finv_f (Inode g)).
Def: Inode' := (finv_inj (Inode g)).
Apply: (intro_closed (fconnect_sym Inode')) => [x y Dy Hx]; Apply/hasP.
Case Hrx: (r x); LeftBy Exists x; RightBy Rewrite: /dconnect (eqP Dy) connect0.
Case/hasP: Hx => [z Hrz Hzx].
Exists z; [Done | Apply: (connect_trans Hzx); Apply connect1].
By Rewrite: /dlink Hrx /clink /relU /setU Dy.
Qed.

Lemma diskN_E : diskN =1 (setU r diskE).
Proof.
Move=> x; Rewrite: /setU /diskE /setD; Case Hx: (r x); RightDone.
Rewrite: -(diskN_node (introT eqP (f_finv (Inode g) x))).
By Apply/hasP; Exists x; RightBy Apply: connect0.
Qed.

Lemma diskF_face : (fclosed face diskF).
Proof.
Apply: (intro_closed (Sface g)) => [x y]; Case/eqP {y}; Move/andP=> [HxF HxN].
Rewrite: /diskF /setD -(fclosed1 (fbandF r)) HxF.
Case: (hasP HxN) => [y Hy Hyx]; Apply: (introT hasP ?); Exists y; Auto.
Apply: (connect_trans Hyx) {y Hy Hyx}; Apply connect1; Apply/andP.
Split; RightBy Apply clinkF.
By Apply/idP=> [Hx]; Case/idP: HxF; Apply: (subsetP (ring_fband ?)).
Qed.

Lemma diskFC_face : (fclosed face diskFC).
Proof.
Move=> /= x y Dy; Move: (diskF_face Dy).
Rewrite: /diskFC /diskF /setD /setC (fbandF r Dy).
By Case Hy: (fband r y); RightBy Simpl; Case.
Qed.

Lemma diskE_edge : (fclosed edge diskE).
Proof.
Apply: (intro_closed (Sedge g)) => [x y]; Case/eqP {y}; Move=> Hx.
Cut (EX x' | (diskN x') & (EX p |
      (fpath face x' p) /\ (last x' p) = (edge x)
    & (negb (has r (Adds x' p))))).
  Simpl; Move=> [x' Hx' [p [Hp []] H]]; Case: {H}(norP H) => [Hrx' Hrp].
  Elim/last_ind: p Hp Hrp => [|p y Hrec]; Simpl.
    By Move=> _; Rewrite: /diskE /setD Hx' Hrx'.
  Rewrite: last_add_last -cats1 path_cat has_cat /= andbT orbF.
  Move/andP=> [Hp Dy]; Move/norP=> [Hrp Hry].
  Rewrite: /diskE /setD ~Hry /=; Apply/hasP.
  Case/andP: {Hrec Hp Hrp}(Hrec Hp Hrp) => [Hry' Hy'].
  Case/hasP: Hy' => [z Hz Hzy']; Exists z; Auto.
  Apply: (connect_trans Hzy'); Apply connect1.
  By Rewrite: /dlink (negbE Hry') -(eqP Dy) clinkF.
Move/andP: Hx => [Hrx HxN]; Pose x' := (face (edge x)).
Step Hx': (cface x' (edge x)) By Rewrite: Sface /x' fconnect1.
Case/connectP: Hx'; Move=> q0; Case/shortenP=> [q Hq Uq _] {q0} Eq.
Case Hqr: (negb (has r (Adds x' q))).
  By Exists x'; [Rewrite: (fclosed1 diskN_node) /x' Eedge | Exists q; Auto].
Case/hasP: Hqr => [y Hqy Hry]; Case/rot_to: {}Hry {}Hr => [i r' Dr].
Rewrite: -(cycle_rot i rlink r) (cycle_path y) Dr /=.
Pose z := (last y r'); Pose z' := (face (edge z)); Move/andP=> [Hzy Hr'].
Step Hrz: (r z) By Rewrite: -(mem_rot i) Dr /z mem_last.
Step Hyz': (cface y z') By Rewrite: Sface /z' -cface1.
Step Hqz': (Adds x' q z').
  Step HqF: (cface x') =1 (Adds x' q).
    Apply: fconnect_cycle; RightBy Apply: setU11.
    By Rewrite: (cycle_path x) /= Eq {1}/eqdf set11.
  By Rewrite: -HqF; Apply: (connect_trans ? Hyz'); Rewrite HqF.
Simpl in Hqz'; Case/orP: Hqz' => [Dz' | Hqz'].
  By Rewrite: (Iedge g (Iface g (eqP Dz'))) Hrz in Hrx.
Case: Eq; Case/splitPr: {q}Hqz' Uq Hq Hqy => [q1 q2].
Rewrite: -cat_adds uniq_cat mem_cat path_cat last_cat.
Move/and3P=> [Uq1 Uq12 Uq2]; Rewrite: /= {2}/eqdf; Move/and3P=> [Hq1 Eq1 Hq2].
Case/orP=> [Hq1y | Hq2y].
  Exists z'; LeftBy Rewrite: (fclosed1 diskN_node) /z' Eedge diskN_E /setU Hrz.
  Exists q2; LeftBy Auto.
  Apply/(hasPx ? (Adds z' q2))=> [[t Hq2t Hrt]]; Case/hasP: Uq12; Exists y; Auto.
  Step Hyt: (cface y t) By Apply: (connect_trans Hyz' (path_connect Hq2 ?)).
  By Rewrite: (scycle_cface HUr Hyt Hry Hrt).
Pose rclink := [t](face if (r t) then (edge t) else t).
Step [c [Hc [Uc Ec]] [Hr'c Hcq1]]:
 (EX c | (fpath rclink z' c) /\ ((uniq (Adds z' c)) /\ (last z' c) = z)
       & (sub_set (Adds y r') (Adds z' c)) 
       /\ (negb (has (Adds x' q1) (Adds z' c)))).
  Step Hr'r: (sub_set r' r).
    By Move=> t Ht; Rewrite: -(mem_rot i r) Dr; Apply: setU1r.
  Step HcF: (t : g; c : (seq g))
      (fpath face t c) -> (sub_set (Adds t c) (cface (last t c))).
    Move=> t c Hc t' Ht'; Apply: (connect_trans ? (path_connect Hc Ht')).
    By Rewrite Sface; Apply/connectP; Exists c.
  Step HcrF: (t : g; c : (seq g)) (uniq (Adds t c)) -> (r (last t c)) ->
      (fpath face t c) -> (fpath rclink t c).
    Step Hbase: (rel_base [t]t (eqdf rclink) (eqdf face) (setC r)).
      By Move=> t Ht t'; Rewrite: /eqdf /rclink (negbE Ht).
    Move=> t c Uc Hrc Hc; Rewrite: -(maps_id c) (path_maps Hbase) // maps_id.
    Rewrite: lastI uniq_add_last in Uc; Case/andP: Uc => [Uc _].
    Move=> t' Ht'; Apply/idP=> [Hrt']; Case/idP: Uc.
    Rewrite: [H](scycle_cface HUr H Hrc Hrt') //.
    By Apply: (HcF ? ? Hc); Rewrite: lastI mem_add_last /= setU1r.
  Def: Ur' := Ur; Rewrite: -(uniq_rot i) Dr /= in Ur'.
  Move/andP: Ur'=> [Hr'y Ur'].
  Cut (EX c2 | (fpath rclink y c2) /\ ((uniq c2) /\ (last y c2) = z)
       & (sub_set r' c2) /\ (sub_set (fband c2) (fband r'))).
    Move=> [c2 [Hc2 [Uc2 Ec2]] [Hr'c2 Hc2r']].
    Step Hc2y: (t : g) (c2 t) -> (negb (cface y t)).
      Move=> t Hc2t; Apply/idP=> [Hyt].
      Step Hr't: (has (cface t) r').
        By Apply: Hc2r'; Apply/hasP; Exists t; RightBy Apply connect0.
      Case: {Hr't}(hasP Hr't) => [t' Hr't' Htt']; Case (negP Hr'y).
      By Rewrite: (scycle_cface HUr (connect_trans Hyt Htt') Hry) ?Hr'r.
    Case/splitPl: {q2 Eq2}Hq2y Hq2 Uq12 Uq2 => [c1 q2' Ec1].
    Rewrite: path_cat -cat_adds has_cat uniq_cat.
    Move/andP=> [Hc1 _]; Move/norP=> [Hc1q1 _]; Move/andP=> [Uc1 _].
    Exists (cat c1 c2).
      Rewrite: path_cat last_cat Ec1 -cat_adds uniq_cat Uc1 Uc2 andbT.
      Rewrite: (HcrF ? ? Uc1) ?Ec1 //; Repeat Split; Auto.
      Apply/hasP=> [[t Hc2t Hc1t]]; Case/idP: (Hc2y ? Hc2t); Rewrite: -Ec1.
      Apply: HcF; Auto.
    Rewrite: -cat_adds has_cat (negbE Hc1q1); Split.
      Move=> t; Move/setU1P=> [[] | Ht].
        By Rewrite: -Ec1 mem_cat /setU mem_last.
      By Rewrite: mem_cat /setU (Hr'c2 ? Ht) orbT.
    Apply/hasP=> [[t Hc2t Hq1t]]; Case/idP: (Hc2y ? Hc2t).
    Apply: (connect_trans Hyz'); Rewrite: -(eqP Eq1) -cface1; Apply: HcF; Auto.
  Clear: i Dr z' Hzy Hrz Hyz' Uq12 Uq2 Eq2 Eq1 Hq2 Hq2y Hr'y; Rewrite: ~/z.
  Elim: r' y Hry Hr'r Hr' Ur' => [|y' r' Hrec] y Hry /=.
    By Do 3 Clear; Exists (Seq0 g); [Auto | Split; Move=> z].
  Move=> H; Move: {H}(H ? (setU11 ? ?)) [t;Ht](H t (setU1r ? Ht)) => Hry' Hr'r.
  Move/andP=> [Hyy' Hr']; Move/andP=> [Hr'y' Ur'].
  Case: {Hrec Hr' Ur'}(Hrec ? Hry' Hr'r Hr' Ur').
  Move=> c2 [Hc2 [Uc2 Ec2]] [Hr'c2 Hc2r'].
  Rewrite: /rlink cface1 in Hyy'; Case/connectP: Hyy'.
  Move=> c0; Case/shortenP=> [c1 Hc1 Uc1 _] {c0} Ec1.
  Def: Hc1F := (HcF ? ? Hc1); Rewrite: Ec1 in Hc1F.
  Exists (cat (Adds (face (edge y)) c1) c2).
    Split.
      Rewrite: path_cat /= Ec1 Hc2 andbT {1}/rclink {1}/eqdf Hry set11.
      By Apply: HcrF; Rewrite: ?Ec1.
    Split; RightBy Rewrite: last_cat /= Ec1.
    Rewrite: uniq_cat Uc1 Uc2 andbT.
    Apply/hasP=> [[t Hc1t Hc2t]]; Case/idP: Hr'y'.
    Step Hr't: (fband r' t).
      By Apply: Hc2r'; Apply/hasP; Exists t; RightBy Apply connect0.
    Case/hasP: Hr't => [t' Hr't' Htt'].
    Step Hy't': (cface y' t') By Apply: (connect_trans (Hc1F ? ?) Htt').
    By Rewrite (scycle_cface HUr Hy't' Hry' (Hr'r ? Hr't')).
  Split; Move=> t Ht.
    Case/setU1P: Ht => [[] | Ht].
      By Rewrite: -Ec1 mem_cat /setU mem_last.
    By Rewrite: mem_cat /setU (Hr'c2 ? Ht) orbT.
  Rewrite: /fband has_cat in Ht; Case/orP: Ht => [Hc1t | Hc2t].
    Case/hasP: Hc1t => [t' Hc1t' Htt'].
    Apply/hasP; Exists y'; LeftBy Apply: setU11.
    By Rewrite: (same_connect (Sface g) Htt') Sface Hc1F.
  Case: {Hc2t}(hasP (Hc2r' ? Hc2t)) => [t' Hr't' Htt'].
  By Apply/hasP; Exists t'; LeftBy Apply: setU1r.
Step [x1 Hnx1 [p [Hp Ep] Upc]] :
  (EX x1 | (Adds z' c (node x1)) &
    (EX p | (path (!clink?) x1 p) /\ (last x1 p) = x'
          & (negb (has (Adds z' c) (Adds x1 p))))).
  Case/hasP: HxN; Move=> x0 Hrx0; Case/connectP.
  Pose x0' := (finv node x0); Move=> p Hp.
  Step Hcc: (fcycle rclink (Adds z' c)).
    By Rewrite: (cycle_path x) /= Hc /eqdf /rclink Ec Hrz -/z' set11.
  Step Hpc: (has (Adds z' c) (Adds x0' p)).
    Step Hcx0: (Adds z' c x0) By Apply: Hr'c; Rewrite: -Dr mem_rot.
    Step [ ]: (rclink x0) = x0'.
      By Rewrite: /x0' -{2 x0}Eedge (finv_f (Inode g)) /rclink Hrx0.
    By Apply/orP; Left; Rewrite: (eqP (next_cycle Hcc Hcx0)) mem_next.
  Elim: p x0' Hp Hpc {x0 Hrx0} => [|x1 p Hrec] x0.
    Rewrite: /= orbF; Move=> _ Hcx Dx0.
    Exists x'; LeftBy Rewrite: /x' Eedge -Dx0.
    Exists (Seq0 g); LeftBy Split.
    Rewrite: /= orbF; Apply/idP=> [Hcx']; Case/hasP: Hcq1.
    By Exists x'; RightBy Apply: setU11.
  Rewrite: {-1 -3 -5 Adds}lock /= -lock; Move/andP=> [Hx01 Hp].
  Case Hcp: (has (Adds z' c) (Adds x1 p)); EAuto.
  Rewrite orbF; Move=> Hcx0 Ep; Move: {}Hcx0 Hx01 {Hrec}.
  Rewrite: /dlink -mem_next -(eqP (next_cycle Hcc Hcx0)) /rclink.
  Case (r x0); LeftDone.
  Move=> Hcfx0; Case/clinkP=> [Dx0 | Dx1];
    RightBy Rewrite: /= -Dx1 -mem_adds Hcfx0 in Hcp.
  Exists x1; LeftBy Rewrite: -Dx0.
  Exists (add_last p x').
    Split; RightBy Rewrite last_add_last.
    Rewrite: -cats1 path_cat /= Ep -{1 x}Eedge -/x' clinkN /= andbT.
    By Apply: (sub_path ? Hp)=> [t t']; Case/andP.
  Rewrite: -cats1 -cat_adds has_cat Hcp /= orbF.
  By Apply/idP=> [Hcx']; Case/hasP: Hcq1; Exists x'; RightBy Apply: setU11.
Step Hcc: (path clink z' c).
  Apply: (sub_path ? Hc) => [t t']; Case/eqP {t'}; Rewrite: /rclink.
  By Case (r t); [Rewrite: -{1 t}Eedge clinkN | Rewrite clinkF].
Step [c0 [Hc0 Ec0] Hc0c] :
  (EX c0 | (path clink x1 c0) /\ (clink (last x1 c0) z')
         & (negb (has (Adds z' c) (Adds x1 c0)))).
  Exists (cat p q1).
    Split; RightBy Rewrite: last_cat Ep -(eqP Eq1) clinkF.
    Rewrite: path_cat Hp Ep; Exact (sub_path (sub_relUr (?) 3!?) Hq1).
  Rewrite: -cat_adds has_cat (negbE Upc).
  By Rewrite has_sym in Hcq1; Case (norP Hcq1).
Case/shortenP: Hc0 Ec0 => [c1 Hc1 Uc1 Hc01] Ec1.
Case/and3P: (planarP g Hpg (Adds x1 (cat c1 (Adds z' c)))); Split.
    Rewrite: last_cat /= Ec mem2_cat mem2_adds (finv_eq_monic (Enode g)) -/z'.
    By Rewrite: set11 -mem_adds Hnx1 orbT.
  Rewrite: -cat_adds uniq_cat Uc1 Uc andbT andTb; Apply/hasP=> [[t Hct Hc1t]].
  Case/hasP: Hc0c; Exists t; Rewrite: //= /setU1.
  By Case: (orP Hc1t) => [Dt | Ht]; [Rewrite Dt | Rewrite: (Hc01 ? Ht) orbT].
By Rewrite: path_cat /= Hc1 Ec1.
Qed.

Local ddart : finSet := (subFin diskN).

Definition snipd_edge [x : g] : g :=
  if (r x) then (next r x) else (edge x).

Remark Hdedge : (u : ddart) (diskN (snipd_edge (subdE u))).
Proof.
Move=> [x HxN]; Rewrite: /= /snipd_edge diskN_E /setU.
Case Hrx: (r x); LeftBy Rewrite: mem_next Hrx.
By Rewrite: orbC -(fclosed1 diskE_edge) /diskE /setD HxN Hrx.
Qed.

Definition snipd_face [x : g] : g :=
  if (r x) then (face (edge (prev r x))) else (face x).

Remark Hdface : (u : ddart) (diskN (snipd_face (subdE u))).
Proof.
Move=> [x HxN]; Rewrite: /= /snipd_face (fclosed1 diskN_node) diskN_E /setU.
Case Hrx: (r x); LeftBy Rewrite: Eedge mem_prev Hrx.
By Rewrite: orbC (fclosed1 diskE_edge) Eface /diskE /setD Hrx HxN.
Qed.

Remark Hdnode : (u : ddart) (diskN (node (subdE u))).
Proof. By Move=> [x HxN]; Rewrite: /= -(diskN_node 1!x (set11 ?)). Qed.

Local dedge [u : ddart] : ddart := (subdI (Hdedge u)).
Local dnode [u : ddart] : ddart := (subdI (Hdnode u)).
Local dface [u : ddart] : ddart := (subdI (Hdface u)).

Remark snipd_monic : (monic3 dedge dnode dface).
Proof.
Hnf; Move=> [x Hx]; Apply: (subdE_inj ?); Rewrite: /= /snipd_edge.
Case Hrx: (r x); Rewrite: /snipd_face.
  By Rewrite: mem_next Hrx Eedge (prev_next Ur).
Step HxE: (diskE (edge x)) By Rewrite: -(fclosed1 diskE_edge) /diskE /setD Hrx.
By Case/andP: HxE => [Hrex _]; Rewrite: (negbE Hrex) Eedge.
Qed.

Definition snip_disk : hypermap := (Hypermap snipd_monic).
Definition snipd [u : snip_disk] : g := (subdE u).

Lemma inj_snipd : (injective snipd). Proof. Exact (subdE_inj 2!?). Qed.

Lemma codom_snipd : (codom snipd) =1 diskN.
Proof.
Move=> z; Apply/set0Pn/idP=> [[[y Hy] Dy] | Hz]; LeftBy Rewrite: (eqP Dy).
Exists ((subdI Hz)::snip_disk); Exact (set11 ?).
Qed.

Definition snipd_ring : (seq snip_disk) := (preimage_seq snipd r).

Lemma maps_snipd_ring : (maps snipd snipd_ring) = r.
Proof.
By Apply: maps_preimage => [x Hx]; Rewrite: codom_snipd diskN_E /setU Hx.
Qed.

Lemma ucycle_snipd_ring : (ufcycle (!edge?) snipd_ring).
Proof.
Step Ubgd : (uniq snipd_ring).
  By Rewrite: -(uniq_maps inj_snipd) maps_snipd_ring Ur.
Rewrite: /ucycle Ubgd andbT.
Apply: (cycle_from_next Ubgd) => [x Hx]; Apply/eqP; Apply: inj_snipd.
Rewrite: /= /snipd_edge -/(snipd x) -maps_snipd_ring (mem_maps inj_snipd) Hx.
Apply (next_maps inj_snipd Ubgd).
Qed.

Lemma cface_snipd : (u, v : snip_disk)
  (cface (snipd u) (snipd v)) = (cface u v).
Proof.
Step HdgF: (u, v : snip_disk) (cface u v) -> (cface (snipd u) (snipd v)).
  Move=> u v; Move/connectP=> [p Hp []] {v}.
  Elim: p u Hp => [|u p Hrec] [x Hx] /=; LeftBy Rewrite: connect0.
  Move/andP=> [Hux Hp]; Apply: (connect_trans ? (Hrec ? Hp)) {Hrec Hp}.
  Rewrite: -~{u Hux}(? =P u Hux) /= /snipd_face.
  Case Hrx: (r x); RightBy Rewrite fconnect1.
  Rewrite: Sface -cface1; Exact (prev_cycle Hr Hrx).
Step HgdFr: (u, v : snip_disk) (fband snipd_ring u) = false ->
   (cface (snipd u) (snipd v)) -> (cface u v).
  Move=> [x Hx] /= v Hxr; Move/connectP=> [p Hp Ep].
  Elim: p x Hx Hxr Hp Ep => [|y p Hrec] x Hx Hxr /=.
    By Move=> _ Dx; Apply: eq_connect0; Apply: inj_snipd.
  Move/andP=> [Dy Hp] Ep.
  Case Hrx: (r x).
    Case/hasP: Hxr; Exists (subdI 1!g Hx); RightBy Apply connect0.
    By Rewrite: -(mem_maps inj_snipd) maps_snipd_ring /=.
  Step Hy: (diskN y).
    Rewrite: (fclosed1 diskN_node) diskN_E /setU (fclosed1 diskE_edge).
    By Rewrite: -(eqP Dy) Eface orbC /diskE /setD Hrx Hx.
  Apply: (connect_trans ? (Hrec ? Hy ? Hp Ep)) {Hrec Hp Ep}.
    By Apply connect1; Rewrite: /eqdf /eqd /= /snipd_face Hrx.
  Apply/hasP=> [[u Hu Hyu]]; Case/hasP: Hxr; Exists u; LeftDone.
  Apply: (connect_trans ? Hyu).
  By Apply connect1; Rewrite: /eqdf /eqd /= /snipd_face Hrx.
Move=> u v; Apply/idP/idP; Auto; Case Hur: (fband snipd_ring u); Auto.
Rewrite: (Sface snip_disk) Sface; Case Hvr: (fband snipd_ring v); Auto.
Case: (hasP Hur) (hasP Hvr) => [u' Hu' Huu'] [v' Hv' Hvv'] Hvu.
Step Hv'u': (cface (snipd v') (snipd u')).
  Apply: (connect_trans (connect_trans ? Hvu) (HdgF ? ? Huu')).
  By Rewrite Sface; Auto.
Rewrite Sface in Huu'; Apply: (connect_trans Hvv' (connect_trans ? Huu')).
By Apply: (eq_connect0 ? (inj_snipd (scycle_cface HUr Hv'u' ? ?)));
  Rewrite: -maps_snipd_ring (mem_maps inj_snipd).
Qed.

Lemma simple_snipd_ring : (simple snipd_ring).
Proof.
Step Hdr: (u : snip_disk) (snipd_ring u) -> (r (snipd u)).
  By Move=> u Hu; Rewrite: -maps_snipd_ring (mem_maps inj_snipd).
Move: {}Ur; Rewrite: -maps_snipd_ring (uniq_maps inj_snipd) /simple.
Elim: {}snipd_ring Hdr => [|u p Hrec] //=.
Move=> H; Move: {H}(H ? (setU11 ? ?)) [v; Hv](H v (setU1r ? Hv)) => Hru Hpr.
Move/andP=> [Hpu Up]; Apply/andP; Split; RightBy Auto.
Apply/mapsP=> [[v Hv Hvu]]; Case/idP: Hpu.
Rewrite: -[H](inj_snipd (scycle_cface HUr H (Hpr ? Hv) Hru)) // cface_snipd.
By Apply/(rootP (Sface ?)).
Qed.

Lemma scycle_snipd_ring : (sfcycle edge snipd_ring).
Proof.
By Rewrite: /scycle simple_snipd_ring andbT; Case (andP ucycle_snipd_ring).
Qed.

Local rdart : finSet := (subFin (setC diskE)).

Remark redgeP : (u : rdart) (setC diskE (edge (subdE u))).
Proof. Move=> [z Hz]; By Rewrite: /setC /= -(diskE_edge 1!z (set11?)). Qed.

Definition snipr_node [z : g] : g :=
  if (r z) then (prev r z) else (node z).

Remark rnodeP : (u : rdart) (setC diskE (snipr_node (subdE u))).
Proof.
Move=> [z Hz]; Rewrite: /snipr_node /setC /=.
Case Hrz: (r z); LeftBy Rewrite: /diskE /setD mem_prev Hrz.
Apply/idP=> [Hnz]; Case/idP: Hz; Rewrite: /diskE /setD Hrz /=.
By Rewrite: (fclosed1 diskN_node) diskN_E /setU Hnz orbT.
Qed.

Definition snipr_face [z : g] : g :=
  if (r (node (face z))) then (next r (node (face z))) else (face z).

Remark rfaceP : (u : rdart) (setC diskE (snipr_face (subdE u))).
Proof.
Move=> [z Hz]; Rewrite: /snipr_face /setC /=.
Case Hrnfz: (r (node (face z))); LeftBy Rewrite: /diskE /setD mem_next Hrnfz.
Rewrite: /diskE /setD andbC (fclosed1 diskN_node) diskN_E /setU Hrnfz /=.
By Rewrite: (fclosed1 diskE_edge) Eface (negbE Hz).
Qed.

Local redge [u : rdart] : rdart := (subdI (redgeP u)).
Local rnode [u : rdart] : rdart := (subdI (rnodeP u)).
Local rface [u : rdart] : rdart := (subdI (rfaceP u)).

Remark snipr_monic : (monic3 redge rnode rface).
Proof.
Move=> [z Hz]; Apply: subdE_inj; Rewrite: /= /snipr_node /snipr_face Eedge.
Case Hrz: (r z); LeftBy Rewrite: mem_next Hrz (prev_next Ur).
Rewrite: /setC /diskE /setD Hrz /= -{1 z}Eedge -(fclosed1 diskN_node) in Hz.
By Rewrite: diskN_E in Hz; Case/norP: Hz => [Hz _]; Rewrite: (negbE Hz) Eedge.
Qed.

Definition snip_rem : hypermap := (Hypermap snipr_monic).
Definition snipr [u : snip_rem] : g := (subdE u).
Lemma inj_snipr : (injective snipr). Proof. Exact (subdE_inj 2!?). Qed.
Lemma codom_snipr : (codom snipr) =1 (setC diskE).
Proof.
Move=> z; Apply/set0Pn/idP=> [[[y Hy] Dy] | Hz]; LeftBy Rewrite (eqP Dy).
Exists ((subdI Hz)::snip_rem); Exact (set11 ?).
Qed.

Definition snipr_ring : (seq snip_rem) := (preimage_seq snipr (rev r)).

Lemma maps_snipr_ring : (maps snipr snipr_ring) = (rev r).
Proof.
Apply: maps_preimage => [x Hx]; Rewrite: mem_rev in Hx.
By Rewrite: codom_snipr /diskE /setC /setD Hx.
Qed.

Lemma ucycle_snipr_ring : (ufcycle (!node?) snipr_ring).
Proof.
Step Ubgr : (uniq snipr_ring).
  By Rewrite: -(uniq_maps inj_snipr) maps_snipr_ring uniq_rev Ur.
Rewrite: /ucycle Ubgr andbT.
Apply: (cycle_from_next Ubgr) => [x Hx]; Apply/eqP; Apply: inj_snipr.
Rewrite: -(mem_maps inj_snipr) maps_snipr_ring mem_rev in Hx.
Rewrite: /= /snipr_node -/(snipr x) Hx -(next_maps inj_snipr Ubgr).
By Rewrite: maps_snipr_ring (next_rev Ur).
Qed.

Lemma snip_patch : (patch snipd snipr snipd_ring snipr_ring).
Proof.
Split. Exact inj_snipd. Exact inj_snipr.
Exact scycle_snipd_ring. Exact ucycle_snipr_ring.
Rewrite: maps_snipd_ring; Exact maps_snipr_ring.
Move=> x; Rewrite: /setU /setC maps_snipd_ring codom_snipd codom_snipr.
  By Rewrite: /setC /diskE /setD negb_andb negb_elim orbC.
Move=> [x Hx]; Rewrite: /setC -(mem_maps inj_snipd) maps_snipd_ring /=.
  By Move/negPf=> Hxb; Rewrite: /snipd_edge Hxb.
By Case.
By Case.
Move=> [x Hx]; Rewrite: /setC -(mem_maps inj_snipr) maps_snipr_ring mem_rev /=.
  By Move/negPf=> Hxb; Rewrite: /snipr_node Hxb.
Qed.

Lemma planar_snipd : (planar snip_disk).
Proof. By Move: {}Hpg; Rewrite (planar_patch snip_patch); Case/andP. Qed.

Lemma planar_snipr : (planar snip_rem).
Proof. By Move: {}Hpg; Rewrite (planar_patch snip_patch); Case/andP. Qed.

End Snip.

Section SnipRot.

(* Disks only depend on the extent of their ring; hence, they are invariant *)
(* under rotation.                                                          *)

Variables n0 : nat; g : hypermap; r : (seq g).

Lemma diskN_rot : (diskN (rot n0 r)) =1 (diskN r).
Proof.
Move=> x; Apply: (etrans (has_rot ? ? ?) (eq_has ? ?)) => [y].
By Apply: eq_connect {x y} => [x y]; Rewrite: /dlink mem_rot.
Qed.

Lemma diskE_rot : (diskE (rot n0 r)) =1 (diskE r).
Proof. By Move=> x; Rewrite: /diskE /setD mem_rot diskN_rot. Qed.

Lemma diskF_rot : (diskF (rot n0 r)) =1 (diskF r).
Proof. By Move=> x; Rewrite: /diskF /setD fband_rot diskN_rot. Qed.

Lemma diskFC_rot : (diskFC (rot n0 r)) =1 (diskFC r).
Proof. By Move=> x; Rewrite: /diskFC /setD /setC fband_rot diskN_rot. Qed.

End SnipRot.

Unset Implicit Arguments.

