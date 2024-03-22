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
Require color.
Require geometry.
Require patch.

Set Implicit Arguments.

Section Sew.

Variables gd, gr : hypermap; bgd : (seq gd); bgr : (seq gr).

Hypothesis Hbgd : (sfcycle edge bgd).
Hypothesis Hbgr : (ufcycle node bgr).
Hypothesis Hrs : (size bgd) = (size bgr).

Lemma HbgdE : (xd : gd) (bgd xd) -> (cedge xd) =1 bgd.
Proof. By Move=> *; Apply fconnect_cycle; Case (andP Hbgd). Qed.

Lemma HbgdE1 : (xd : gd) (bgd (edge xd)) -> (bgd xd).
Proof. By Move=> xd Hxd; Rewrite: -(HbgdE Hxd) Sedge fconnect1. Qed.

Lemma HbgrN : (xr : gr) (bgr xr) -> (cnode xr) =1 bgr.
Proof. By Move=> *; Apply fconnect_cycle; Case (andP Hbgr). Qed.

Lemma HbgrN1 : (xr : gr) (bgr (node xr)) -> (bgr xr).
Proof. By Move=> xr Hxr; Rewrite: -(HbgrN Hxr) Snode fconnect1. Qed.

Remark in_bgd : (xd : gd) {xr0 : gr | (bgd xd)} + {(setC bgd xd)}.
Proof.
Move=> xd; Rewrite: /setC; Case Hxd: (bgd xd); [Left | By Right].
By Case: {}bgr Hxd Hrs => [|xr0 pr]; [Case bgd | Exists xr0].
Qed.
 
Remark in_bgr : (xr : gr) {xd0 : gd | (bgr xr)} + {(setC bgr xr)}.
Proof.
Move=> xr; Rewrite: /setC; Case Hxr: (bgr xr); [Left | By Right].
By Case: {}bgd Hxr Hrs => [|xd0 pd]; [Case bgr | Exists xd0].
Qed.

Local hdr [xr0 : gr; xd : gd] : gr := (sub xr0 (rev bgr) (index xd bgd)).

Local hrd [xd0 : gd; xr : gr] : gd := (sub xd0 bgd (index xr (rev bgr))).

Remark bgr_hdr : (xd : gd; Hxd : (bgd xd); xr0 : gr) (bgr (hdr xr0 xd)).
Proof.
By Move=> *; Rewrite: /hdr -mem_rev mem_sub // size_rev -Hrs index_mem.
Qed.

Remark bgd_hrd : (xr : gr; Hxr : (bgr xr); xd0 : gd) (bgd (hrd xd0 xr)).
Proof.
By Move=> *; Rewrite: /hrd mem_sub // Hrs -size_rev index_mem mem_rev.
Qed.

Remark hrd_hdr : (xd : gd; Hxd : (bgd xd); xd0 : gd; xr0 : gr)
  (hrd xd0 (hdr xr0 xd)) = xd.
Proof.
Move=> xd Hxd xd0 xr0; Rewrite: /hrd /hdr index_uniq ?sub_index //.
  By Rewrite: size_rev -Hrs index_mem.
By Rewrite: uniq_rev; Case: (andP Hbgr).
Qed.

Remark hdr_hrd : (xr : gr; Hxr : (bgr xr); xd0 : gd; xr0 : gr)
  (hdr xr0 (hrd xd0 xr)) = xr.
Proof.
Move=> xr Hxr xd0 xr0; Rewrite: /hrd /hdr index_uniq ?sub_index ?mem_rev //.
  By Rewrite: Hrs -size_rev index_mem mem_rev.
By Apply simple_uniq; Case: (andP Hbgd).
Qed.

Remark node_hdr : (xd : gd; Hxd : (bgd xd); xr0 : gr)
  (node (hdr xr0 xd)) = (hdr xr0 (node (face xd))).
Proof.
Case: (andP Hbgd) (andP Hbgr) => [HdE Ud] [HrN Ur] xd Hxd xr0.
Move/simple_uniq: Ud => Ud; Pose xr := (hdr xr0 xd).
Step Hxr : (bgr xr) By Rewrite: /xr bgr_hdr.
Rewrite: -(eqP (prev_cycle HdE Hxd)) Eedge (eqP (next_cycle HrN Hxr)).
Rewrite: -(rev_rev bgr) next_rev ?uniq_rev // !prev_sub Hxd mem_rev Hxr.
Case Dbgr: {1}(rev bgr) => [|xr1 bgr']; LeftBy Rewrite: -mem_rev Dbgr in Hxr.
Rewrite: /xr {1}/hdr.
Case Dbgd: {1 2}bgd => [|xd1 bgd']; LeftBy Rewrite: Dbgd in Hxd.
Simpl; Pose i := (index xd bgd'); Step Hi: (ltn i (size bgd)).
  By Rewrite: Dbgd /= ltnS /i index_size.
Rewrite: /hdr index_uniq //; Rewrite: Hrs -size_rev in Hi.
Apply: (etrans (congr (sub ? ?) ?) (set_sub_default ? ? Hi)).
Rewrite: -uniq_rev Dbgr /= in Ur; Case/andP: Ur => [Hxr1' Ur'].
Rewrite: Dbgd /= in Ud; Case/andP: Ud => [Hxd1' _].
Def: Hrs' := Hrs; Rewrite: Dbgd -(size_rev bgr) Dbgr /= in Hrs'.
Injection: Hrs' => Hrs'.
Rewrite: Dbgd /= /setU1 eqd_sym in Hxd; Case Hxd1: (xd =d xd1) Hxd.
  Rewrite: Dbgr /= /i -(cats0 bgr') -(cats0 bgd') !index_cat /= !addn0.
  By Clear; Rewrite: (eqP Hxd1) (negbE Hxr1') (negbE Hxd1').
By Rewrite: Dbgr /= -index_mem; Move=> *; Rewrite: index_uniq // -Hrs'.
Qed.

Remark edge_hrd : (xr : gr; Hxr : (bgr xr); xd0 : gd)
  (edge (hrd xd0 xr)) = (hrd xd0 (face (edge xr))).
Proof.
Move=> xr Hxr xd0; Pose yr := (face (edge xr)).
Step Hyr: (bgr yr) By Apply HbgrN1; Rewrite: /yr Eedge.
Rewrite: -{1 xr}Eedge -/yr -{1 yr}(hdr_hrd Hyr xd0 xr).
Pose yd := (hrd xd0 yr); Step Hyd: (bgd yd) By Rewrite: /yd bgd_hrd.
By Rewrite: node_hdr // hrd_hdr ?Eface // HbgdE1 ?Eface.
Qed.

Inductive sew_tag : Set := SewDisk : sew_tag | SewRest : sew_tag.

Definition sew_tag_eq [pt1, pt2] : bool :=
  Cases pt1 pt2 of
    SewDisk SewDisk => true
  | SewRest SewRest => true
  | _ _ => false
  end.

Definition sew_tag_data : dataSet.
Apply (DataSet 2!sew_tag_eq); Abstract By Do 2 Case; Constructor.
Defined.
Canonical Structure sew_tag_data.

Definition sew_tag_set : finSet.
Apply (FinSet 2!(Seq SewDisk SewRest)); Abstract By Case.
Defined.
Canonical Structure sew_tag_set.
Syntactic Definition ptag := sew_tag_set.

Local sew_sub_map [i : ptag] : finSet :=
  Cases i of SewDisk => gd | SewRest => (subFin (setC bgr)) end.

Definition sew_dart : finSet := (sumFin sew_sub_map).

Definition sewd [xd : gd] : sew_dart := (!sumdI ? sew_sub_map SewDisk xd).

Definition sewr_r [xr : gr; Hxr : (setC bgr xr)] : sew_dart :=
  (!sumdI ? sew_sub_map SewRest (subdI Hxr)).

Definition sewr [xr : gr] : sew_dart :=
  if (in_bgr xr) then [u]let (xd0, _) = u in (sewd (hrd xd0 xr))
  else (!sewr_r?).

Lemma inj_sewd : (injective sewd).
Proof.
Move=> xd yd; Move/(introT eqP); Rewrite: /sewd /= sumd_eqdr; Exact (xd =P yd).
Qed.

Lemma inj_sewr : (injective sewr).
Proof.
Move=> xr yr; Move/(introT eqP); Rewrite: /sewr.
Case: (in_bgr xr) (in_bgr yr) => [[xd0 Hxr] | Hxr] [[xd1 Hyr] | Hyr] //=.
  By Move=> Hxy; Rewrite: -(hdr_hrd Hxr xd0 xr) (inj_sewd (eqP Hxy)) hdr_hrd.
Rewrite: /sewr_r sumd_eqdr /eqd /=; Exact (xr =P yr).
Qed.

Remark sewr_bgr : (xd0 : gd; xr : gr; Hxr : (bgr xr))
  (sewr xr) = (sewd (hrd xd0 xr)).
Proof.
Move=> xd0 xr Hxr; Rewrite: /sewr; Case: (in_bgr xr) => [[xd1 _] | Hxr'].
  By Rewrite: -{1 xr}(hdr_hrd Hxr xd0 xr) hrd_hdr ?bgd_hrd.
By Case/idP: Hxr'.
Qed.

Remark sewr_gr : (xr : gr; Hxr : (setC bgr xr)) (sewr xr) = (sewr_r Hxr).
Proof.
Move=> xr Hxr; Rewrite: /sewr.
Case: (in_bgr xr) => [[xd0 Hxr'] | Hxr']; LeftBy Rewrite (negbE Hxr) in Hxr'.
By Rewrite (bool_eqT Hxr Hxr').
Qed.

Remark sewr_hdr : (xd : gd; Hxd : (bgd xd); xr0 : gr)
  (sewr (hdr xr0 xd)) = (sewd xd).
Proof. By Move=> xd Hxd xr0; Rewrite: (sewr_bgr xd) ?hrd_hdr ?bgr_hdr. Qed.

Definition sew_edge [w : sew_dart] : sew_dart :=
  Cases w of
    (sumdI SewDisk xd) =>
      if (in_bgd xd) is (inleft (exist xr _)) then (sewr (edge (hdr xr xd)))
      else (sewd (edge xd))
  | (sumdI SewRest ur) =>
      let (xr, _) = ur in (sewr (edge xr))
  end.

Definition sew_face_r [xr : gr] : sew_dart :=
  let ufr = (sewr (face xr)) in
  if ufr is (sumdI SewDisk xd) then (sewd (face xd)) else ufr.

Definition sew_face [w : sew_dart] : sew_dart :=
  Cases w of
    (sumdI SewDisk xd) =>
      if (in_bgd xd) is (inleft (exist xr _)) then (sew_face_r (hdr xr xd))
      else (sewd (face xd))
  | (sumdI SewRest ur) =>
      let (xr, _) = ur in (sew_face_r xr)
  end.

Definition sew_node [w : sew_dart] : sew_dart :=
  Cases w of
    (sumdI SewDisk xd) => (sewd (node xd))
  | (sumdI SewRest ur) => let (xr, _) = ur in (sewr (node xr))
  end.

Lemma Esew_map : (monic3 sew_edge sew_node sew_face).
Proof.
Move=> [[|] xd]; [Simpl | Case: xd => [xr Hxr] /=].
  Case: (in_bgd xd) => [[xr0 Hxd] | Hxd] /=.
    Pose exr := (edge (hdr xr0 xd)); Transitivity (sew_node (sew_face_r exr)).
      Rewrite: /sewr; Case: (in_bgr exr) => [[xd0 Hexr] | Hexr] //=.
      Case: (in_bgd (hrd xd0 exr)); RightBy Rewrite: /setC bgd_hrd.
      By Move=> [xr1 _]; Rewrite: /= hdr_hrd.
    Rewrite: /= /sew_face_r (sewr_bgr xd) /=.
      By Rewrite: /exr -edge_hrd ?bgr_hdr // Eedge (hrd_hdr Hxd).
    By Apply HbgrN1; Rewrite: /exr Eedge bgr_hdr.
  Case: (in_bgd (edge xd)) => [[xr0 Hexd] | Hexd]; Rewrite: /= ?Eedge //.
  By Case (negP Hxd); Apply HbgdE1.
Transitivity (sew_node (sew_face_r (edge xr))).
  Rewrite: /sewr; Case: (in_bgr (edge xr)) => [[xd0 Hexr] | Hexr] //=.
  Case: (in_bgd (hrd xd0 (edge xr))) => [[xr0 Hexd] | Hexd] /=.
    By Rewrite hdr_hrd.
  By Rewrite: /setC bgd_hrd in Hexd.
Step Hfexr: (setC bgr (face (edge xr))).
  Apply/idP=> [Hfexr]; Case/idP: Hxr.
  By Rewrite: -{1 xr}Eedge -(HbgrN Hfexr) fconnect1.
By Rewrite: /sew_face_r (sewr_gr Hfexr) /= Eedge (sewr_gr Hxr).
Qed.

Definition sew_map : hypermap := (Hypermap Esew_map).

Lemma sewr_rev_sewd : (maps sewr bgr) = (rev (maps sewd bgd)).
Proof.
Apply: (etrans (esym (rev_rev ?)) (congr rev ?)); Rewrite: -maps_rev.
Case: (andP Hbgd) {}sewr_hdr {}Hrs => [_ Ud]; Rewrite: /hdr -(size_rev bgr).
Elim: {}bgd (rev bgr) {Ud}(simple_uniq Ud) => [|xd pd Hrec] [|xr pr] //=.
Move/andP=> [Hpxd Upd] Edr; Rewrite: -(Edr ? (setU11 ? ?) xr) set11 /=.
Injection=> Hsz; Congr Adds; Apply: Hrec {Hrec} => // [yd Hyd yr0].
Rewrite: -(Edr ? (setU1r ? Hyd) yr0).
By Case: (yd =P xd) Hpxd => [[]|_]; Rewrite: ?Hyd.
Qed.

Lemma sew_map_patch : (patch 1!sew_map sewd sewr bgd bgr).
Proof.
Split; Try Done. Exact inj_sewd. Exact inj_sewr. Exact sewr_rev_sewd.
Move=> x; Case: {2}x (erefl x) => [[|] xd]; [Move=> Dx | Case: xd => [xr Hxr] Dx].
    Change x = (sewd xd) in Dx.
    Rewrite: /setU /setC Dx codom_f (mem_maps inj_sewd) /=.
    Case: (in_bgd xd) => [[xr0 Hxd] | Hxd].
      Rewrite Hxd; Apply/set0Pn; Exists (hdr xr0 xd).
      By Rewrite: /preimage (sewr_hdr Hxd) set11.
    Rewrite: (negbE Hxd); Apply/set0Pn=> [[xr H]]; Case/idP: Hxd; Move: H.
    Rewrite: /preimage /sewr; Case: (in_bgr xr) => [[xd0 Hxr] | Hxr]; RightDone.
    By Rewrite: (inj_eqd inj_sewd); Move/eqP=> Dxd; Rewrite: Dxd bgd_hrd.
  Change x = (sewr_r Hxr) in Dx.
  Rewrite: Dx /setU /setC {2}/codom /set0b eq_card0 //=.
  By Apply/set0Pn; Exists xr; Rewrite: /preimage (sewr_gr Hxr) set11.
By Move=> xd Hxd /=; Case: (in_bgd xd) => // [[xr0 Hxd']]; Case/idP: Hxd.
Move=> xr; Rewrite: {2}/sewr; Case: (in_bgr xr) => [[xd0 Hxr] | Hxr] //=.
  Case: (in_bgd (hrd xd0 xr)) => [[xr0 _] | Hxd']; LeftBy Rewrite: hdr_hrd.
  By Case (negP Hxd'); Rewrite bgd_hrd.
By Move=> xr Hxr; Rewrite: (sewr_gr Hxr).
Qed.

End Sew.

Unset Implicit Arguments.
