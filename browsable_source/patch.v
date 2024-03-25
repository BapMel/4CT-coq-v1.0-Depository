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
Require geometry.
Require jordan.
Require color.
Require coloring.

Set Implicit Arguments.

Section Patch.

(* Patching two maps to cover a larger one. The relations established here *)
(* are used in both directions: with sew, to deduce the properties of the  *)
(* new map created by glueing, and in snip, to deduce the properties of    *)
(* the two maps created by cutting along an rlink cycle.                   *)
(* It is important to note that the relations between the two parts is     *)
(* not quite symmetrical: the border of the inside ("disk") map is an edge *)
(* cycle, while the border of the outer ("remainder") part is a node orbit *)
(* The disk border must be simple, but only in the "disk" map; the         *)
(* corresponding sequence in the main and remainder maps needs not be.     *)
(* At the end of this file is the first application of patching: we prove  *)
(* that a minimal counter example must be connected.                       *)

Variables g, gd, gr : hypermap; hd : gd -> g; hr : gr -> g.
Variables bgd : (seq gd); bgr : (seq gr).

Record patch : Prop :=
  Patch {
    patch_injd : (injective hd);
    patch_injr : (injective hr);
    patch_cycle_d : (sfcycle edge bgd);
    patch_cycle_r : (ufcycle node bgr);
    patch_maps_ring_r : (maps hr bgr) = (rev (maps hd bgd));
    patch_codom_r : (codom hr) =1 (setU (setC (codom hd)) (maps hd bgd));
    patch_edge_d : (xd : gd) (setC bgd xd) -> (hd (edge xd)) = (edge (hd xd));
    patch_node_d : (xd : gd) (hd (node xd)) = (node (hd xd));
    patch_edge_r : (xr : gr) (hr (edge xr)) = (edge (hr xr));
    patch_node_r : (xr : gr) (setC bgr xr) -> (hr (node xr)) = (node (hr xr))
  }.

Hypothesis Hgh : patch.

Local Ihd := (patch_injd Hgh).
Local Ihr := (patch_injr Hgh).
Local Hbgd := (patch_cycle_d Hgh).
Local Hbgr := (patch_cycle_r Hgh).
Local bg : (seq g) := (maps hd bgd).
Local Dbgr : (maps hr bgr) = (rev bg) := (patch_maps_ring_r Hgh).
Local Ehr := (patch_codom_r Hgh).
Remark Ebgr : (maps hr bgr) =1 bg. Proof. Rewrite Dbgr; Apply mem_rev. Qed.
Remark Ehd : (codom hd) =1 (setU (setC (codom hr)) bg).
Proof.
Move=> x; Rewrite: /setU /setC Ehr /setU /setC negb_orb negb_elim andbC orbC.
By Case Hx: (bg x); LeftBy (Case/mapsP: Hx => [xd _ []]; Rewrite codom_f).
Qed.
Local EdE := (patch_edge_d Hgh).
Local EdN := (patch_node_d Hgh).
Local ErE := (patch_edge_r Hgh).
Local ErN := (patch_node_r Hgh).

Remark Ubgd : (uniq bgd). Proof. By Case (andP (scycle_ucycle Hbgd)). Qed.
Remark Ubgr : (uniq bgr). Proof. By Case (andP Hbgr). Qed.
Remark Ubg : (uniq bg). Proof. By Rewrite: /bg (uniq_maps Ihd) Ubgd. Qed.

Remark Ebgdr: (xd : gd) (codom hr (hd xd)) = (bgd xd).
Proof. By Move=> *; Rewrite: Ehr /setU /setC codom_f /bg (mem_maps Ihd). Qed.

Remark EbgdE: (xd : gd) (bgd xd) -> (cedge xd) =1 bgd.
Proof. By Refine (fconnect_cycle ?); Case (andP Hbgd). Qed.

Remark Ebgrd: (xr : gr) (codom hd (hr xr)) = (bgr xr).
Proof. By Move=> *; Rewrite: Ehd /setU /setC codom_f -Ebgr (mem_maps Ihr). Qed.

Remark EbgrN: (xr : gr) (bgr xr) -> (cnode xr) =1 bgr.
Proof. By Apply: fconnect_cycle; Case (andP Hbgr). Qed.

Remark EhdUr : (setU (codom hd) (codom hr)) =1 g.
Proof. By Move=> x; Rewrite: /setU Ehr /setU /setC; Case (codom hd x). Qed.

Remark EhdIr : (setI (codom hd) (codom hr)) =1 bg.
Proof.
Move=> x; Rewrite: /setI Ehr /setU /setC; Case Hx: (codom hd x); Auto.
By Symmetry; Apply/mapsP=> [[xd _ Dx]]; Rewrite: -Dx codom_f in Hx.
Qed.

Lemma card_patch : (addn (card gd) (card gr)) = (addn (size bg) (card g)).
Proof.
Rewrite: -(card_codom Ihd) -(card_codom Ihr) -cardUI (eq_card EhdUr) addnC.
By Rewrite: (eq_card EhdIr) (card_uniqP Ubg).
Qed.

Remark HbgdE : (fclosed edge bgd).
Proof.
Apply: (intro_closed (Sedge ?)) => [xd yd Dyd Hxd]; Move.
Case/andP: Hbgd => [H _]; Rewrite: -{H}(fconnect_cycle H Hxd).
Exact (connect1 Dyd).
Qed.

Remark HbgrN : (fclosed node bgr).
Proof.
Apply: (intro_closed (Snode ?)) => [xr yr Dyr Hxr]; Move.
Case/andP: Hbgr => [H _]; Rewrite: -{H}(fconnect_cycle H Hxr).
Exact (connect1 Dyr).
Qed.

Remark EdErN : (xd : gd; xr : gr)
  ((hd (edge xd)) =d (hr xr)) = ((hd xd) =d (hr (node xr))).
Proof.
Move=> xd xr; Case Hxd: (bgd xd).
  Case/andP: Hbgd => [CdE _]; Case/andP: Hbgr => [CrN _].
  Rewrite: (eqP (next_cycle CdE Hxd)) -(next_maps Ihd Ubgd) -/bg.
  Rewrite: (monic2F_eqd (prev_next Ubg)) -(next_rev Ubg) -Dbgr.
  Rewrite: (next_maps Ihr Ubgr).
  Case Hxr: (bgr xr); LeftBy Rewrite: -(eqP (next_cycle CrN Hxr)).
  Step Hxdr: (maps hr bgr (hd xd)) By Rewrite: Ebgr /bg (mem_maps Ihd).
  Apply/eqP/eqP => [Exr].
    By Rewrite: Exr (mem_maps Ihr) mem_next Hxr in Hxdr.
  By Rewrite: Exr (mem_maps Ihr) -(HbgrN 1!xr (set11?)) Hxr in Hxdr.
Apply/eqP/eqP => [Exd].
  Move: (EhdIr (hr xr)); Rewrite: /setI codom_f -Exd codom_f.
  By Rewrite: /bg (mem_maps Ihd) -(HbgdE 1!xd (set11?)) Hxd.
Move: (EhdIr (hr (node xr))); Rewrite: /setI codom_f -Exd codom_f.
By Rewrite: /bg (mem_maps Ihd) Hxd.
Qed.

Remark HbgdP : (xd : gd) (bgd xd) ->
  (EX xr | (hd (edge xd)) = (hr xr) & (hd xd) = (hr (node xr))).
Proof.
Move=> xd Hxd; Step Hxr: (codom hr (hd xd)).
  By Rewrite: Ehr /setU /bg (mem_maps Ihd) Hxd orbT.
Case/set0Pn: Hxr => [xr Dxr]; Rewrite: /preimage -(Eedge ? xr) in Dxr.
By Exists (face (edge xr)); Apply: eqP; LeftBy Rewrite EdErN.
Qed.

Remark HbgrP : (xr : gr) (bgr xr) ->
  (EX xd | (hd (edge xd)) = (hr xr) & (hd xd) = (hr (node xr))).
Proof.
Move=> xr Hxr; Step Hxd: (codom hd (hr xr)).
  By Rewrite: Ehd /setU -Ebgr (mem_maps Ihr) Hxr orbT.
Case/set0Pn: Hxd => [xd Dxd]; Rewrite: /preimage -(Eface ? xd) in Dxd.
By Exists (node (face xd)); Apply: eqP; Rewrite: -?EdErN eqd_sym.
Qed.

Remark EdF : (xd : gd; Hxd : (setC bgd xd)) (hd (face xd)) = (face (hd xd)).
Proof.
Move=> xd Hxd; Apply (monic_move (monicF_sym (Eface g))).
Rewrite: /setC -(Eface ? xd) -[yd](HbgdE 1!yd (set11?)) in Hxd.
By Rewrite: -EdN -EdE ?Eface.
Qed.

Remark ErF : (xr : gr; Hxr : (setC bgr (face xr)))
  (face (hr xr)) = (hr (face xr)).
Proof. By Move=> xr Hxr; Rewrite: -{1 xr}Eface ErE (ErN Hxr) Enode. Qed.

Remark EdrF : (xd : gd; xr : gr)
  ((hr (face xr)) =d (hd xd)) = ((hd (face xd)) =d (face (hr xr))). 
Proof.
Move=> xd xr; Rewrite: -{2 xr}Eface -{1 xd}Eface ErE.
By Rewrite: -(monic2F_eqd (Enode g)) -EdN eqd_sym EdErN.
Qed.

Local bbd : (set gd) := (fband bgd).

Lemma patch_fcard_face_d :
  (fcard face gd) = (addn (size bg) (fcard face (setC bbd))).
Proof. Rewrite: /bg size_maps -(scycle_fcard_fband Hbgd); Apply: n_compC. Qed.

Definition outer : (set g) := (fclosure face (codom hr)).

Lemma closed_gr : (fclosed edge (codom hr)).
Proof.
Refine (intro_closed (Sedge g) ?); Move=> x y Dy Hx.
By Rewrite: -(eqP Dy) -(f_iinv Hx) -ErE codom_f.
Qed.

Lemma closed_outer : (fclosed face outer).
Proof. Exact (closure_closed (Sface g) ?). Qed.

Remark closed_outerC : (fclosed face (setC outer)).
Proof. Exact (setC_closed closed_outer). Qed.

Lemma closed_gd : (fclosed node (codom hd)).
Proof.
Apply: (intro_closed (Snode g)) => [x y Dy Hx].
By Rewrite: -(eqP Dy) -(f_iinv Hx) -EdN codom_f.
Qed.

Lemma plain_patch : (plain g) == (andb (plainb (setC bgd)) (plainb gr)).
Proof.
PropCongr; Apply/idP/andP => [HgE | [HgdE HgrE]].
  Move: {HgE}(plain_eq HgE) (plain_neq HgE) => De2 He1.
  Split; Apply/plainP=> [x Hx].
    Split; RightBy Rewrite: -(inj_eqd Ihd) EdE // He1.
    By Apply Ihd; Rewrite: !EdE -?(fclosed1 (setC_closed HbgdE)) // De2.
  By Split; [Apply Ihr; Rewrite: !ErE De2 | Rewrite: -(inj_eqd Ihr) ErE He1].
Apply/plainP=> [x _]; Case Hxr: (codom hr x).
  Case/set0Pn: Hxr => [xr]; Move/eqP => Dx.
  By Rewrite: Dx -!ErE (inj_eqd Ihr) plain_eq // plain_neq.
Rewrite: Ehr in Hxr; Case/norP: Hxr; Move/negbE2; Move/set0Pn => [xd].
Move/eqP => Dx; Rewrite: Dx /bg (mem_maps Ihd); Move=> Hxd.
Case: (plainP HgdE ? Hxd) => [De2 He1].
By Rewrite: -!EdE -?(fclosed1 (setC_closed HbgdE)) // (inj_eqd Ihd) De2 He1.
Qed.

Lemma cubic_patch :
  (cubic g) == (andb (cubicb gd) (cubicb (setC bgr))).
Proof.
PropCongr; Apply/idP/andP => [HgN | [HgdN HgrN]].
  Move: {HgN}(cubic_eq HgN) (cubic_neq HgN) => De2 He1.
  Split; Apply/cubicP=> [x Hx].
    By Split; [Apply Ihd; Rewrite: !EdN De2| Rewrite: -(inj_eqd Ihd) EdN He1].
  Split; RightBy Rewrite: -(inj_eqd Ihr) ErN // He1.
  By Apply Ihr; Rewrite: !ErN -?(fclosed1 (setC_closed HbgrN)) // De2.
Apply/cubicP=> [x _]; Case Hxd: (codom hd x).
  Case/set0Pn: Hxd => [xd]; Move/eqP => Dx.
  By Rewrite: Dx -!EdN (inj_eqd Ihd) cubic_eq // cubic_neq.
Rewrite: Ehd in Hxd; Case/norP: Hxd; Move/negbE2; Move/set0Pn => [xd].
Move/eqP => Dx; Rewrite: Dx -Ebgr (mem_maps Ihr); Move=> Hxr.
Case: (cubicP HgrN ? Hxr) => [De2 He1].
By Rewrite: -!ErN -?(fclosed1 (setC_closed HbgrN)) // (inj_eqd Ihr) De2 He1.
Qed.

Lemma outer_hd : (xd : gd) (outer (hd xd)) = (bbd xd).
Proof.
Move=> xd; Rewrite: {outer}lock; Apply/idP/idP; Rewrite: -lock.
  Case/set0Pn=> [z]; Case/andP; Case/connectP => [p Hp []].
  Elim: p xd Hp => [|y p Hrec] xd /=.
    Clear; Rewrite Ebgdr; Apply: (subsetP (ring_fband ?)).
  Move/andP=> [Dy].
  Case Hxd: (bgd xd); LeftBy Do 2 Clear; Apply: (subsetP (ring_fband ?)).
  Rewrite: -(eqP Dy) -(EdF (negbI Hxd)); Move=> Hp Hz.
  By Rewrite: /bbd (fclosed1 (fbandF bgd)); Auto.
Move/hasP=> [zd Hzd Hxzd]; Move/connectP: Hxzd Hzd => [p Hp []] {zd}.
Elim: p xd Hp => [|yd p Hrec] xd /=.
  By Move=> _ Hxd; Apply: (subsetP (subset_closure ? ?)); Rewrite Ebgdr.
Move/andP=> [Dxd Hp] Hzd.
Case Hxd: (bgd xd).
  By Apply: (subsetP (subset_closure ? ?)); Rewrite Ebgdr.
Rewrite: /outer [b](closure_closed (Sface g) b 5!(hd xd) (set11 ?)).
Rewrite: -(EdF (negbI Hxd)) (eqP Dxd); Exact (Hrec ? Hp Hzd).
Qed.

Remark adj_hd : (rel_adjunction hd (eqdf face) (eqdf face) (setC outer)).
Proof.
Apply: (strict_adjunction (Sface ?) closed_outerC Ihd).
  Apply/subsetP => [x Hxn]; Rewrite Ehd; Apply/orP; Left; Apply/idP=> [Hx].
  By Case/set0Pn: Hxn; Exists x; Rewrite: /setI connect0.
Move=> xd Hxd yd; Rewrite: /eqdf -EdF ?(inj_eqd Ihd) //.
Rewrite: /setC outer_hd in Hxd.
By Apply/idP => [Hxd']; Case/idP: Hxd; Apply: (subsetP (ring_fband ?)).
Qed.

Lemma patch_face_d : (xd, yd : gd; Hxd : (setC outer (hd xd)))
  (cface xd yd) = (cface (hd xd) (hd yd)).
Proof. Exact (rel_functor adj_hd). Qed.

Remark IhdF : (xd : gd) (cface (hd xd) (hd (face xd))).
Proof.
Move=> xd; Case Hxd: (bgd xd); RightBy Rewrite: (EdF (negbI Hxd)) fconnect1.
Case/connectP: (etrans (Sface ? ? ?) (fconnect1 ? xd)) => [p].
Elim: p (face xd) => [| yd' p Hrec] yd /=; LeftBy Move=> _ [ ]; Apply connect0.
Move=> Hyp Ep; Case: (andP Hyp) => [Dyd Hp].
Case Hyd: (bgd yd).
  Rewrite: -(scycle_cface Hbgd 5!yd 6!xd) ?connect0 //.
  By Apply/connectP; Exists (Adds yd' p).
Apply: (connect_trans (Hrec ? Hp Ep)).
By Rewrite: Sface -(eqP Dyd) (EdF (negbI Hyd)) fconnect1.
Qed.

Lemma patch_face_d' : (xd, yd : gd) (cface xd yd) -> (cface (hd xd) (hd yd)).
Proof.
Move=> xd yd; Move/connectP=> [p Hp []] {yd}.
Elim: p xd Hp => [|yd p Hrec] xd /=; LeftBy Clear; Apply: connect0.
Move/andP=> [Dxd Hp].
By Apply: (connect_trans ? (Hrec ? Hp)); Rewrite: -(eqP Dxd) IhdF.
Qed.

Lemma patch_face_r : (xr, yr : gr) (cface xr yr) = (cface (hr xr) (hr yr)).
Proof.
Move=> xr yr; Apply/idP/idP.
  Move/connectP=> [p Hp []] {yr}.
  Elim: p xr Hp => [|yr p Hrec] xr /=; LeftBy Clear; Apply: connect0.
  Move/andP=> [Dxr Hp]; Apply: (connect_trans ? (Hrec ? Hp)) {p Hp Hrec}.
  Rewrite: -~{yr Dxr}(eqP Dxr).
  Case Hfxr: (bgr (face xr)).
    Case/HbgrP: Hfxr => [xd Dfxr _]; Rewrite: -Dfxr.
    Move/(introT eqP): Dfxr => Dfxr; Rewrite: eqd_sym EdrF in Dfxr.
    By Rewrite: cface1 -(eqP Dfxr) Sface IhdF.
  By Rewrite: -(ErF (negbI Hfxr)) fconnect1.
Pose x := (hr xr); Move/connectP=> [p Hp Ep].
Step Hhp: if (codom hr x) then x = (hr xr) else
               (EX xd | x = (hd xd) &
                 (EX yd | (hd yd) = (hr xr) & (cface yd xd))).
  By Rewrite: /x codom_f.
Elim: p x xr Hp Ep Hhp => [|z p Hrec] x xr /=.
  Move=> _ Dx; Rewrite: Dx codom_f; Move=> Dxr.
  By Rewrite: (Ihr Dxr) connect0.
Case/andP; Move/eqP=> Dz Hp Ep.
Case Ihrx: (codom hr x).
  Move=> Dx; Apply: (connect_trans (fconnect1 ? ?)).
  Apply: (Hrec ? ? Hp Ep) {Hp Ep Hrec}; Rewrite: -~{z}Dz.
  Case Ihrfx: (codom hr (face x)).
    Case Hfxr: (bgr (face xr)); RightBy Rewrite: -(ErF (negbI Hfxr)) Dx.
    Case/HbgrP: Hfxr => [xd Dxd _]; Rewrite: -Dxd.
    Move/(introT eqP): {}Dxd => Dfxd; Rewrite: eqd_sym EdrF in Dfxd.
    Rewrite: Dx -(eqP Dfxd); Congr hd; Apply: (scycle_cface Hbgd).
        By Rewrite: Sface fconnect1.
      By Rewrite: -Ebgdr (eqP Dfxd) -Dx.
    By Rewrite: -Ebgdr Dxd codom_f.
  Rewrite: Ehr in Ihrfx; Case/norP: Ihrfx; Move/negbE2; Case/set0Pn=> [xd].
  Move/eqP => Dfx; Exists xd; LeftDone.
  Exists (edge (node xd)); RightBy Rewrite: -{2 xd}Enode fconnect1.
  By Apply: eqP; Rewrite: EdErN EdN -Dfx Dx -{1 xr}Eface ErE Eedge set11.
Move=> [xd Dxd [yd Dyd Hxyd]]; Apply: (Hrec ? ? Hp Ep) {Hp Ep Hrec}.
Rewrite: Ehr Dxd /setU /setC codom_f /bg (mem_maps Ihd) /= in Ihrx.
Def: Efxd := (EdF (negbI Ihrx)); Rewrite: -~{z}Dz.
Case Ihrfx: (codom hr (face x)).
  Rewrite: Dxd -Efxd -Dyd; Congr hd; Apply: (scycle_cface Hbgd).
      By Rewrite: -cface1 Sface.
    By Rewrite: -Ebgdr Efxd -Dxd.
  By Rewrite: -Ebgdr Dyd codom_f.
Exists (face xd); LeftBy Rewrite Dxd.
By Exists yd; RightBy Rewrite: -cface1r.
Qed.

Lemma patch_face_dr : (xd : gd; Hxd : (outer (hd xd)))
  {yd : gd & {yr : gr | (hd yd) = (hr yr) /\ (cface xd yd) &
       (cface (hd xd)) =1 (cface (hr yr))}}.
Proof.
Move=> xd Hxd; Case/pickP: (setI (cface xd) bgd) => [yd Hyd | Hnxd].
  Exists yd; Case/andP: Hyd => [Hxyd Hyd].
  Step Hyr: (codom hr (hd yd)).
    By Rewrite: Ehr /setU /bg (mem_maps Ihd) Hyd orbT.
  Exists (iinv Hyr); Rewrite f_iinv; LeftBy Split.
  Exact (same_cface (patch_face_d' Hxyd)).
Rewrite outer_hd in Hxd; Case/hasPn: Hxd => [yd Hyd]; Apply/idP => [Hxyd].
By Case/andP: (Hnxd yd); Split.
Qed.

Lemma patch_bridgeless : (bridgeless g) -> (bridgeless gd) /\ (bridgeless gr).
Proof.
Move=> Hgl; Split.
  Apply/set0P=> [xd]; Rewrite: cface1r; Apply/idP=> [Hfexd].
  Case/set0Pn: Hgl; Exists (hd xd).
  By Rewrite: cface1r -{2 xd}Eedge EdN Enode; Apply patch_face_d'.
By Apply/set0P=> [xr]; Rewrite: patch_face_r ErE (set0P Hgl).
Qed.

Lemma bridgeless_patch : (bridgeless gd) -> (bridgeless gr) ->
  (chordless bgd) -> (bridgeless g).
Proof.
Move=> Hgdl Hgrl Hgdc; Apply/set0P=> [x]; Apply/idP=> [Hnex].
Case Hx: (codom hr x).
  Move/set0Pn: Hx => [xr Dx]; Rewrite: (eqP Dx) -ErE in Hnex.
  By Case/set0Pn: Hgrl; Exists xr; Rewrite patch_face_r.
Rewrite: Ehr in Hx; Case/norP: Hx; Move/negbE2.
Case/set0Pn=> [xd]; Move/eqP => Dx Hbx.
Rewrite: /bg Dx (mem_maps Ihd) in Hbx; Rewrite: Dx -(EdE Hbx) in Hnex.
Case Hxr: (outer (hd xd));
  RightBy Case/idP: (set0P Hgdl xd); Rewrite: patch_face_d // /setC Hxr.
Step Hexr: (outer (hd (edge xd))).
  Apply: etrans Hxr; Symmetry; Apply: (closed_connect ? Hnex).
  Apply: closure_closed; Apply: Sface.
Rewrite: !outer_hd in Hxr Hexr; Move/hasP: Hxr => [yd Hyd Hxyd].
Move/hasP: Hexr => [zd Hzd Hexzd].
Case/set0Pn: (subsetP Hgdc ? Hyd); Exists zd.
Apply/andP; Split; LeftBy Apply/adjP; Exists xd; LeftBy Rewrite Sface.
Case/HbgdP: {}Hyd => [yr Dyr Dnyr]; Rewrite: /setD1 Hzd andbT.
Case/andP: {}Hbgd => [Dbgd _].
Apply/andP; Split; Apply/eqP=> [Dzd]; Case/set0Pn: Hgrl.
  Exists (node yr); Rewrite: cface1r Enode.
  Rewrite: patch_face_r -Dnyr -Dyr (eqP (next_cycle Dbgd Hyd)) Dzd.
  Apply: (connect_trans (connect_trans ? Hnex)).
    By Rewrite Sface; Apply patch_face_d'.
  By Apply patch_face_d'.
Exists (node (node yr)); Rewrite: cface1r Enode.
Def: Dnnyr := (introT eqP Dnyr); Rewrite: -{1 yd}Eface EdErN in Dnnyr.
Rewrite: patch_face_r -Dnyr -(eqP Dnnyr) -{1 yd}(eqP (prev_cycle Dbgd Hyd)).
Rewrite: Eedge Dzd Sface; Apply: (connect_trans (connect_trans ? Hnex)).
  By Rewrite Sface; Apply patch_face_d'.
By Apply patch_face_d'.
Qed.

Local ag : (set g) := (closure glink (codom hr)).

Remark Hag : (closed glink ag).
Proof. Exact (closure_closed (Sglink ?) ?). Qed.

Remark Hagr : (n_comp glink gr) = (n_comp glink ag).
Proof.
Def: Hgg := (Sglink g); Def: Hggr := (Sglink gr).
Rewrite (adjunction_n_comp 3!hr Hgg Hggr Hag).
  Apply: eq_card => [xr]; Rewrite: /setI /preimage /ag.
  By Rewrite: (subsetP (subset_closure 1!g glink ?) ? (codom_f hr xr)).
Split.
  Move=> x Hx; Case: (pickP (setI (connect glink x) (codom hr))).
    By Move=> y; Move/andP=> [Hxy Hy]; Exists (iinv Hy); Rewrite f_iinv.
  By Move=> Hnx; Case/set0P: Hx.
Move=> xr zr _; Apply/idP/idP; Rewrite: -clink_glink.
  Move/connectP => [p Hp []] {zr}.
  Elim: p xr Hp => [|yr p Hrec] xr /=; LeftBy Rewrite connect0.
  Move/andP=> [Hxr Hp]; Apply: (connect_trans ? (Hrec ? Hp)) {Hrec Hp}.
  Step Hfzr : (zr : gr) (connect glink (hr zr) (hr (face zr))).
    Move=> zr; Move: (fconnect1 face zr); Rewrite patch_face_r.
    Apply: (!connect_sub ?) {zr} => [x y]; Case/eqP {y}.
    Exact (connect1 (glinkF ?)).
  Case/clinkP: Hxr => [Dxr | Dfxr]; RightBy Rewrite: -Dfxr Hfzr.
  By Apply: (connect_trans (connect1 (glinkE ?))); Rewrite: -{yr}Enode -Dxr -ErE.
Pose x := (hr xr); Move/connectP=> [p Hp Ep].
Step Hxr: if (codom hr x) then x = (hr xr) else (bgr xr) By Rewrite: /x codom_f.
Elim: p x xr Hp Ep Hxr => [|y p Hrec] x xr /=.
  Move=> _ Dx; Rewrite: Dx codom_f; Move=> Dxr.
  By Rewrite: (Ihr Dxr) connect0.
Move/andP=> [Hxy Hp] Ep.
Case Hyd: (codom hd y).
  Step Hbzr : (yr : gr) (bgr yr) -> (connect glink yr zr).
    Move {x xr Hxy} => xr Hxr.
    Case Hyr: (codom hr y) [x](Hrec y x Hp Ep); [Clear Hp Ep Hrec | By Auto].
    Rewrite: Ehd /setU /setC ~Hyr -Ebgr in Hyd; Case/mapsP: Hyd=> [yr Hyr Dy].
    Move=> Hrec; Apply: (connect_trans ? (Hrec ? (esym Dy))) {Hrec Dy}.
    Rewrite: -~{Hxr}(EbgrN Hxr) in Hyr; Apply: connect_sub xr yr Hyr => [xr yr].
    By Move/eqP=> Dyr; Apply connect1; Rewrite: -Dyr glinkN.
  Case (codom hr x); [Move=> Dx | By Auto]; Rewrite: ~{x}Dx in Hxy.
  Case/clinkP: Hxy => [Dxrn | Dfxr].
    By Apply Hbzr; Rewrite: -Ebgrd Dxrn -(f_iinv Hyd) -EdN codom_f.
  Apply: (connect_trans (connect1 (glinkF ?))); Apply: Hbzr {Hbzr}.
  By Apply/idPn=> [Hfxr]; Rewrite: -Ebgrd -(ErF Hfxr) Dfxr Hyd in Hfxr.
Rewrite: Ehd in Hyd; Case/norP: Hyd; Move/negbE2; Case/set0Pn => [yr].
Move/eqP=> Dy Hyr; Rewrite: Dy -Ebgr (mem_maps Ihr) in Hyr; Move=> Hx.
Apply: (connect_trans ? (Hrec ? yr Hp Ep ?)) {Hp Ep Hrec};
  RightBy Rewrite: Dy codom_f.
Rewrite: -clink_glink; Apply connect1.
Case/clinkP: Hxy => [Dny | Dfx].
  Rewrite: Dy -(ErN Hyr) in Dny; Rewrite: Dny codom_f in Hx.
  By Rewrite: -(Ihr Hx) clinkN.
Rewrite: -{1 y}Enode Dy -(ErN Hyr) -ErE in Dfx.
Rewrite: (Iface ? Dfx) codom_f in Hx.
By Rewrite: -{1 yr}Enode (Ihr Hx) clinkF.
Qed.

Lemma patch_connected_r : (connected g) -> (negb (set0b gr)) -> (connected gr).
Proof.
Move=> Hcg Hgr; Rewrite: /connected Hagr -(eq_n_comp_r 2!g) //.
Case/set0Pn: Hgr => [xr _] y; Symmetry; Apply/set0Pn.
Exists (hr xr); Rewrite: /setI codom_f andbT -clink_glink.
Apply/connectP; Apply: (connected_clink Hcg).
Qed.

Lemma patch_fcard_face_r : (fcard face gr) = (fcard face outer).
Proof.
Rewrite: /= (adjunction_n_comp 3!hr (Sface ?) (Sface ?) closed_outer).
  Apply: eq_card => [xr]; Rewrite: /setI /preimage andbC /outer.
  By Rewrite: (subsetP (subset_closure (eqdf face) (codom hr))) ?codom_f ?andbT.
Split; RightBy Exact [xr; yr; _](patch_face_r xr yr).
Move=> x Hx; Case: (pickP (setI (cface x) (codom hr))).
  By Move=> y; Move/andP=> [Hxy Hy]; Exists (iinv Hy); Rewrite f_iinv.
By Move=> Hnxr; Case/set0P: Hx.
Qed.

Lemma genus_patch : (genus g) = (addn (genus gd) (genus gr)).
Proof.
Pose ebg := (size bg) =d (0).
Step Hebgd: if ebg then bgd = seq0 else (EX xd | (bgd xd)).
  By Rewrite: /ebg /bg; Case: {}bgd => [|x p] //; Exists x; Rewrite: /= setU11.
Step Hebgr: if ebg then  bgr = seq0 else (EX xr | (bgr xr)).
  Rewrite: /ebg -size_rev -Dbgr; Case: {}bgr => [|x p] //.
  By Exists x; Rewrite: /= setU11.
Step HcdE : (fcard edge gd) = (addn (negb ebg) (fcard edge (setC (codom hr)))).
  Rewrite: (n_compC bgd); Congr addn.
    Case: {}ebg Hebgd; [Move=> Dbgd | Move=> [x Hx]].
      By Apply: eq_card0 => [x]; Rewrite: Dbgd /= /setI andbF.
    Rewrite: -(eq_n_comp_r (EbgdE Hx)); Apply: (n_comp_connect (Sedge ?)).
  Def: closed_grC := (setC_closed closed_gr).
  Rewrite: (adjunction_n_comp 3!hd (Sedge ?) (Sedge ?) closed_grC).
    Apply: eq_n_comp_r => [x]; Congr negb.
    By Rewrite: Ehr /setU /setC codom_f /= /bg (mem_maps Ihd).
  Apply (strict_adjunction (Sedge ?) closed_grC Ihd).
    Apply/subsetP => [x Hx]; Rewrite: /setC Ehr in Hx.
    By Case/norP: Hx; Rewrite: /setC negb_elim.
  Move=> xd; Rewrite: /setC Ehr /setU /setC codom_f /= /bg (mem_maps Ihd).
  By Move=> Hxd yd; Rewrite: /eqdf /= -(EdE Hxd) (inj_eqd Ihd).
Step HcdF : (fcard face gd) = (addn (size bg) (fcard face (setC outer))).
  Rewrite: patch_fcard_face_d; Congr addn.
  Rewrite (adjunction_n_comp (Sface ?) (Sface ?) closed_outerC adj_hd).
  By Apply: eq_card => [xd]; Rewrite: /setI /setC -outer_hd.
Step HcdN: (fcard node gd) = (fcard node (codom hd)).
  Rewrite: (adjunction_n_comp 3!hd (Snode ?) (Snode ?) closed_gd).
    By Apply: eq_card=> [xd]; Rewrite: /setI /preimage codom_f.
  Apply: (strict_adjunction (Snode ?) closed_gd Ihd (subset_refl ?)) => [xd _ yd].
  By Rewrite: /eqdf -EdN (inj_eqd Ihd).
Step HcdG : (n_comp glink gd) = (addn (negb ebg) (n_comp glink (setC ag))).
  Def: Hgg := (Sglink g); Def: Hggd := (Sglink gd).
  Step Eggd: (x, y : gd) (setC bgd x) -> (glink (hd x) (hd y)) = (glink x y).
    Move=> x y Hx; Rewrite: {1}/glink /relU /setU /eqdf.
    By Rewrite: -(EdE Hx) -EdN -(EdF Hx) !(inj_eqd Ihd).
  Rewrite: (adjunction_n_comp 3!hd Hgg Hggd (setC_closed Hag)).
    Rewrite (n_compC (preimage hd ag)); Congr addn.
    Case: {}ebg Hebgd; [Move=> Dbgd | Move=> [x Hx]].
      Apply: eq_card0 => [x]; Apply/nandP; Right; Apply/set0Pn=> [[y Hy]].
      Case/andP: Hy; Rewrite: -clink_glink; Move/connectP=> [p Hp []] {y}.
      Elim: p x Hp => [|y p Hrec] xd; LeftBy Rewrite: /= Ebgdr Dbgd.
      Case/andP; Move/clinkP=> [Dx | Dy].
        Rewrite: -{1 xd}Eedge EdN in Dx; Rewrite: -(Inode g Dx); EAuto.
      By Rewrite: -Dy -EdF ?Dbgd; EAuto.
    Apply: etrans (n_comp_connect Hggd x); Apply: eq_n_comp_r => [y].
    Rewrite: /preimage /ag; Apply/set0Pn/idP.
      Case=> [z]; Case/andP; Rewrite: -clink_glink; Move/connectP=> [p Hp []] {z}.
      Elim: p y Hp => [|z p Hrec] y /=.
        Clear; Rewrite: Ebgdr -~{Hx}(EbgdE Hx); Apply: connect_sub x y => [x y].
        By Case/eqP; Apply connect1; Rewrite: glinkE.
      Case/andP; Move/clinkP=> [Dy | Dz].
        Rewrite: -{1 y}Eedge EdN in Dy; Rewrite: -(Inode g Dy).
        Move=> Hq Eq; Apply: (connect_trans (Hrec ? Hq Eq)) {Hrec Hq Eq}.
        By Apply connect1; Rewrite: -{2 y}Eedge glinkN.
      Case Hy: (bgd y).
        Move=> _ _ {q z Hrec Dz}; Rewrite: -(EbgdE Hx) in Hy.
        Apply: connect_sub x y Hy {Hx} => [x y]; Case/eqP; Apply connect1.
        By Rewrite: glinkE.
      Rewrite: -(EdF (negbI Hy)) in Dz; Rewrite: -Dz.
      Move=> Hq Eq; Apply: (connect_trans (Hrec ? Hq Eq)) {Hrec Hq Eq}.
      By Rewrite: Hggd connect1 ?glinkF.
    Rewrite: Hggd; Move/connectP => [p Hp Dx]; Case: {x}Dx Hx.
    Elim: p y Hp => [|y p Hrec] x /=.
      By Move=> _ Hx; Exists (hd x); Rewrite: /setI connect0 Ebgdr.
    Case Hx: (bgd x).
      By Move=> _ _; Exists (hd x); Rewrite: /setI connect0 Ebgdr.
    Move/andP=> [Hxy Hp] Ep.
    Case: {p Hrec Hp Ep}(Hrec ? Hp Ep) => [z Hz]; Exists z.
    Rewrite: -(Eggd x y (negbI Hx)) in Hxy.
    By Rewrite: /setI (same_connect Hgg (connect1 Hxy)).
  Apply (strict_adjunction Hggd (setC_closed Hag) Ihd).
    Apply/subsetP => [x Hxn]; Case/orP: (EhdUr x) => // [Hx].
    By Case/idP: Hxn; Apply: (subsetP (subset_closure ? ?)).
  Move=> xd Hx yd; Apply Eggd; Apply/idP => [Hxd]; Case/idP: Hx.
  By Apply: (subsetP (subset_closure ? ?)); Rewrite Ebgdr.
Step HcrE: (fcard edge gr) = (fcard edge (codom hr)).
  Rewrite: (adjunction_n_comp 3!hr (Sedge ?) (Sedge ?) closed_gr).
    By Apply: eq_card => [z]; Rewrite: /setI /preimage codom_f.
  Apply (strict_adjunction (Sedge ?) closed_gr Ihr (subset_refl ?)).
  By Move=> xr _ yr; Rewrite: {1}/eqdf -ErE (inj_eqd Ihr).
Step HcrN: (fcard node gr) = (addn (negb ebg) (fcard node (setC (codom hd)))).
  Def: HafC := (setC_closed closed_gd).
  Rewrite: (adjunction_n_comp 3!hr (Snode ?) (Snode ?) HafC).
    Rewrite: (n_compC [x](codom hd (hr x))); Congr addn.
    Case: {}ebg Hebgr; [Move=> Dbgr0 | Move=> [x Hx]].
      By Apply: eq_card0 => [x]; Rewrite: /setI Ebgrd Dbgr0 andbF.
    Apply: etrans (n_comp_connect (Snode ?) x); Apply: eq_n_comp_r => [y].
    By Rewrite: Ebgrd (EbgrN Hx).
  Apply (strict_adjunction (Snode ?) HafC Ihr).
    Apply/subsetP=> [x]; Rewrite: /setC Ehd /setC.
    By Case/norP; Rewrite negb_elim.
  Move=> xr; Rewrite: /setC Ebgrd /eqdf; Move=> Hxr yr.
  By Rewrite: -(ErN Hxr) (inj_eqd Ihr).
Rewrite: {1}/genus -(subn_add2l (addn (genus_lhs gd) (genus_lhs gr))).
Rewrite: addnC {1 4 5}/genus_lhs !even_genusP /genus_rhs.
Rewrite: (n_compC ag) (n_compC (codom hr)) (n_compC (codom hd))(n_compC outer).
Rewrite: HcdE HcdF -HcdN HcdG -HcrE -patch_fcard_face_r HcrN -Hagr !double_add.
Rewrite: -!addnA (double_addnn (negb ebg)) (addnCA (card gd)).
Rewrite: (addnA (card gd)) card_patch -!addnA -!(addnCA (negb ebg)).
Rewrite: !subn_add2l addnCA !subn_add2l -(addnCA (card g)) subn_add2l addnC.
Rewrite: -!addnA !(addnCA (double (genus gr))) -double_add.
Do 2 Rewrite: addnA addnCA subn_add2l; Rewrite: -!addnA !subn_add2l.
By Do 2 Rewrite: addnCA subn_add2l; Rewrite: subn_addr half_double addnC.
Qed.

Lemma planar_patch : (planar g) == (andb (planarb gd) (planarb gr)).
Proof. By PropCongr; Rewrite: genus_patch eqn_add0. Qed.

Lemma colorable_patch : (four_colorable g) <->
  (EX et | (ring_trace bgd et) & (ring_trace bgr (rot (1) (rev et)))).
Proof.
Split.
  Move=> [k [HkE HkF]]; Exists (trace (maps k bg)).
    Exists (comp k hd); RightBy Rewrite (maps_comp k hd).
    Step Hk'F: (invariant face (comp k hd)) =1 gd.
      Move=> x; Apply/eqcP; Apply: (fconnect_invariant HkF); Apply patch_face_d'.
      By Rewrite: Sface fconnect1.
    Split; RightDone; Move => xd; Rewrite: /invariant -{2 xd}Eedge.
    Rewrite: -(eqcP (Hk'F (edge xd))) /comp EdN; Pose y := (hd (face (edge xd))).
    Rewrite: -{1 y}Enode (eqcP (HkF (edge (node y)))); Apply: HkE.
  Exists (comp k hr); RightBy Rewrite: -trace_rev -maps_rev -Dbgr -maps_comp.
  Split; LeftBy  Move=> x; Rewrite: /invariant /comp ErE; Apply: HkE.
  Move=> x; Apply/eqcP; Apply: (fconnect_invariant HkF).
  By Rewrite: -patch_face_r Sface fconnect1.
Move=> [et [kd [HkdE HkdF] Ekd] [kr [HkrE HkrF] Ekr]]; Simpl in Ekd Ekr.
Pose c0 := (addc (head_color (maps kd (rev bgd))) (head_color (maps kr bgr))).
Pose kd' := (comp (addc c0) kd); Def: Ic0 := (monic_inj 1!color (addc_inv c0)).
Step Hkd'E: (invariant edge kd') =1 set0.
  By Move=> x; Rewrite: -(HkdE x); Apply: invariant_inj.
Step Hkd'F: (invariant face kd') =1 gd.
  By Move=> x; Rewrite: -(HkdF x); Apply: invariant_inj.
Step Ebkd'r: (rev (maps kd' bgd)) = (maps kr bgr).
  Move: Ekr; Rewrite: Ekd -trace_rev -!maps_rev /kd' (maps_comp (addc c0) kd) /c0.
  Case: (rev bgd) => [|xd bgd']; LeftBy Case: {}bgr; Move => // xr; Case.
  Case: {}bgr => [|xr bgr'] Ekdr; LeftBy Case: bgd' Ekdr.
  Rewrite: /= -untrace_trace -maps_adds trace_addc addcC addc_inv.
  By Rewrite: -maps_adds Ekdr maps_adds untrace_trace.
Move: {kd c0}kd' Hkd'E Hkd'F Ebkd'r {Ic0 HkdE HkdF Ekd Ekr} => kd HkdE HkdF Ebkdr.
Step Ekdr: (xd : gd; xr : gr) (hd xd) = (hr xr) -> (kd xd) = (kr xr).
  Move=> xd xr Dx; Step Hxd: (bgd xd) By Rewrite: -Ebgdr Dx codom_f.
  Step Hxr: (rev bgr xr) By Rewrite: mem_rev -Ebgrd -Dx codom_f.
  Rewrite: -(sub_index xd Hxd) -(sub_index xr Hxr).
  Rewrite: -index_mem in Hxd; Rewrite: -index_mem in Hxr.
  Rewrite: -(sub_maps xr Color0) // maps_rev -Ebkdr rev_rev.
  Rewrite: -(sub_maps xd Color0) //; Congr (sub Color0).
  By Rewrite: -(index_maps Ihd) -(index_maps Ihr) maps_rev Dbgr rev_rev Dx.
Pose dhd := [x; xd]x =d (hd xd); Pose dhr := [x; xr]x =d (hr xr).
Pose k := [x]if pick xr in (dhr x) then (kr xr) else
             if pick xd in (dhd x) then (kd xd) else Color0.
Def: Hkk := [d; a](introT (!set0Px d a)).
Step HkF: (invariant face k) =1 g.
  Move=> x; Rewrite: /invariant /k /setA; Apply/eqP.
  Case: (pickP (dhr x)) => [xr Dx | Hxr].
    Case: (pickP (dhr (face x))) => [yr Dy | Hyr].
      Apply: (fconnect_invariant HkrF).
      By Rewrite: patch_face_r -(eqP Dx) -(eqP Dy) Sface fconnect1.
    Case: (pickP (dhd (face x))) => [yd Dy | Hyd].
      Rewrite: (eqP Dx) /dhd -{1 yd}Enode eqd_sym -EdrF in Dy.
      Rewrite: -(eqcP (HkrF xr)) -{1 yd}Enode (eqcP (HkdF (edge (node yd)))).
      By Apply: Ekdr; Case/eqP: Dy.
    By Move: (EhdUr (face x)); Rewrite: /setU /codom !Hkk.
  Case: (pickP (dhd x)) => [xd Dx | Hxd].
    Step Hxd: (negb (bgd xd)) By Rewrite: -Ebgdr /codom Hkk -?(eqP Dx).
    Rewrite: -(eqcP (HkdF xd)) (eqP Dx) -(EdF Hxd).
    Case: (pickP (dhr (hd (face xd)))) => [yr Dy | Hyr].
      By Symmetry; Apply: Ekdr; Case/eqP: Dy.
    Case: (pickP (dhd (hd (face xd)))) => [yd Dy | Hyd].
      By Rewrite: (Ihd (eqP Dy)).
    By Case/eqP: (Hyd (face xd)).
  By Move: (EhdUr x); Rewrite: /setU /codom !Hkk.
Exists k; Split; RightDone; Move=> x; Rewrite: /invariant /k.
Case: (pickP (dhr x)) => [xr Dx | Hxr].
  Rewrite: (eqP Dx) -ErE.
  Case: (pickP (dhr (hr (edge xr)))) => [yr Dy | Hyr].
    Rewrite: -(Ihr (eqP Dy)); Apply: HkrE.
  By Case/eqP: (Hyr (edge xr)).
Case: (pickP (dhd x)) => [xd Dx | Hxd].
  Step Hxd: (negb (bgd xd)) By Rewrite: -Ebgdr /codom Hkk -?(eqP Dx).
  Def: HxdE := (HkdE xd); Rewrite: (eqP Dx) -(EdE Hxd).
  Case: (pickP (dhr (hd (edge xd)))) => [yr Dy | Hyr].
    By Rewrite: -(Ekdr ? ? (eqP Dy)).
  Case: (pickP (dhd (hd (edge xd)))) => [yd Dy | Hyd].
    By Rewrite: -(Ihd (eqP Dy)).
  By Case/eqP: (Hyd (edge xd)).
By Move: (EhdUr x); Rewrite: /setU /codom !Hkk.
Qed.

End Patch.

(* Patching disjoint components of the map along empty borders. Used to *)
(* show that the minimal counter example is connected.                  *)

Section PatchGcomp.

Variables g : hypermap; z : g.

Definition gcompd_dart : finSet := (subFin (gcomp z)).

Remark Hgcompd_edge : (u : gcompd_dart) (gcomp z (edge (subdE u))).
Proof. By Move=> [x Hx]; Exact (connect_trans Hx (connect1 (glinkE ?))). Qed.

Remark Hgcompd_node : (u : gcompd_dart) (gcomp z (node (subdE u))).
Proof. By Move=> [x Hx]; Exact (connect_trans Hx (connect1 (glinkN ?))). Qed.

Remark Hgcompd_face : (u : gcompd_dart) (gcomp z (face (subdE u))).
Proof. By Move=> [x Hx]; Exact (connect_trans Hx (connect1 (glinkF ?))). Qed.

Definition gcompd_edge [u : gcompd_dart] : gcompd_dart :=
  (subdI (Hgcompd_edge u)).
Definition gcompd_node [u : gcompd_dart] : gcompd_dart :=
  (subdI (Hgcompd_node u)).
Definition gcompd_face [u : gcompd_dart] : gcompd_dart :=
  (subdI (Hgcompd_face u)).

Remark gcompd_monic : (monic3 gcompd_edge gcompd_node gcompd_face).
Proof. Move=> [x Hx]; Apply: subdE_inj; Apply: Eedge. Qed.

Definition gcomp_disk : hypermap := (Hypermap gcompd_monic).
Definition gcompd [u : gcomp_disk] : g := (subdE u).

Lemma inj_gcompd : (injective gcompd). Proof. Exact (subdE_inj 2!?). Qed.
Lemma codom_gcompd : (codom gcompd) =1 (gcomp z).
Proof.
Move=> x; Apply/set0Pn/idP => [[[y Hy] Dy] | Hx]; LeftBy Rewrite (eqP Dy).
Exists ((subdI Hx)::gcomp_disk); Exact (set11 ?).
Qed.

Definition gcompr_dart : finSet := (subFin (setC (gcomp z))).

Remark gcompr_edgeP : (u : gcompr_dart) (setC (gcomp z) (edge (subdE u))).
Proof.
Move=> [x Hx]; Apply/idP=> /= [Hx']; Case/idP: Hx.
Apply: (connect_trans Hx'); Rewrite: Sglink /=; Apply connect1; Apply glinkE.
Qed.

Remark gcompr_nodeP : (u : gcompr_dart) (setC (gcomp z) (node (subdE u))).
Proof.
Move=> [x Hx]; Apply/idP=> /= [Hx']; Case/idP: Hx.
Apply: (connect_trans Hx'); Rewrite: Sglink /=; Apply connect1; Apply glinkN.
Qed.

Remark gcompr_faceP : (u : gcompr_dart) (setC (gcomp z) (face (subdE u))).
Proof.
Move=> [x Hx]; Apply/idP=> /= [Hx']; Case/idP: Hx.
Apply: (connect_trans Hx'); Rewrite: Sglink /=; Apply connect1; Apply glinkF.
Qed.

Definition gcompr_edge [u : gcompr_dart] : gcompr_dart :=
  (subdI (gcompr_edgeP u)).
Definition gcompr_node [u : gcompr_dart] : gcompr_dart :=
  (subdI (gcompr_nodeP u)).
Definition gcompr_face [u : gcompr_dart] : gcompr_dart :=
  (subdI (gcompr_faceP u)).

Remark gcompr_monic : (monic3 gcompr_edge gcompr_node gcompr_face).
Proof. Move=> [x Hx]; Apply: subdE_inj; Apply: Eedge. Qed.

Definition gcomp_rem : hypermap := (Hypermap gcompr_monic).
Definition gcompr [u : gcomp_rem] : g := (subdE u).
Lemma inj_gcompr : (injective gcompr). Proof. Exact (subdE_inj 2!?). Qed.
Lemma codom_gcompr : (codom gcompr) =1 (setC (gcomp z)).
Proof.
Move=> x;  Apply/set0Pn/idP => [[[y Hy] Dy] | Hx]; LeftBy Rewrite (eqP Dy).
Exists ((subdI Hx)::gcomp_rem); Exact (set11 ?).
Qed.

Lemma patch_gcomp : (patch gcompd gcompr seq0 seq0).
Proof.
Repeat Split; Try Done; Try Apply inj_gcompd; Try Apply inj_gcompr.
By Move=> x; Rewrite: /setU /setC /= orbF codom_gcompd codom_gcompr.
Qed.

End PatchGcomp.

Lemma minimal_counter_example_is_connected : (g : hypermap)
  (minimal_counter_example g) -> (connected g).
Proof.
Move=> g Hg; Apply/idPn=> [Hcg]; Case (minimal_counter_example_is_noncolorable Hg).
Case: (pickP g) => [z _ | Hg0];
  RightBy Exists [_:g]Color0; Split; Move=> x; Move: (Hg0 x).
Def: Hpgdr := (patch_gcomp z); Def: Hpg : (planar g) := Hg.
Rewrite (planar_patch Hpgdr) in Hpg; Move/andP: Hpg => [Hpgd Hpgr].
Case: (patch_bridgeless Hpgdr Hg) => [Hgbd Hgbr].
Def: HgE : (plain g) := Hg; Def: HgN : (cubic g) := Hg.
Rewrite (plain_patch Hpgdr) in HgE; Move/andP: HgE => [HgdE HgrE].
Rewrite (cubic_patch Hpgdr) in HgN; Case/andP: HgN.
Move/cubic_precubic=> HgdN; Move/cubic_precubic=> HgrN.
Def: Hng := (card_patch Hpgdr); Rewrite: /= add0n in Hng.
Def: Hmg := (minimal_counter_example_is_minimal Hg).
Case: (colorable_patch Hpgdr) => [_ H]; Apply: H {H}; Exists (seq0 :: colseq).
  Case: (Hmg (gcomp_disk z)); Try (By Repeat Split; Auto);
    RightBy Move=> kd Hkd; Exists kd.
  Rewrite: -addn1 -Hng /= leq_add2l ltnNge leqn0.
  Apply/eqP=> [Hgr]; Case/eqnP: Hcg; Rewrite: -(n_comp_connect (Sglink ?) z).
  Apply: eq_n_comp_r => [x]; Symmetry.
  Exact (negbEf (set0P (introT eqP (etrans (esym (card_sub_dom ?)) Hgr)) x)).
Case: (Hmg (gcomp_rem z)); Try (By Repeat Split; Auto);
  RightBy Move=> kr Hkr; Exists kr.
Rewrite: -add1n -Hng leq_add2r ltnNge leqn0; Apply/eqP=> [Hgd].
Case/idP: (card0_eq (etrans (esym (card_sub_dom ?)) Hgd) z); Apply: connect0.
Qed.

Coercion minimal_counter_example_is_connected :
  minimal_counter_example >-> connected.

Definition minimal_counter_example_is_planar_bridgeless_plain_connected :
  (g : hypermap) (minimal_counter_example g) ->
  (planar_bridgeless_plain_connected g).
Move=> g Hg; Split; Exact Hg. Defined.

Coercion minimal_counter_example_is_planar_bridgeless_plain_connected
  : minimal_counter_example >-> planar_bridgeless_plain_connected.

Definition minimal_counter_example_is_planar_plain_cubic_connected :
  (g : hypermap) (minimal_counter_example g) -> (planar_plain_cubic_connected g).
Repeat Move=> g Hg; Repeat Split; Exact Hg. Defined.

Coercion minimal_counter_example_is_planar_plain_cubic_connected
  : minimal_counter_example >-> planar_plain_cubic_connected.

Unset Implicit Arguments.

