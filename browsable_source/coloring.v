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
Require walkup.
Require geometry.
Require color.
Require chromogram.

(* Hypermap, graph and contract colorings, colorable maps, ring traces, valid *)
(* contracts, and the definition of the special maps used in the proof:       *)
(* minimal counter example, C-reducible, and  embeddable.                     *)
(*   Results established here include the decidability of coloring, and the   *)
(* proof that minimal counter examples are also cubic.                        *)

Set Implicit Arguments.

Section Coloring.

Variable g : hypermap. 

Definition coloring [k : g -> color] : Prop :=
  (invariant edge k) =1 set0 /\ (invariant face k) =1 g.

Lemma coloring_inj : (h : color -> color) (injective h) -> 
  (k : g -> color) (coloring k) -> (coloring (comp h k)).
Proof.
Move=> h Hh k [HkE HkF]; Split; Move=> x; Rewrite: /invariant.
  By Move: (HkE x); Rewrite: -(invariant_inj edge Hh k).
By Move: (HkF x); Rewrite: -(invariant_inj face Hh k).
Qed.

Definition ring_trace [r : (seq g); et : colseq] : Prop :=
  (EX k | (coloring k) & et = (trace (maps k r))).

Definition four_colorable : Prop :=
  (EX k : g -> color | (coloring k)).

Lemma colorable_bridgeless : four_colorable -> (bridgeless g).
Proof.
Move=> [k [HkE HkF]]; Apply/set0Pn=> [[x Hx]]; Case/idP: (HkE x); Apply/eqP.
By Rewrite: -(fconnect_invariant HkF Hx).
Qed.

Definition graph_coloring [k : g -> color] : Prop :=
  (invariant edge k) =1 set0 /\ (invariant node k) =1 g.

Definition graph_four_colorable : Prop :=
  (EX k : g -> color | (graph_coloring k)).

Definition cc_coloring [cc : (seq g); k : g -> color] : Prop :=
  (invariant edge k) =1 (insertE cc) /\ (invariant face k) =1 g.

Definition cc_colorable [cc : (seq g)] : Prop :=
  (EX k | (cc_coloring cc k)).

Definition cc_ring_trace [cc, r : (seq g); et : colseq] : Prop :=
  (EX k | (cc_coloring cc k) & et = (trace (maps k r))).

End Coloring.

Section ColoringDual.

Variable g : hypermap. 

Lemma coloring_dual : (k : g -> color)
  (!coloring (dual g) k) <-> (graph_coloring k).
Proof.
Move=> k; Split.
  Move=> [HkE' HkF']; Split; Move=> x; Rewrite: /invariant eqd_sym.
    Rewrite: -{1 x}(finv_f (Iedge g)); Exact (HkE' (edge x)).
  Rewrite: -{1 x}(finv_f (Inode g)); Exact (HkF' (node x)).
Move=> [HkE HkN]; Split; Move=> x; Rewrite: /invariant eqd_sym.
  Rewrite: -{1 x}(f_finv (Iedge g)); Exact (HkE ?).
Rewrite: -{1 x}(f_finv (Inode g)); Exact (HkN ?).
Qed.

Lemma four_colorable_dual :
  (four_colorable (dual g)) <-> (graph_four_colorable g).
Proof. Split; Move=> [k Hk]; Exists k; Case (coloring_dual k); Auto. Qed.

Lemma coloring_mirror : (k : g -> color) (!coloring (mirror g) k) -> (coloring k).
Proof.
Move=> k [HkE' HkF']; Step HkF: (invariant face k) =1 g.
  Move=> x; Rewrite: /invariant eqd_sym -{1 x}(finv_f (Iface g)); Apply: HkF'.
Split; Move=> // x; Rewrite: /invariant eqd_sym.
Rewrite: -(? =P (k x) (HkF ?)) -(? =P (k (edge x)) (HkF ?)) -{1 x}Eedge.
Apply: HkE'.
Qed.

Lemma colorable_mirror : (four_colorable (mirror g)) -> (four_colorable g).
Proof. By Move=> [k Hk]; Exists k; Apply coloring_mirror. Qed.

End ColoringDual.

Section EqmColorable.

Variables g, g' : hypermap.
Hypothesis Eg': g =m g'.

Lemma eqm_colorable : (four_colorable g) -> (four_colorable g').
Proof.
Case: {}g {}Eg' => [d e n f EgE] [e' n' f' Eg'E Ee _ Ef] [k [HkE HkF]]; Exists k.
Split; Move=> x; Rewrite: /invariant /= -?Ee -?Ef; [Apply: HkE | Apply: HkF].
Qed.

Lemma eqm_graph_colorable : (graph_four_colorable g) -> (graph_four_colorable g').
Proof.
Case: {}g {}Eg' => [d e n f EgE] [e' n' f' Eg'E Ee En _] [k [HkE HkN]]; Exists k.
Split; Move=> x; Rewrite: /invariant /= -?Ee -?En; [Apply: HkE | Apply: HkN].
Qed.

End EqmColorable.

Section DecideColorable.

Variable g : hypermap.

(* We need decidability of ring traces in birkhoff.                           *)
Lemma decide_ring_trace : (r : (seq g); et : colseq)
  {(ring_trace r et)} + {~(ring_trace r et)}.
Proof.
Move=> r et.
Pose kpr := [k;p;lc](andb (maps k p) =d lc <(seqData ?)>(trace (maps k r)) =d et).
Pose ekpr := [p;lc](EX k | (coloring k) & (kpr k p lc)).
Cut {(ekpr seq0 seq0)} + {~(ekpr seq0 seq0)}.
  Move=> [Hk | Hnk]; [Left | Right].
    Move: Hk => [k Hk Det]; Exists k; Auto; Exact (esym (eqseqP Det)).
  By Move=> [k Ht Det]; Case Hnk; Exists k; Auto; Rewrite: /kpr Det !set11.
Def Dn: n := (card (setC (Seq0 g))).
Elim: n (Seq0 g) (seq0 :: colseq) Dn => [|n Hrec] p lc Dn.
  Step Hp: (x : g) (p x) By Exact [x](negbEf (card0_eq (esym Dn) x)).
  Pose kp := [x](sub Color0 lc (index x p)).
  Pose kkp := [x](setU1 (kp (edge x)) (setC1 (kp (face x))) (kp x)).
  Case Hkp: (andb (set0b kkp) (kpr kp p lc)).
    Case/andP: Hkp => [Hkp Det]; Left; Exists kp; Auto.
    Split; Move=> x; Case/norP: (set0P Hkp x) => [HxE HxF].
      Exact (negbE HxE).
    Exact (negbE2 HxF).
  Right; Case; Move=> k [HkE HkF]; Case/andP=> [Dlc Det].
  Step Dkp: kp =1 k.
    Move=> x; Rewrite: /kp -(eqP Dlc).
    Apply: (etrans (sub_maps x ? ? ?)); LeftBy Rewrite: /= index_mem.
    By Rewrite sub_index.
  Rewrite: /kpr !(eq_maps Dkp) Dlc Det /= andbT in Hkp; Case/set0Pn: Hkp.
  Move=> x; Rewrite: /kkp /setU1 /setC1 !Dkp.
  By Rewrite: -/(invariant edge k x) -/(invariant face k x) HkE HkF.
Case: (pickP (setC p)) => [x Hx | Hp]; RightBy Rewrite (eq_card0 Hp) in Dn.
Pose ekprx := [c](ekpr (Adds x p) (Adds c lc)).
Step Hekprx: (c : color) {(ekprx c)} + {~(ekprx c)}.
  Move=> c; Apply: Hrec. Rewrite: (cardD1 x) Hx in Dn; Injection: Dn => Dn.
  By Rewrite Dn; Apply: eq_card => [y]; Rewrite: /= /setU1 /setC negb_orb.
Step Hekpr: (c : color) (ekprx c) -> (ekpr p lc).
  Move=> c [k Hk Hkpr]; Rewrite: /kpr {1}/eqd /= -andbA in Hkpr.
  By Case (andP Hkpr); Exists k.
Case (Hekprx Color0); [Left; EAuto | Move=> Hc0].
Case (Hekprx Color1); [Left; EAuto | Move=> Hc1].
Case (Hekprx Color2); [Left; EAuto | Move=> Hc2].
Case (Hekprx Color3); [Left; EAuto | Move=> Hc3].
Right; Move=> [k Hk Hkpr]; Cut (ekprx (k x)); LeftBy Case (k x).
By Exists k; RightBy Rewrite: /kpr {1}/eqd /= set11.
Qed.

Lemma decide_colorable : {(four_colorable g)} + {~(four_colorable g)}.
Proof.
Case: (decide_ring_trace (Seq0 g) seq0::colseq) => [Hk | Hnk].
  By Left; Move: Hk => [k Hk _]; Exists k.
By Right; Move=> [k Hk]; Case: Hnk; Exists k.
Qed.

End DecideColorable.

Section MinimalCounterExample.

Variable g : hypermap.

Record minimal_counter_example : Prop :=
  MinimalCounterExample {
    minimal_counter_example_is_planar_bridgeless_plain_precubic :>
      (planar_bridgeless_plain_precubic g);
    minimal_counter_example_is_noncolorable :
      ~(four_colorable g);
    minimal_counter_example_is_minimal :
      (g' : hypermap) (planar_bridgeless_plain_precubic g') ->
        (ltn (card g') (card g)) -> (four_colorable g')
  }.

Lemma minimal_counter_example_is_cubic : minimal_counter_example -> (cubic g).
Proof.
Move=> Hg; Def: Hbg := (bridgeless_cface Hg).
Def: HgE : (plain g) := Hg; Def: HgN := (precubic_leq Hg).
Apply/subsetP=> [x _]; Apply/negPf=> [Hx].
Case Hxnx: (x =d (node x)).
  By Case/idP: (Hbg x); Rewrite: {2 x}(eqP Hxnx) cface1r Enode connect0.
Step Dnnx: (node (node x)) = x.
  Rewrite: /order_set in Hx; Apply: eqP; Apply/negPf => [Hnnx].
  Move: (HgN x); Rewrite: leq_eqVlt Hx /order.
  Rewrite: (cardD1 x) (cardD1 (node x)) (cardD1 (node (node x))).
  By Rewrite: /setD1 -!cnode1r connect0 (inj_eqd (Inode g)) Hxnx eqd_sym Hnnx.
Pose g' := (walkupE x); Pose h' := [u : g'](subdE u).
Pose unx := ((subdI 2!(setC1 x) (negbI Hxnx)) :: g').
Pose g'' := (walkupE unx); Pose h'' := [w : g''](subdE w).
Pose h := [w](h' (h'' w)).
Step Hh' : (injective h') By Exact (subdE_inj 2!?).
Step Hh'' : (injective h'') By Exact (subdE_inj 2!?).
Step Hh : (injective h) By Exact (inj_comp Hh' Hh'').
Step HhF : (w1, w2 : g'') (cface w1 w2) = (cface (h w1) (h w2)).
  Move=> w1 w2; Apply: (etrans ? (fconnect_skip (Iface ?) ? ?)). 
  Exact (fconnect_skip (Iface ?) ? ?).
Step HhN : (w1, w2 : g'') (cnode w1 w2) = (cnode (h w1) (h w2)).
  Move=> w1 w2; Refine (etrans ? (fconnect_skip (Inode ?) ? ?)). 
  Exact (fconnect_skip (Inode ?) ? ?).
Step HhN1 : (w : g'') (h (node w)) = (node (h w)).
  Move=> w; Pose nw' := (walkupI unx (node (h w))); Pose nw := (walkupI w nw').
  Step Dnw': (h' nw') = (node (h w)).
    Rewrite: /h' /nw' walkupI_eq -{1 x}Dnnx (inj_eqd (Inode g)).
    By Case Hnxw: ((node x) =d (h w)); LeftBy Case: (negP (subd_mem w)).
  Step Dnw: (h nw) = (node (h w)).
    Rewrite: /nw {1}/h /h'' walkupI_eq -(inj_eqd Hh') Dnw' /= (inj_eqd (Inode g)).
    By Case Hxhw: (x =d (h w)); LeftBy Case (negP (subd_mem (h'' w))).
  By Rewrite: -Dnw; Congr h; Symmetry; Do 2 Apply: (subdE_skip (Inode ?)).
Step Hg''g : (ltn (card g'') (card g)).
  By Rewrite: /g'' /g' !card_walkup (cardD1 x) /= -subn1 add1n ltnS leq_subr.
Step Hh''E: (w : g'') (order edge w) = (card (setD1 (cedge (h'' w)) unx)).
  Move=> w; Rewrite: /order -(card_image Hh''); Refine (eq_card [u]?).
  Rewrite: /setD1; Case Hu: (negb unx =d u).
    Pose wu := ((subdI 2!(setC1 unx) Hu) :: g'').
    Rewrite: {1 u}(erefl (h'' wu)) (image_f Hh'') /=.
    Refine (etrans (eq_fconnect (glink_fp_skip_edge ?) w wu) ?).
      By Rewrite: /glink /relU /setU /eqdf /eqd /= /skip1 Dnnx !set11 /= orbT.
    Exact (fconnect_skip (Iedge ?) w wu).
  Apply/set0Pn; Case; Move=> wu; Move/andP => [Du _]; Case/idPn: Hu.
  Rewrite: (u =P ? Du); Exact (subd_mem wu).
Case: (!minimal_counter_example_is_minimal Hg g'') => //; Try By Apply ltnW.
  Repeat Split.
        By Do 2 Apply: planar_walkupE; Exact Hg.
      Apply/set0P=> [w]; Rewrite: -{1 w}Eedge cface1r HhF HhN1.
      By Def: y := (h (face (edge w))); Rewrite: -{2 y}Enode -cface1r Hbg.
    Apply/subsetP=> [w _]; Rewrite: /order_set.
    Rewrite: Hh''E ; Pose u := (h'' w).
    Case Hu: (negb (has (cedge (h' u)) (seq2 x (node x)))).
      Rewrite: -(eqnP (subsetA HgE (h w))) -(card_image Hh').
      Apply/eqP; Apply: eq_card => [y].
      Case Hy: (setC1 x y).
        Pose v := ((subdI Hy) :: g').
        Rewrite: -{1 y}/(h' v) (image_f Hh') /= /setD1 /eqd /=.
        Case: ((node x) =P y) => [Dnx | _].
          Symmetry; Apply: negbE.
          By Rewrite: /= orbF Dnx in Hu; Case: (norP Hu).
        Exact (same_cskip_edge Hu v).
      Case/norP: Hu; Move/negPf=> H _; Case/eqP: {y}Hy; Rewrite: /h -/u ~H.
      By Apply/set0Pn=> [[v H]]; Case/andP: H => [Dv _]; Case/idP: (subd_mem v).
    Step HxX: (negb (cross_edge x)).
      Move: Hu; Rewrite: /= orbF /cross_edge Sedge !fconnect_orbit /orbit.
      Rewrite: ![y](eqnP (subsetA HgE y)) /= /setU1 !orbF Hxnx.
      Move=> H; Apply/eqP=> [Dnx]; Move: H; Rewrite: -Dnx (inj_eqd (Iedge g)).
      Rewrite: orbA orbC !orbA eqd_sym orbb -orbA orbC eqd_sym orbb eqd_sym Dnx.
      By Case/orP=> [Dx | Dex];
        [Case (negP (subd_mem w)) | Case (negP (subd_mem u))].
    Move: (cardD1 unx (cedge u)).
    Rewrite: (cskip_edge_merge HxX unx (negbEf Hu)) /= connect0 /= orbT /=.
    Rewrite: -2!eqdSS add1n; Case; Move: (cardUI (cedge x) (cedge (node x))).
    Rewrite: -/(order edge x) -/(order edge (node x)).
    Rewrite: ![z](eqnP (subsetA HgE z)) addnC /addn /=.
    Step HxnxI: (setI (cedge x) (cedge (node x))) =1 set0.
      Move=> y; Apply/andP=> [[Hyx Hynx]].
      By Case/idP: HxX; Rewrite: /cross_edge (same_cedge Hyx) Sedge.
    Rewrite: (eqnP (introT set0P HxnxI)) /= (cardD1 x) {1}/setU connect0.
    Rewrite: /= add1n; Case; Rewrite: eqdSS -(card_image Hh').
    Apply/eqP; Apply: eq_card => [y]; Rewrite: /setD1.
    Case Hy: (negb x =d y).
      Pose v := ((subdI 2!(setC1 x) Hy) :: g').
      Rewrite: -{1 y}/(h' v) (image_f Hh') /= /setU.
      Refine (etrans (cskip_edge_merge HxX v (negbEf Hu)) ?).
      By Rewrite: /= orbF !(Sedge g y).
    Apply/set0Pn=> [[v H]]; Case/andP: H => [Dv _].
    By Case (negP (subd_mem v)); Rewrite: {1 x}(eqP (negbEf Hy)).
  Apply/subsetP=> [w _]; Rewrite: /order_set.
  Apply: leq_trans (HgN (h w)); Rewrite: leq_eqVlt; Apply/orP; Left.
  Rewrite: /order -(card_image Hh); Apply/eqP; Apply: eq_card => [y].
  Step HxN: (fcycle (!node?) (seq2 x (node x))).
    By Rewrite: /= /eqdf Dnnx !set11.
  Case Hxy: (cnode x y).
    Transitivity false.
      Apply/set0Pn=> [[wy H]]; Case/andP: H => [Dy _].
      Rewrite: (fconnect_cycle HxN (setU11 ? ?)) /= /setU1 orbF in Hxy.
      Rewrite: (eqP Dy) in Hxy; Case/orP: Hxy => [Hxy | Hnxy].
        By Case (negP (subd_mem (h'' wy))).
      By Case (negP (subd_mem wy)).
    Rewrite: Snode -(same_cnode Hxy) (fconnect_cycle HxN (setU11 ? ?)) /=.
    Rewrite: /setU1 orbF; Symmetry; Apply/norP.
    Split; [Exact (subd_mem (h'' w)) | Exact (subd_mem w)].
  Rewrite: (fconnect_cycle HxN (setU11 ? ?)) /= /setU1 orbF in Hxy.
  Case/norP: Hxy => [Hxy Hnxy].
  Pose wy := (subdI 2!(setC1 unx) 3!(subdI 2!(setC1 x) Hxy) Hnxy).
  By Rewrite: -{1 2 y}/(h wy) (image_f Hh) HhN.
Move=> k [HkE HkF]; Case: (minimal_counter_example_is_noncolorable Hg).
Pose a' := [y; w](cface y (h w)).
Step Ha'x : (y : g) (a' y) =1 set0 -> (set2 x (node x) y).
  Move=> y Ha'y; Apply/norP=> [[Hxy Hnxy]].
  Pose wy := (subdI 2!(setC1 unx) 3!(subdI 2!(setC1 x) Hxy) Hnxy).
  By Case/idP: (Ha'y wy); Rewrite: /a' /= connect0.
Step Ha'F : (y : g) (a' y) =1 set0 -> (z : g) (cface y z) -> y = z.
  Move=> y Ha'y z Hyz.
  Step Hz : (set2 x (node x) z).
    Apply Ha'x; Move=> w; Rewrite: /a' -(same_cface Hyz); Exact (Ha'y w).
  Case Hynz: (set2 y (node y) z).
    Case/orP: Hynz; Move=> Dz; LeftBy Apply: eqP.
    By Rewrite: -{1 y}Enode (eqP Dz) -cface1 Sface Hbg in Hyz.
  Case/idP: Hynz; Rewrite: /set2.
  By Case/orP: (Ha'x ? Ha'y); Case/eqP => //; Rewrite: orbC Dnnx.
Pose k' := [y]if pick z in (a' y) then (k z) else
              if y =d x then Color0 else Color1.
Step HkFF: (w, w' : g'') (cface w w') -> (k w) = (k w').
  Move=> w w'; Move/connectP=> [p Hp []] {w' Hw Hw'}.
  Elim: p w Hp => // [fw p Hrec] w; Move/andP=> [Dfw Hp].
  Rewrite: -(eqcP (HkF w)) ((face w) =P ? Dfw); Exact (Hrec ? Hp).
Step Hk'F: (y, z : g) (cface y z) -> (k' y) = (k' z).
  Move=> y z Hyz; Rewrite: /k'.
  Case: (pickP (a' y)) => [w Hw | Hy].
    Rewrite: /a' (same_cface Hyz) in Hw.
    Case: (pickP (a' z)) => [w' Hw' | Hz].
      By Apply HkFF; Rewrite: HhF -(same_cface Hw).
    By Case/idP: (Hz w).
  Rewrite: -(Ha'F ? Hy ? Hyz).
  By Case: (pickP (a' y)) => [w Hw | _]; LeftBy Case/idP: (Hy w).
Step Hk'E: (y : g) (negb (set2 x (node x) y)) -> ~ (k' y) = (k' (edge y)).
  Move=> y; Move/norP=> [Hxy Hnxy].
  Pose w := ((subdI 2!(setC1 unx) 3!(subdI 2!(setC1 x) Hxy) Hnxy) :: g'').
  Step Dfey: (face (edge y)) = (h (face (edge w))).
    By Apply Inode; Rewrite: -HhN1 !Eedge.
  Rewrite: (Hk'F (edge y) ? (fconnect1 ? ?)) /k'.
  Case: (pickP (a' y)) => [w' Hw' | Hy];
    RightBy Case/idP: (Hy w); Rewrite: /a' /= connect0.
  Case: (pickP (a' (face (edge y)))) => [w'' Hw'' | Hfey];
    RightBy Case/idP: (Hfey (face (edge w))); Rewrite: /a' Dfey /= connect0.
  Move=> Hkw; Case/eqcP: (HkE w); Rewrite: -(eqcP (HkF (edge w))); Symmetry.
  By Apply: (etrans (etrans ? Hkw)); Apply HkFF; Rewrite: HhF // -Dfey Sface.
Exists k'.
Split; RightBy Move=> y; Apply/eqP; Apply: Hk'F; Rewrite: Sface fconnect1.
Move=> y; Apply/eqcP.
Case Hy: (set2 x (node x) y); RightBy Apply nesym; Apply Hk'E; Apply negbI.
Def: De2y := (plain_eq Hg y).
Case Hey: (set2 x (node x) (edge y));
  RightBy Rewrite: -{2 y}De2y; Apply Hk'E; Apply negbI.
Rewrite: /k'; Case: (pickP (a' y)) => [w Hw | _].
  Step Hfy: (set2 x (node x) (face y)).
    By Rewrite: -De2y /set2 -!(monic2F_eqd (Enode g)) Dnnx orbC.
  Step HyF : (fcycle (!face?) (seq1 y)).
    Case HyN : (set2 y (node y) (face y)).
      Case: (orP HyN); Move/eqP=> Dfy; LeftBy Rewrite: /= /eqdf -Dfy set11.
      By Case/idP: (Hbg (node y)); Rewrite: cface1r Enode Sface Dfy fconnect1.
    Case/idP: HyN; Rewrite: /set2.
    By Case: (orP Hy); Move/eqP=> Dy; Rewrite: -{1 3 y}Dy // orbC Dnnx.
  Rewrite: /a' (fconnect_cycle HyF (setU11 ? ?)) /= /setU1 orbF in Hw.
  Rewrite: (eqP Hw) in Hy.
  Case: (orP Hy); Move=> Dy; LeftBy Case (negP (subd_mem (h'' w))).
  By Case (negP (subd_mem w)).
Case: (pickP (a' (edge y))) => [w Hw | Ha'ey].
  Step Hfey: (set2 x (node x) (face (edge y))).
    By Rewrite: /set2 -!(monic2F_eqd (Enode g)) Dnnx orbC.
  Step HyF : (fcycle (!face?) (seq1 (edge y))).
    Case HyN : (set2 (edge y) (node (edge y)) (face (edge y))).
      Case: (orP HyN); Move/eqP=> Dfey; LeftBy Rewrite: /= /eqdf -Dfey set11.
      Case/idP: (Hbg (node (edge y))).
      By Rewrite: cface1r Enode Sface Dfey fconnect1.
    Case/idP: HyN; Rewrite: /set2; Case: (orP Hey); Move=> Dey;
      By Rewrite: -{1 3 (edge y)}(eqP Dey) // orbC Dnnx.
  Rewrite: /a' (fconnect_cycle HyF (setU11 ? ?)) /= /setU1 orbF in Hw.
  Rewrite: (eqP Hw) in Hey.
  Case: (orP Hey); Move=> Dey; LeftBy Case (negP (subd_mem (h'' w))).
  By Case (negP (subd_mem w)).
Move: Hy; Rewrite: (eqd_sym y) /set2; Case: (x =P y) => [[]|_] /= Dy.
  By Rewrite: plain_neq.
By Rewrite: (Ha'F ? Ha'ey ? (fconnect1 ? ?)) -(eqP Dy) Enode set11.
Qed.

Coercion minimal_counter_example_is_cubic : minimal_counter_example >-> cubic.

End MinimalCounterExample.

(* Used for symmetry disposition, and flipped configuration match. *)
Lemma minimal_counter_example_mirror : (g : hypermap)
  (minimal_counter_example g) -> (minimal_counter_example (mirror g)).
Proof.
Move=> g; Do 4 Case; Move=> Hpg Hbg HgE HgN Hkg Htg.
Split; Auto; RightBy Move=> Hkmg; Case Hkg; Apply colorable_mirror.
Split; RightBy Rewrite: precubic_mirror.
Split; RightBy Rewrite: plain_mirror.
Split; RightBy Rewrite: bridgeless_mirror.
By Rewrite: planar_mirror.
Qed.

Section ConfigurationProperties.

Variables n0 : nat; g : hypermap; r, cc : (seq g).

(* We state and prove separately the geometrical and semantic requirements  *)
(* on configurations. The former ("embeddable") are established by the quiz *)
(* construction; the latter ("c_reducible") by the reducibility check.      *)
(* The geometrical requirements are that configuration maps must be plain   *)
(* quasicubic planar bridgeless maps with a simple ring, that satisfy two   *)
(* additional conditions: the ring faces arities must be in the 3..6 range, *)
(* and the kernel must have radius 2. These two additional properties are   *)
(* used in embed.v to extend a partial hypermap morphism into an embedding. *)

Definition good_ring_arity [x : g] : bool :=
  (set4 (3) (4) (5) (6) (arity x)).

Section Radius2.

(* Since our configuration maps have at most one "bridge" face, we can use *)
(* a slightly more restrictive definition of "radius 2" : we insist that   *)
(* every region is a exactly two adj "hops" away from the center rather    *)
(* than just "at most two" (the extra requirement will always be met,      *)
(* because we can always take a detour through an adjacent spoke.          *)
(* The waeker definition is more complex, and in particular it's eaasier   *)
(* to check the stricter condition on the configurations' data.            *)

Variable a : (set g).

Definition at_radius2 [x, y : g] : bool :=
  (negb (disjoint (adj y) (setI (adj x) a))).

Lemma at_radius2P : (fclosed face a) -> (x, y : g)
  (reflect (EX x' | (EX y' | (cface x x') /\ (cface y y')
                           & (a (edge x')) /\ (cface (edge x') (edge y'))))
     (at_radius2 x y)).
Proof.
Move=> HaF x y; Apply: (iffP set0Pn); Case.
  Move=> z; Case/and3P; Move/adjP=> [y' Hyy' Hy'z]; Move/adjP=> [x' Hxx' Hx'z] Haz.
  Exists x'; Exists y'; Auto; Split; LeftBy Rewrite: (closed_connect HaF Hx'z).
  By Rewrite: (same_cface Hx'z) Sface.
Move=> x' [y' [Hxx' Hyy'] [Haex' Hexy']]; Exists (edge x').
By Rewrite: /setI (adjF Hxx') (adjF Hyy') (adjFr Hexy') !adjE.
Qed.

Definition radius2 : bool := (negb (disjoint a [x](subset a (at_radius2 x)))).

Lemma radius2P : (reflect (EX x | (a x) & (sub_set a (at_radius2 x))) radius2).
Proof.
Apply: (iffP set0Pn); Case=> [x].
  By Case/andP=> [Hx]; Move/subsetP; Exists x.
By Move=> Hx Ha; Exists x; Rewrite: /setI ~Hx; Apply/subsetP.
Qed.

End Radius2.

Record embeddable : Prop :=
  Embeddable {
    embeddable_base :> (scycle_planar_bridgeless_plain_quasicubic_connected r);
    embeddable_ring : (all good_ring_arity r);
    embeddable_kernel : (radius2 (kernel r))
  }.

Definition sparse [p : (seq g)] : bool := (!simple (permF g) p).

Lemma sparse_adds : (x : g; p : (seq g))
  (sparse (Adds x p)) = (andb (negb (has (cnode x) p)) (sparse p)).
Proof. Exact (!simple_adds (permF g)). Qed.

Lemma sparse_catC : (p1, p2 : (seq g)) (sparse (cat p1 p2)) = (sparse (cat p2 p1)).
Proof. Exact (!simple_catC (permF g)). Qed.

Lemma sparse_catCA : (p1, p2, p3 : (seq g))
  (sparse (cat p1 (cat p2 p3))) = (sparse (cat p2 (cat p1 p3))).
Proof. Exact (!simple_catCA (permF g)). Qed.

Lemma sparse_rot: (p : (seq g)) (sparse (rot n0 p)) = (sparse p).
Proof. Exact (!simple_rot n0 (permF g)). Qed.

Definition triad [p : (seq g); x : g] : bool :=
  (andb (ltn (2) (count [y](fband p (edge y)) (orbit face x)))
        (negb (subset p (adj x)))).

Record valid_contract : Prop :=
  ValidContract {
    valid_contract_is_off_ring : (disjoint r (insertE cc));
    valid_contract_is_sparse : (sparse (insertE cc));
    valid_contract_size : (set4 (1) (2) (3) (4) (size cc));
    valid_contract_triad :
      (size cc) = (4) -> (negb (disjoint (kernel r) (triad (insertE cc))))
  }.
        
Record c_reducible : Prop :=
  Creducible {
    c_reducible_base :> valid_contract;
    c_reducible_coclosure : (et : colseq)
      (cc_ring_trace cc (rev r) et) -> (kempe_coclosure (ring_trace (rev r)) et)
  }.

End ConfigurationProperties.

Syntax constr level 0 :
  map_sparse_pp [(sparse 1!$_)] -> ["sparse"]
| map_good_ring_arity_pp [(good_ring_arity 1!$_)] -> ["good_ring_arity"].

Grammar constr constr0 : constr :=
  map_sparse ["sparse"] -> [(!sparse ?)]
| map_good_ring_arity ["good_ring_arity"] -> [(!good_ring_arity ?)].

Section Preembedding.

(* The properties of the partial morphism contructed in quiz, and extended  *)
(* to an embedding in embed. The morphism is only defined on the kernel of  *)
(* the configuration. On this subset, it should be a strict morphism for    *)
(* face and arity. The darts on which it commutes with edge should form an  *)
(* rlink-connected cover of the kernel, up to cface.                        *)

Variables g, g' : hypermap; a : (set g); h : g -> g'.

Definition edge_central [x : g] : bool := (h (edge x)) =d (edge (h x)).

Lemma edge_central_edge : (plain g) -> (plain g') ->
  (x : g) (edge_central (edge x)) = (edge_central x).
Proof.
Move=> HgE Hg'E x; Rewrite: /edge_central eqd_sym plain_eq //.
By Rewrite: (monic2F_eqd (plain_eq Hg'E)).
Qed.

Record preembedding : Prop :=
  Preembedding {
    preembedding_face : (x : g) (a x) -> (h (face x)) = (face (h x));
    preembedding_arity : (x : g) (a x) -> (arity (h x)) = (arity x);
    preembedding_cover : (subset a (fclosure face edge_central));
    preembedding_rlinked : (rlink_connected (setI a edge_central))
  }.

Lemma preembedding_simple_path :
  preembedding -> (fclosed face a) ->
  (x, y : g) (a (edge x)) -> (a y) ->
  (EX p | (and3 (path rlink x p) (cface (last x p) y) (negb p =d seq0))
        & (simple p) /\ (all (setI a edge_central) p)).
Proof.
Move=> [_ _ HhaF HhaE] HaF x y Hx Hy; Pose a' := (setI a edge_central).
Case/set0Pn: (subsetP HhaF ? Hx) => [x']; Move/andP=> [Hxx' Hx'E].
Case/set0Pn: {HhaF}(subsetP HhaF ? Hy) => [y']; Move/andP=> [Hyy' Hy'E].
Step Hx': (a' x') By Rewrite: /a' /setI -(closed_connect HaF Hxx') Hx.
Step Hy': (a' y') By Rewrite: /a' /setI -(closed_connect HaF Hyy') Hy.
Case: {HhaE}(HhaE ? ? Hx' Hy') => [p Hp Hpa']; Rewrite: -/a' in Hpa'.
Step Hxp: (path rlink x (add_last p y')).
  By Move: Hp; Rewrite: headI /= {1}/rlink Eface -(same_cface Hxx').
Case: (simplify_rlink Hxp) => [p' [Hp' Up'] [Ep' Ep'0 Hpp']].
Exists p'; Split; Try By Rewrite: -?Ep'0 1?headI.
  By Rewrite: -Ep' last_add_last Sface.
Rewrite: -!subset_all in Hpp' *; Apply: (subset_trans Hpp').
By Rewrite: subset_all -cats1 all_cat Hpa' /= Hy'.
Qed.

End Preembedding.

Unset Implicit Arguments.
