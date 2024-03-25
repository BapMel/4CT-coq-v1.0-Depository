(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require tacticext.
Require boolprop.
Require funs.
Require dataset.
Require natprop.
Require seq.
Require paths.
Require finset.
Require connect.
Require znat.
Require hypermap.
Require geometry.
Require color.
Require coloring.
Require patch.
Require snip.
Require grid.
Require matte.

Set Implicit Arguments.

Section GridMap.

(* The construction of a hypermap, from a finite set of disjoint mattes and *)
(* a set of adjacency boxes. These sets are simply represented by functions *)
(* on `nat' integers. The construction starts by extending the mattes so    *)
(* that mattes that meet a common adjacency box share a contour edge. Then  *)
(* we compute a bounding box for the mattes, and create a plain planar      *)
(* connected hypermap by framing the bounding box. The matte rings then map *)
(* to simple rings of this map with disjoint disks, so we can use the       *)
(* "snip" operation to turn them into node rings (we need to operate in the *)
(* dual map to make this work), by removing their interiors. Dualizing the  *)
(* resulting hypermap gives us a map whose coloring solves the initial      *)
(* coloring problem.                                                        *)

Definition cmatte : Set := nat -> matte.
Definition adjbox : Set := nat -> nat -> grect.

Variables nbreg : nat; ab0 : adjbox; cm0 : cmatte.

Definition regpair [i, j : nat] : bool := (andb (ltn i j) (ltn j nbreg)).

Definition cm_mem [cm : cmatte] : gpointset :=
  [p](iter_n nbreg [i](orb (cm i p)) false).

Definition cm_proper [cm : cmatte] : Prop :=
  (i, j : nat) (regpair i j) -> (negb (has (cm i) (cm j))).

Definition ab_adj [ab : adjbox; i, j : nat] : bool :=
  (ltn (0) (garea (ab i j))).

Definition ab_proper [ab : adjbox] : Prop :=
  (i1, j1, i2, j2 : nat) (regpair i1 j1) -> (regpair i2 j2) ->
    (p : gpoint) (ab i1 j1 p) -> (ab i2 j2 p) -> i1 = i2 /\ j1 = j2.

Definition ab_cm_proper [ab : adjbox; cm : cmatte] : Prop :=
  (i, j : nat) (regpair i j) -> (ab_adj ab i j) ->
    (and (has (inset (ab i j)) (cm i))
         ([k](andb (ltn k nbreg) (has (ab i j) (cm k)))) =1 (set2 i j)).

Hypotheses Hab0 : (ab_proper ab0); Hcm0 : (cm_proper cm0).
Hypothesis Habcm0 : (ab_cm_proper ab0 cm0).

(* We first do a global refinement, so that we can use the extend_meet lemma. *)
(* This operation will also be used in the topological construction, to       *)
(* rescale the mattes and boxes.                                              *)

Definition refine_cmatte : cmatte := [i](refine_matte (cm0 i)).
Definition refine_adjbox : adjbox := [i, j](refine_rect (ab0 i j)).

Syntactic Definition cm1 := refine_cmatte.
Syntactic Definition ab1 := refine_adjbox.

Lemma cm_proper_refine : (cm_proper cm1).
Proof.
Move=> i j Hij; Apply/hasPn=> [p].
Rewrite: /refine_cmatte /= !mem_refine_mdisk; Apply: (hasPn (Hcm0 Hij)).
Qed.

Lemma refine_cmatte_refined : (i, j : nat)
  (refined_in (cm1 i)::(set ?) (ab1 i j)).
Proof. Move=> *; Apply: (!refine_matte_refined). Qed.

Lemma ab_proper_refine : (ab_proper ab1).
Proof.
Move=> i1 j1 i2 j2 Hij1 Hij2 p; Rewrite: /refine_adjbox !mem_refine_rect.
Apply: (Hab0 Hij1 Hij2).
Qed.

Lemma ab_adj_refine : (ab_adj ab1) =2 (ab_adj ab0).
Proof.
Move=> i j; Rewrite: /ab_adj /refine_adjbox garea_refine_rect.
By Case (garea (ab0 i j)).
Qed.

Lemma ab_cm_proper_refine : (ab_cm_proper ab1 cm1).
Proof.
Move=> i j Hij; Rewrite: ab_adj_refine; Case/(Habcm0 Hij) => [Habcmi Habij].
Split.
  Case/hasP: Habcmi => [q Hcmq Habq]; Apply/hasP; Exists (addg q q).
    By Rewrite: /refine_cmatte mem_refine_matte halfg_double.
  Step Hab1q: (inset2 (ab1 i j) (addg q q)); RightBy Case/andP: Hab1q.
  By Apply: inset2_refine; Rewrite halfg_double.
Move=> k; Rewrite: -Habij /refine_cmatte /refine_adjbox; Congr andb.
Apply/hasP/hasP=> [[q Hcmq Habq]].
  By Rewrite: mem_refine_matte mem_refine_rect in Hcmq Habq; Exists (halfg q).
By Exists (addg q q); Rewrite: ?mem_refine_matte ?mem_refine_rect halfg_double.
Qed.

(* The second stage of the construction eliminates the adjbox data by        *)
(* entending the mattes so that they meet in each box.                       *)

Definition cm_adj [cm : cmatte; i, j : nat] : bool :=
  (has [p](mring (cm i) (gedge p)) (mring (cm j))).

Definition subregpair [i1, j1, i2, j2 : nat] : bool :=
  if j2 =d j1 then (ltn i2 i1) else (andb (ltn i2 j2) (ltn j2 j1)).

Lemma cm_extend_meet : {cm2 : cmatte | (cm_proper cm2)
       & (i, j : nat) (regpair i j) -> (ab_adj ab1 i j) -> (cm_adj cm2 i j)}.
Proof.
Cut {cm : cmatte | (cm_proper cm) /\ (ab_cm_proper ab1 cm)
      & (i, j : nat) (regpair i j) ->
        if (subregpair nbreg nbreg i j) then
               (ab_adj ab1 i j) -> (cm_adj cm i j)
        else (refined_in (cm j)::(set ?) (ab1 i j))}.
  Move=> [cm [Hcm _] Hadj]; Exists cm; LeftDone.
  Move=> i j Hij; Move: (Hadj ? ? Hij); Rewrite: /regpair in Hij.
  Case: (andP Hij); Clear; Rewrite: ltn_neqAle; Move/andP=> [Hj _].
  By Rewrite: /subregpair (negbE Hj) Hij.
Elim: {}nbreg => [|j1 Hrecj] /=.
  Exists cm1; LeftBy Split; [Exact cm_proper_refine | Exact ab_cm_proper_refine].
  Move=> i [|j] // _; Rewrite: /subregpair andbF; Apply: (!refine_matte_refined).
Elim: {-2}(S j1) => [|i1 Hreci].
  Case: Hrecj => [cm Hcm Hadj]; Exists cm; Auto.
  Move=> i j Hij; Move: {Hadj}(Hadj ? ? Hij); Rewrite: /subregpair.
  Case: (j =P (S j1)) => [Dj | _].
    By Rewrite: Dj eqn_leq !ltnn /= andbC ltn_neqAle ltnn andbF.
  By Rewrite: ltnS (leq_eqVlt j); Case: (j =P j1) => [[] | _] //; Rewrite andbT.
Move/S: j1 Hreci {Hrecj} => j1 [cm Hcm Hadj].
Case Hij1: (negb (andb (regpair i1 j1) (ab_adj refine_adjbox i1 j1))).
  Exists cm; LeftDone.
  Move=> i j Hij; Move: (Hadj ? ? Hij); Rewrite: /subregpair ltnS (leq_eqVlt i).
  Case: (j =P j1) => // [Dj]; Case: (i =P i1) => //= [Di] _ Haij.
  By Case/idP: Hij1; Rewrite: -Dj -Di Hij.
Case/andP: Hij1 Hcm => [Hij1 Haij1] [Hcm Habcm].
Case: (Habcm ? ? Hij1 Haij1) {Haij1}; Pose r1 := (ab1 i1 j1).
Move=> Hr1i1 Hr1; Step Hr1j1: (has r1 (cm j1)).
  By Move: (Hr1 j1); Rewrite set22; Case/andP.
Step Hr1cm: (refined_in (cm j1)::(set ?) (refine_adjbox i1 j1)).
  By Move: (Hadj ? ? Hij1); Rewrite: /subregpair set11 ltnn.
Case: (extend_meet Hr1cm Hr1j1 Hr1i1); LeftBy Rewrite: has_sym; Apply Hcm.
Rewrite: -/r1; Move=> xm [Hxm Hxmr] Hxmi.
Pose xcm := [i](if i =d j1 then xm else (cm i)).
Step Excm: (i : nat) (sub_set (cm i) (xcm i)).
  By Move=> i; Rewrite: /xcm; Case: (i =P j1); [Case/esym | Move=> _ q].
Step Hxcm: (cm_proper xcm) /\ (ab_cm_proper ab1 xcm).
  Split; Move=> i j Hij; Case: (andP Hij) => [Hi Hj];
    Rewrite: ltn_neqAle in Hi; Case/andP: Hi => [Hi _].
    Rewrite: /xcm; Case: (j =P j1) => [Dj | _].
      Rewrite: -Dj (negbE Hi); Apply/hasP=> [[p Hxmp Hip]].
      Case/andP: (Hxmr ? Hxmp) => [Hi1p]; Case/orP=> [Hp].
        Step Hr1i: (andb (ltn i nbreg) (has r1 (cm i))).
          Apply/andP; Split; RightBy Apply/hasP; Exists p.
          Case/andP: Hij {}ltn_trans; EAuto.
        Rewrite: Hr1 /set2 -Dj orbC eqd_sym (negbE Hi) /= in Hr1i.
        By Rewrite: (eqP Hr1i) Hip in Hi1p.
      By Rewrite: -Dj in Hp; Case/hasP: (Hcm ? ? Hij); Exists p.
    Case: (i =P j1) => [Di | _]; RightBy Apply: Hcm.
    Apply/hasP=> [[p Hjp Hxmp]].
    Case/andP: (Hxmr ? Hxmp) => [Hi1p]; Case/orP=> [Hp].
      Step Hr1j: (andb (ltn j nbreg) (has r1 (cm j))).
        By Rewrite: Hj; Apply/hasP; Exists p.
      Rewrite: Hr1 /set2 -Di orbC (negbE Hi) /= in Hr1j.
      By Rewrite: (eqP Hr1j) Hjp in Hi1p.
    By Rewrite: -Di in Hp; Case/hasP: (Hcm ? ? Hij); Exists p.
  Move=> Haij; Case: (Habcm ? ? Hij Haij) => [Hcmi Habij]; Split.
    By Case/hasP: Hcmi => [p Hcmp Hp]; Apply/hasP; Exists p; LeftBy Apply: Excm.
  Move=> k; Rewrite: -~Habij /xcm; Case: (k =P j1) => // [Dk]; Rewrite Dk.
  Congr andb; Apply/hasP/hasP=> [[p Hcmp Habp]]; RightBy Exists p; Auto.
  Case/andP: (Hxmr ? Hcmp) => [Hi1p]; Case/orP=> [Hp]; RightBy Exists p.
  By Case: (ab_proper_refine Hij Hij1 Habp Hp); Do 2 Case/esym; Apply: hasP.
Exists xcm; [Done | Case: Hxcm => [Hxcm _] i j Hij].
Move: (Hadj ? ? Hij); Case Hsij: (subregpair (S i1) j1 i j).
  Case Hs'ij: (subregpair i1 j1 i j).
    Move=> H; Move/H {H}; Rewrite: /cm_adj; Case/hasP=> [p].
    Rewrite: !mring_def; Case/andP=> [Hip _]; Move/andP=> [Hjp _].
    Def: Hxcmij := (Hxcm ? ? Hij).
    Apply/hasP; Exists p; Rewrite: mring_def Excm ?gedge2 //=.
      By Rewrite: has_sym in Hxcmij; Apply: (hasPn Hxcmij); Apply: Excm.
    By Apply: (hasPn Hxcmij); Apply: Excm.
  Do 2 Clear; Move: Hsij Hs'ij; Rewrite: /subregpair ltnS leq_eqVlt.
  Case: (i =P i1); RightBy Move=> _ H; Case/idP.
  Case: (j =P j1); RightBy Move=> _ _ H; Case/idP.
  Case/andP: Hij1 => [Hi1 _] Dj Di _ _; Rewrite: Di Dj /cm_adj /xcm set11.
  By Rewrite: eqn_leq andbC leqNgt Hi1.
Move: Hsij; Rewrite: /subregpair ltnS leqNgt /xcm.
Case: (j =P j1) => [Dj | Hj] /=; RightBy Case/esym.
Move/idP=> Hi; Rewrite: ltnNge (ltnW Hi) /= {1 j}Dj.
Step Hr1i: (p : gpoint) (ab1 i j p) -> (r1 p) = false.
  Move=> p Hp; Apply/idP=> [Hp1].
  By Case: (ab_proper_refine Hij Hij1 Hp Hp1) Hi => [[] _]; Rewrite ltnn.
Move=> Hcmj1 p q Hp Epq.
Step Hq: (ab1 i j q) By Move: Hp; Rewrite: /refine_adjbox !mem_refine_rect Epq.
Apply/idP/idP; Move/(Hxmr ?); Case/andP; Clear; Rewrite: /setU Hr1i //=.
  By Rewrite: (Hcmj1 ? ? Hp Epq); Apply: Hxm.
By Rewrite: -(Hcmj1 ? ? Hp Epq); Apply: Hxm.
Qed.

Local cm2 : cmatte := let (cm, _, _) = cm_extend_meet in cm.

Remark Hcm2 : (cm_proper cm2). Proof. By Rewrite: /cm2; Case cm_extend_meet. Qed.

Remark Habcm2 : (i, j : nat) (regpair i j) -> (ab_adj ab1 i j) -> (cm_adj cm2 i j).
Proof. By Rewrite: /cm2; Case cm_extend_meet. Qed.

(* Now we compute a bounding box for the extended mattes. *)

Definition grect0 : grect := (Grect (Znat 0) (Znat 0) (Znat 0) (Znat 0)).

Definition cm_bbox : grect :=
  (iter_n nbreg [i; r](foldr extend_grect r (cm2 i)) grect0).

Syntactic Definition bb := cm_bbox.

Lemma sub_cm_bbox : (sub_set (cm_mem cm2) bb).
Proof.
Move=> p; Rewrite: /cm_mem /cm_bbox /=; Elim: {}nbreg => //= [n Hrec].
Move: (iter_n n [i; r](foldr extend_grect r (cm2 i)) grect0) Hrec => r Hrec Hprec.
Step Hp: (orb (cm2 n p) (r p)) By Apply/orP; Case/orP: Hprec; Auto.
Elim: {n cm}((cm2 n)::gpointseq) Hp {Hprec Hrec} => //= [q m Hrec] Hp.
Apply mem_extend_grect; Apply/orP; Rewrite: /setU1 -orbA in Hp; Case/orP: Hp; Auto.
Qed.

Syntactic Definition bbw := (gwidth bb).
Syntactic Definition bbh := (gheight bb).

Remark Hbb0: (ltn (0) (garea bb)).
Proof.
Case Dn: {}nbreg => [|n]; LeftBy Rewrite: /cm_bbox Dn.
Case Dcm2n: (cm2 n) => [[|p m] c Hm Hc Uc Dc] //.
Step Hp: (bb p).
  Apply sub_cm_bbox; Rewrite: /cm_mem Dn; Apply/orP; Left.
  By Rewrite: Dcm2n /= setU11.
By Move: Hp; Rewrite: -mem_enum_grect -size_enum_grect; Case (enum_grect bb).
Qed.

(* Now we define a frame around the box. *)

Definition frs_step [p : gpoint] : gpoint := (gface (gedge (gface p))).

Definition halfg_n_frs [n : nat; d : gbits; p : gpoint] : gpoint :=
  let (x, y) = p in
  Cases d of
    Gb00 => (Gpoint (addz x (Zpos n)) y)
  | Gb11 => (Gpoint (subz x (Zpos n)) y)
  | Gb10 => (Gpoint x (addz y (Zpos n)))
  | Gb01 => (Gpoint x (subz y (Zpos n)))
  end.

Lemma iter_frs_step : (n : nat; d : gbits; p : gpoint)
  (iter n frs_step (consg d p)) = (consg d (halfg_n_frs n d p)).
Proof.
Elim=> [|n Hrec]; LeftBy Case; Case=> *; Rewrite: /= /subz /= ?addz0.
Move=> d p; Rewrite: /= ~Hrec /frs_step {1}/gface oddg_edge halfg_edge oddg_face.
Rewrite: halfg_face ccw4 oddg_cons halfg_cons; Congr consg.
By Case: d; Case: p => [x y]; Rewrite: /= -?addzA /= ?addn0 ?addn1 ?addz0 //;
  Rewrite: /subz -addn1 zpos_addn oppz_add -!addzA.
Qed.

Definition frs_base [d : gbits; x, y : znat] : gpoint :=
  (consg (ccw d) (addg (Gpoint x y) (addg d (oppg (ccw d))))).
 
Lemma frs_base_eq : (d : gbits; x, y : znat)
  (frs_base d x y) = (gnode (consg d (Gpoint x y))).
Proof.
Move=> d x y; Rewrite: /gnode oddg_cons /consg -addgA addgCA /frs_base /consg.
By Move: (Gpoint x y) => p; Rewrite: -!addgA -!(addgCA p); Case d.
Qed.

Definition cm_frame : gpointseq :=
  let (xmin, xmax, ymin, ymax) = bb in
  (cat (traject frs_step (frs_base Gb00 xmin ymin) bbh)
  (cat (traject frs_step (frs_base Gb01 xmin ymax) bbw)
  (cat (traject frs_step (frs_base Gb11 xmax ymax) bbh)
       (traject frs_step (frs_base Gb10 xmax ymin) bbw)))).

Syntactic Definition bbf := cm_frame.

Lemma cm_frame_size : (size bbf) = (double (addn bbh bbw)).
Proof.
Rewrite: /cm_frame; Case: {1}bb=> [x0 x1 y0 y1] /=.
By Rewrite: !size_cat !size_traject !double_addnn -!addnA.
Qed.

Lemma zwidth_eq : (x0, x1 : znat)
  x1 = (if (zwidth x0 x1) is (S n) then (addz x0 (Zpos n)) else x1).
Proof.
Move=> x0 x1; Rewrite: -{1 3 x1}(subz_add x0) -addz_subA /zwidth.
By Case (subz x1 x0).
Qed.

Lemma cycle_cm_frame : (cycle mrlink bbf).
Proof.
Step Hfrs: (n : nat; p : gpoint)
  (path mrlink p (traject frs_step (frs_step p) n)).
  Move=> n p; Apply: (sub_path ? (fpath_traject ? ? ?)) {p} => [p q].
  Rewrite: /eqdf /mrlink; Case/eqP; Apply/eqP.
  By Rewrite: /frs_step end0g_face end1g_edge end0g_face.
Move: Hbb0; Rewrite: /garea /cm_frame /gwidth /gheight; Case: bb => [x0 x1 y0 y1].
Case: (zwidth x0 x1) (zwidth_eq x0 x1) => // [w] Dx1.
Rewrite mult_sym; Case: (zwidth y0 y1) (zwidth_eq y0 y1) => //= [h] Dy1 _.
Rewrite: -cats1; Repeat Rewrite: path_cat ?last_cat /= ?Hfrs.
Rewrite: !last_traject /frs_base !iter_frs_step.
Rewrite: /mrlink /end0g /end1g !oddg_cons !halfg_cons /= -!addzA /= !addz0 !add0n.
Rewrite: !addn0 !zpos_addn !addzA -Dx1 -Dy1 !set11 {1 y1}Dy1 (addzC y0) subz_add.
By Rewrite: set11 Dx1 addzC subz_add set11.
Qed.

Lemma uniq_cm_frame : (uniq bbf).
Proof.
Step Ufrs1: (n : nat; p : gpoint) (uniq (traject frs_step p n)).
  Move=> [|n] // p; Rewrite: looping_uniq; Apply/trajectP=> [[i Hi Dp]].
  Rewrite: ltn_neqAle in Hi; Case/andP: Hi; Case/eqP; Move: {Dp}(congr halfg Dp).
  Rewrite: -{p}consg_odd_half !iter_frs_step !halfg_cons.
  By Case/oddg: p (halfg p) => [] [x y]; Injection=> Dn; Move/addz_inj: Dn;
    Try Move/(monic_inj 1!znat oppz_opp 7!?); Injection=> Dn.
Step Ufrs2: (n1, n2 : nat; d1, d2 : gbits; p1, p2 : gpoint) (negb d1 =d d2) ->
  (has (traject frs_step (consg d1 p1) n1) (traject frs_step (consg d2 p2) n2))
    = false.
  Move=> n1 n2 d1 d2 p1 p2 Hd; Apply/hasP=> [[q]].
  Move/trajectP=> [i2 _ []] {q}; Move/trajectP=> [i1 _ Ei]; Case/eqP: Hd.
  By Move: (congr oddg Ei); Rewrite: !iter_frs_step !oddg_cons.
Rewrite: /cm_frame /frs_base; Case: bb => [x0 x1 y0 y1].
Repeat Rewrite: uniq_cat !Ufrs1 ?has_cat !Ufrs2 //.
Qed.

Lemma cm_frame_def : bbf =1 [p](andb (bb (halfg (gedge p))) (negb (bb (halfg p)))).
Proof.
Step Efrs: (n1 : nat; d, d1 : gbits; p, p1 : gpoint)
  (traject frs_step (consg d1 p1) (locked S n1) (consg d p)) =
     (if d =d d1 then (locked traject ? frs_step (consg d1 p1) (S n1) (consg d p))
      else false).
  Move=> n1 d d1 p p1; Rewrite: -!lock; Move/S: n1 => n1.
  Case: (d =P d1) => // [Hd]; Apply/trajectP=> [[i _ Dp]]; Case: Hd.
  By Move: (congr oddg Dp); Rewrite: iter_frs_step !oddg_cons.
Step leqz_pos: (x : znat; n : nat) (leqz x (addz x (Zpos n))).
  By Move=> x n; Rewrite: /leqz -subz_sub subzz; Case n.
Step leqz_wid: (x0, x1 : znat) (leqz x0 x1) -> {w : nat | (addz x0 (Zpos w)) = x1}.
  Move=> x0 x1 Hx01; Exists (pred (zwidth x0 x1)); Move: (zwidth_eq x0 x1) Hx01.
  By Rewrite: /leqz -oppz_sub /zwidth; Case (subz x1 x0).
Move=> p; Rewrite: -{1 p}consg_odd_half halfg_edge.
Case/halfg: p (oddg p) => [x y] d.
Move: Hbb0; Rewrite: /garea /cm_frame /gwidth /gheight; Case: bb => [x0 x1 y0 y1].
Case: (zwidth x0 x1) (zwidth_eq x0 x1) => // [w] Dx1.
Rewrite mult_sym; Case: (zwidth y0 y1) (zwidth_eq y0 y1) => // [h] Dy1 _.
Rewrite: {S}lock /frs_base; Repeat Rewrite: mem_cat /setU !Efrs.
Case: d => /=; Rewrite: !addz0 !addn0 ?orbF -!andbA -lock;
  (Apply/trajectP/idP; [Move=> [i Hi Dp]; Move: {Dp}(congr halfg Dp);
     Rewrite: iter_frs_step !halfg_cons /= -?incz_def -?decz_def;
     Injection=> [] []
    | Rewrite: -?incz_def -?decz_def; Move/and5P=> [Hx0 Hx1 Hy0 Hy1]]).
 Rewrite: decz_inc -negb_leqz leqzz !andbF Dy1 !leqz_pos !andbT Dx1 leqz_add2l.
  By Rewrite: leqz_nat.
 Rewrite: Hx0 Hx1 leqz_dec ~Hy0 orbT /= negb_leqz leqz_inc -negb_leqz orbC.
  Rewrite: -leqz_dec_inc ~Hy1 /=; Case/eqP.
  Case: (leqz_wid ? ? Hx0) Hx1 => [i []]; Rewrite: Dx1 leqz_add2l leqz_nat.
  By Move=> Hi; Exists i; Rewrite: // iter_frs_step.
 Rewrite: incz_dec -leqz_inc_dec -negb_leqz leqzz Dx1 !leqz_pos !andbT.
  By Rewrite:  Dy1 leqz_add2l leqz_nat.
 Rewrite: Hy0 Hy1 !andbT andbC leqz_inc ~Hx1 orbT /= negb_leqz leqz_inc -negb_leqz.
  Rewrite: ~Hx0 orbF; Case/eqP; Rewrite decz_inc.
  Case: (leqz_wid ? ? Hy0) Hy1 => [i []]; Rewrite: Dy1 leqz_add2l leqz_nat.
  By Move=> Hi; Exists i; Rewrite: // iter_frs_step.
 Rewrite: incz_dec -leqz_inc_dec -negb_leqz leqzz !andbF Dy1 leqz_pos !andbT.
  Rewrite: andbC -leqz_opp2 oppz_sub {1}/subz addzC leqz_pos /=.
  By Move: (zpos_subn w i); Rewrite: -ltnS Hi Dx1 -addz_subA; Case.
 Rewrite: Hx0 Hx1 /= andbC leqz_inc ~Hy1 orbT /= negb_leqz leqz_inc -negb_leqz.
  Rewrite: ~Hy0 orbF; Case/eqP.
  Case: (leqz_wid ? ? Hx0) Hx1 => [i []]; Rewrite: Dx1 leqz_add2l leqz_nat.
  Move=> Hi; Exists (subn w i); LeftBy Rewrite: ltnS leq_subr.
  Rewrite: iter_frs_step /= decz_inc; Congr consg; Congr Gpoint.
  By Rewrite: zpos_subn Hi {1}/subz oppz_sub -addzA addz_subA subz_add.
 Rewrite: decz_inc -negb_leqz leqzz !andbF Dx1 leqz_pos !andbT /=.
  Rewrite: andbC -leqz_opp2 oppz_sub {1}/subz addzC leqz_pos /=.
  By Move: (zpos_subn h i); Rewrite: -ltnS Hi Dy1 -addz_subA; Case.
 Rewrite: Hy0 Hy1 !andbT leqz_dec ~Hx0 orbT /= negb_leqz leqz_inc -negb_leqz.
  Rewrite: -leqz_dec_inc ~Hx1 orbF; Case/eqP.
  Case: (leqz_wid ? ? Hy0) Hy1 => [i []]; Rewrite: Dy1 leqz_add2l leqz_nat.
  Move=> Hi; Exists (subn h i); LeftBy Rewrite: ltnS leq_subr.
  Rewrite: iter_frs_step /=; Congr consg; Congr Gpoint.
  By Rewrite: zpos_subn Hi {1}/subz oppz_sub -addzA addz_subA subz_add.
Qed.

(* We build a dual hypermap (that is gmface == gnode^-1 & gmnode == gface^-1) *)
(* so that we use the definitions from snip.v and patch.v directly.           *)

Definition gm_grid : gpointseq := (enum_grect (refine_rect bb)).

Syntactic Definition gbg := gm_grid.

Lemma gm_grid_def : (p : gpoint) (gbg p) = (bb (halfg p)).
Proof. By Move=> p; Rewrite: /gm_grid mem_enum_grect mem_refine_rect. Qed.

Lemma size_gm_grid : (size gbg) = (double (double (garea bb))).
Proof. By Rewrite: /gm_grid size_enum_grect garea_refine_rect. Qed.

Definition gmdartseq : gpointseq := (cat bbf gbg).

Definition gmdart : finSet := (SeqFinSet gmdartseq).

Lemma gmedgeP : (u : gmdart) (gmdartseq (gedge (subdE u))).
Proof.
Case=> [x] /=; Rewrite: /gmdartseq !mem_cat /setU !cm_frame_def -!gm_grid_def.
By Rewrite: gedge2; Case (gbg x); Case (gbg (gedge x)).
Qed.

Definition gmnode [p : gpoint] : gpoint :=
  if (bbf p) then (prev bbf p) else (gedge (gnode p)).

Lemma gmnodeP : (u : gmdart) (gmdartseq (gmnode (subdE u))).
Proof.
Case=> [x] /=; Rewrite: /gmdartseq !mem_cat /setU /gmnode.
Case Hx: (bbf x); LeftBy Rewrite: mem_prev Hx.
By Rewrite: /= !gm_grid_def; Move=> H; Rewrite: -halfg_face gmonicN H orbT.
Qed.

Definition gmface [p : gpoint] : gpoint :=
  if (bbf (gedge p)) then (next bbf (gedge p)) else (gface (gedge p)).

Lemma gmfaceP : (u : gmdart) (gmdartseq (gmface (subdE u))).
Proof.
Move=> u; Case: u (gmedgeP u) => [x H] {H}/=.
Rewrite: /= /gmdartseq !mem_cat /setU /gmface.
Case Hx: (bbf (gedge x)); LeftBy Rewrite: mem_next Hx.
By Rewrite: /= !gm_grid_def; Move=> H; Rewrite: halfg_face H orbT.
Qed.

Local gm_edge [u : gmdart] : gmdart := (subdI (gmedgeP u)).
Local gm_node [u : gmdart] : gmdart := (subdI (gmnodeP u)).
Local gm_face [u : gmdart] : gmdart := (subdI (gmfaceP u)).

Lemma gm_boxmapP : (!monic3 gmdart gm_edge gm_node gm_face).
Proof.
Case=> [x Hx] /=; Apply: subdE_inj; Rewrite: /= /gmface gedge2.
Rewrite: /gmdartseq mem_cat /setU in Hx.
Case Hx': (bbf x) Hx; Rewrite: /gmnode.
  By Rewrite: mem_next Hx' prev_next // uniq_cm_frame.
By Rewrite: cm_frame_def halfg_face -!gm_grid_def andbC /= gmonicF; Case/esym.
Qed.

Definition gm_boxmap : hypermap := (Hypermap gm_boxmapP).

Syntactic Definition gmb := gm_boxmap.
Local gmbE : gmb -> gpoint := (subdE 2!?).
Remark HgmbE: (injective gmbE). Proof. Apply: (!subdE_inj). Qed.

Definition gm_ring [i : nat] : (seq gmb) :=
  (preimage_seq gmbE ((mring (cm2 i)))).

Lemma cm_memPx : (cm : cmatte; p : gpoint)
  (reflect (EX i | (ltn i nbreg) & (cm i p)) (cm_mem cm p)).
Proof.
Move=> cm p; Rewrite: /cm_mem; Elim: {}nbreg => [|n Hrec]; LeftBy Right; Case.
Rewrite: /= orbC; Case: Hrec=> [Hp] /=.
  By Left; Case: Hp => [i]; Exists i; LeftBy Apply leqW.
Apply introP; LeftBy Exists n; LeftBy Apply leqnn.
Move=> Hnp [i Hi Hp']; Rewrite: ltnS leq_eqVlt in Hi.
By Case/setU1P: Hi => [Di | Hi]; [Rewrite: -Di Hp' in Hnp | Case Hp; Exists i].
Qed.

Syntactic Definition cm_memP := cm_memPx | 2.

Lemma maps_gm_ring : (i : nat) (ltn i nbreg) ->
  (maps gmbE (gm_ring i)) = ((mring (cm2 i))).
Proof.
Move=> i Hi; Apply: maps_preimage => [x Hix].
Case: (subdIoptP gmdartseq x); LeftBy Move=> u _ []; Rewrite: /gmbE codom_f.
Rewrite: /gmdartseq mem_cat /setU gm_grid_def; Case/orP; Right.
Rewrite: mring_def in Hix; Case/andP: Hix => [Hx _].
By Apply: sub_cm_bbox; Apply/cm_memP; Exists i.
Qed.

Lemma rect_gnode2 : (p : gpoint; r : grect)
  (r p) -> (r (gnode (gnode p))) -> (r (gnode p)).
Proof.
Move=> p [x0 x1 y0 y1]; Rewrite: {1}/gnode oddg_node /gnode -!addgA addg_inv.
Case: p (oddg p) => [x y] /= d; Move/and4P=> [Hx0 Hx1 Hy0 Hy1].
By Case: d; Rewrite: /= ?addz0 -?incz_def -?decz_def;
  Case/and4P=> *; Apply/and4P; Split.
Qed.

Lemma end0g_gmcface : (u, v : gmb)
  (cface u v) = ((end0g (gmbE u)) =d (end0g (gmbE v))).
Proof.
Move=> u v; Apply/idP/eqP.
  Move/connectP=> [p]; Case/fpathP=> [n []] [] {p v}.
  Rewrite last_traject; Elim: n u => // [n Hrec] u; Rewrite: -iter_f -~Hrec.
  Case: u => [x H] {H}/=; Rewrite: /gmface; Case Hx: (bbf (gedge x)).
    Move: (next_cycle cycle_cm_frame Hx); Rewrite: /mrlink; Case/eqP.
    By Rewrite: end1g_edge.
  By Rewrite: end0g_face end1g_edge.
Step Ehen: (p : gpoint) (halfg (gedge (gnode p))) = (halfg p).
  By Move=> p; Rewrite: -halfg_face gmonicN.
Step Hn1: (w1, w2 : gmb) (gmbE w1) = (gnode (gmbE w2)) -> (cface w1 w2).
  Move=> [nx Hx] [x Hnx] /= Dnx; Apply connect1; Rewrite: /eqdf /eqd /= /gmface.
  Apply/eqP; Move: Hx Hnx; Rewrite: /gmdartseq !mem_cat /setU !cm_frame_def.
  Rewrite: Dnx gedge2 -halfg_face gmonicN -!gm_grid_def -Dnx.
  Case Hx: (gbg x); Rewrite: ?andbF //= ?orbF andbT Dnx.
  Move: Hx; Rewrite: -{1 2 x}gmonicE; Move=> Hx1 Hx2 Hx0; Case/idP: Hx1.
  Rewrite: gm_grid_def -halfg_face -gm_grid_def in Hx0.
  Move: Hx0 Hx2; Rewrite: /gm_grid !mem_enum_grect; Apply: (!rect_gnode2).
Move/same_end0g; Case/setU1P; LeftBy Case/HgmbE; Apply connect0.
Case/setU1P; LeftBy Rewrite Sface; Auto.
Rewrite: /setU1 orbF orbC; Case/orP; Move/eqP.
  Move/(congr gnode 5!?); Rewrite gnode4; Auto.
Case: (subdIoptP gmdartseq (gnode (gmbE u))) => [u' _ Du' | Hn1u].
  Rewrite: -Du' Sface; Move=> Dv; Apply connect_trans with u'; Auto.
Case: (subdIoptP gmdartseq (gnode (gmbE v))) => [v' _ Dv' | Hn1v].
  Move/(congr [w](gnode (gnode w)) 5!?); Rewrite: gnode4 -Dv'.
  Move=> Du; Apply connect_trans with v'; Auto.
Move=> Dv; Case/idP: Hn1v; Move: u v Dv Hn1u => [x Hx] [y Hy] /= Dy; Move: Hx Hy.
Rewrite: /gmdartseq !mem_cat /setU -Dy !cm_frame_def -{1 x}gnode4 !Ehen Dy.
Rewrite: -!gm_grid_def.
By Case (gbg x); Case (gbg y); Case (gbg (gnode y)); Case (gbg (gnode x)).
Qed.

Lemma scycle_gm_ring : (i : nat) (ltn i nbreg) -> (scycle rlink (gm_ring i)).
Proof.
Move=> i Hi; Step Ur: (simple (gm_ring i)).
  Move: (mring (cm2 i)) (gm_ring i) (maps_gm_ring Hi) (simple_mring (cm2 i)).
  Elim=> [|p c Hrec] [|[x Hx] c'] //=; Injection=> Dc [] {p}.
  Move/andP=> [Hcx Uc]; Rewrite: (!simple_adds gmb) ~Hrec ~{Uc}// andbT.
  Apply/hasP=> [[u Hu Hux]]; Case/mapsP: Hcx; Exists (gmbE u).
    By Rewrite: -Dc maps_f.
  By Rewrite: end0g_gmcface in Hux; Move/eqP: Hux.
Apply/andP; Split; RightDone; Move/simple_uniq: Ur => Ur.
Apply: cycle_from_next => // [u Hu]; Rewrite: /rlink end0g_gmcface.
Rewrite: -(next_maps HgmbE) // maps_gm_ring //.
Rewrite: -(mem_maps HgmbE) maps_gm_ring // in Hu.
By Move: (next_cycle (cycle_mring ?) Hu); Rewrite: /= end0g_edge.
Qed.

Lemma gm_plain : (plain gmb).
Proof.
Apply/plainP=> [[x Hx]] /= _; Split; LeftBy Apply HgmbE; Rewrite: /= gedge2.
By Rewrite: /eqd /= /gedge -{4 x}addg0 (monic_eqd (addg_inv x)); Case (oddg x).
Qed.

Lemma gm_disk_def : (i : nat) (ltn i nbreg) ->
  (sub_set (diskN (gm_ring i)) [u](cm2 i (halfg (gmbE u)))).
Proof.
Move=> i Hi u; Case/hasP=> [v Hv]; Case/connectP=> [p Hp []] {u}.
Pose v' := (finv node v); Rewrite: -/v' in Hp.
Step Hbbi: (sub_set (cm2 i) bb).
  By Move=> x Hx; Apply sub_cm_bbox; Apply/cm_memP; Exists i.
Step Hv': (cm2 i (halfg (gmbE v'))).
  Rewrite: -(mem_maps HgmbE) maps_gm_ring // mring_def in Hv.
  Case/andP: Hv => [Hvi _].
  Case Hvb: (bbf (subdE v)); LeftBy Rewrite: cm_frame_def andbC Hbbi //= in Hvb.
  Move: Hvb Hvi; Rewrite: -{v}(f_finv (Inode gmb)) -/v' /= /gmnode.
  Case Hv': (cm_frame (subdE v')); LeftBy Rewrite: mem_prev Hv'.
  By Rewrite: -halfg_face gmonicN.
Elim: p {v Hv}v' Hv' Hp => [|v p Hrec] u //= Hu.
Case/andP; Move/andP=> [Heu Huv]; Apply: Hrec {Hrec}.
Rewrite: -(mem_maps HgmbE) maps_gm_ring // mring_def Hu /= negb_elim in Heu.
Case/clinkP: Huv; Move/(congr gmbE 5!?)=> /=.
  Case Hu': (bbf (subdE u)); LeftBy Rewrite: cm_frame_def andbC Hbbi // in Hu'.
  Rewrite: /gmnode; Case Hv: (cm_frame (subdE v)) => [] Du.
    By Rewrite: Du mem_prev Hv in Hu'.
  By Move: Hu; Rewrite: -halfg_face Du gmonicN.
By Case; Rewrite: /gmface cm_frame_def andbC Hbbi //= halfg_face.
Qed.

Lemma disjoint_gm_disk : (i, j : nat) (regpair i j) ->
  (disjoint (diskN (gm_ring i)) (diskN (gm_ring j))).
Proof.
Move=> i j Hij; Case: (andP Hij) => [Hi' Hj]; Def: Hi := (ltn_trans Hi' Hj).
Apply/set0Pn=> [[u]]; Move/andP=> [Hui Huj].
By Case/hasP: (Hcm2 Hij); Exists (halfg (gmbE u)); Apply gm_disk_def.
Qed.

Lemma gm_connected : (connected gmb).
Proof.
Pose hE := [u](halfg (gmbE u)).
Step DhE : (u : gmb) (halfg (gmbE u)) = (hE u) By Done.
Step [u0 Hu0]: (EX u0 | (bb (hE u0))).
  Move: Hbb0 (mem_enum_grect bb); Rewrite: -size_enum_grect.
  Case: (enum_grect bb) => // [p er] _ Hbb.
  Case: (subdIoptP gmdartseq (consg Gb00 p)) => [u _ Du | ].
    By Exists u; Rewrite: /hE /gmbE Du halfg_cons -Hbb /= setU11.
  Rewrite: /gmdartseq mem_cat /setU gm_grid_def halfg_cons -Hbb /=.
  By Rewrite: setU11 orbT.
Cut (v : gmb) (bb (hE v)) -> (gcomp u0 v).
  Move=> Hg; Rewrite: /connected /n_comp (cardD1 (root glink u0)).
  Rewrite: /setI (roots_root (Sglink gmb)); Apply/set0P=> [v].
  Apply/and3P=> [[Huv Dv _]]; Case/eqP: Huv; Case/(? =P v): Dv.
  Apply: (rootP (Sglink gmb)); Move: (subd_mem v); Rewrite: -/(gmbE v).
  Rewrite: /gmdartseq mem_cat; Case/orP; RightBy Rewrite: gm_grid_def; Auto.
  Rewrite: cm_frame_def; Case/andP=> [Hev _].
  By Apply connect_trans with (edge v); Auto; Rewrite: Sglink connect1 ?glinkE.
Step Hbb': (sub_set bb bb) By Move.
Elim: (S (garea bb)) {-2 -4}bb (ltnSn (garea bb)) Hbb' u0 Hu0 => // [n Hrec] r Hn.
Move=> Hr u Hu v Hv; Case: (pickP [w](andb (hE w) =d (hE u) (r (hE (edge w))))).
  Rewrite: ltnS in Hn; Move=> w; Case/andP; Pose p := (gmbE w); Move/eqP=> Dp Hrw. 
  Pose r1 := (gchop_rect r p); Pose r2 := (gchop_rect r (gedge p)).
  Step Hr1w: (r1 (hE w)).
    By Rewrite: /r1 mem_gchop_rect /setI {2}/hE gchop_halfg Dp andbT.
  Step Hr1: (v' : gmb) (r1 (hE v')) -> (gcomp u v').
    Step Hr1: (sub_set r1 r) By Move=> q; Rewrite: /r1 mem_gchop_rect; Case/andP.
    Apply: Hrec; [Idtac | By Move; Auto | By Rewrite: -Dp].
    Apply: leq_trans Hn; Apply ltn_garea_sub_rect with (hE (edge w)); Auto.
    Rewrite: /setD Hrw /r1 mem_gchop_rect -{p}gedge2 /setI gchop_edge.
    By Rewrite: /setC /hE /=  gchop_halfg andbF.
  Case Hr1v: (r1 (hE v)); Auto.
  Step Hr2v: (r2 (hE v)).
    By Move/negbI: Hr1v; Rewrite: /r1 /r2 !mem_gchop_rect /setI Hv gchop_edge.
  Apply: (connect_trans (Hr1 ? Hr1w)); Apply connect_trans with (edge w).
    By Apply connect1; Apply glinkE.
  Step Hr2: (sub_set r2 r) By Move=> q; Rewrite: /r2 mem_gchop_rect; Case/andP.
  Apply Hrec with r2; Auto; Try By Move; Auto.
    Apply: leq_trans Hn; Apply ltn_garea_sub_rect with (hE u); Auto.
    Rewrite: /setD Hu -Dp /r2 mem_gchop_rect /setI gchop_edge /setC.
    By Rewrite: /hE gchop_halfg andbF.
  By Rewrite: /r2 mem_gchop_rect /setI Hrw /hE /= gchop_halfg.
Pose p := (hE u); Move=> Hp; Step Hrp: r =1 (set1 p).
  Move=> q; Apply/idP/eqP=> [Hq | []] //.
  Step Hrq: (all [d](gchop (consg d p) q) (traject ccw Gb00 (4))).
    Apply/allPn=> [[d _ Hqd]]; Case (subdIoptP gmdartseq (consg d p)).
      Move=> w _ Dw; Case/idP: (Hp w).
      Rewrite: /hE Dw halfg_cons /= set11 andTb.
      Rewrite: -/p -(halfg_cons d p) -{(consg d p)}gedge2 in Hu.
      Move: (gchop_rect_edge Hu 4!q).
      Rewrite: !mem_gchop_rect /setI gchop_edge /setC Hqd andbT -Dw.
      By Move=> H; Case/andP: (H Hq).
    By Rewrite: /gmdartseq mem_cat /setU gm_grid_def halfg_cons orbC Hr.
  Rewrite: /= /gchop !halfg_cons !oddg_cons andbCA andbC -!andbA /= andbA in Hrq.
  Case/andP: Hrq; Case: {}p {}q => [x y] [x' y']; Rewrite: -!eqz_leq.
  By Do 2 Case/eqP.
Step Huv: (traject gface (gmbE u) (4) (gmbE v)).
  Rewrite: Hrp in Hv; Rewrite: -{(gmbE v)}consg_odd_half DhE -(eqP Hv).
  Rewrite: -{(gmbE u)}consg_odd_half DhE -/p /= /setU1.
  Rewrite: {1 2 4}/gface !halfg_face !oddg_face halfg_cons oddg_cons.
  By Case (oddg (gmbE u)); Case (oddg (gmbE v)); Rewrite: /= set11 ?orbT.
Case/trajectP: Huv => [i _ Dv] {n Hrec Hv p Hp Hrp Hn}; Rewrite: Sglink.
Elim: i u {r Hr Hu}(Hr ? Hu) Dv => [|i Hrec] u Hu Dv.
  By Apply eq_connect0; Apply HgmbE.
Step Hfeu: (gmbE (face (edge u))) = (gface (gmbE u)).
  By Rewrite: /= /gmface -/(gmbE u) gedge2 cm_frame_def DhE Hu andbF. 
Apply: (connect_trans (Hrec (face (edge u)) ? ?) ?).
    By Rewrite: /hE Hfeu halfg_face.
  By Rewrite: Hfeu iter_f.
By Apply connect1; Rewrite: -{2 u}Eedge glinkN.
Qed.

Lemma gm_planar : (planar gmb).
Proof.
Pose ngm := (addn (double (garea bb)) (addn (gwidth bb) (gheight bb))).
Step Engm: (card gmb) = (double ngm).
  Pose egmb := (preimage_seq gmbE gmdartseq).
  Step Degmb : (maps gmbE egmb) = gmdartseq.
    Apply: maps_preimage=> [x Hx]; Apply/set0Pn.
    Exists (subdI 2!gmdartseq Hx); Apply: set11.
  Step Uegmb: (uniq egmb).
    Rewrite: -(uniq_maps HgmbE) Degmb /gmdartseq uniq_cat uniq_cm_frame.
    Rewrite: {2}/gm_grid uniq_enum_grect andbT.
    By Apply/hasPn=> [x Hx]; Rewrite: cm_frame_def andbC -gm_grid_def Hx.
  Apply: (etrans (etrans (eq_card ?) (card_uniqP Uegmb))).
    By Move=> [x Hx]; Rewrite: -(mem_maps HgmbE) Degmb.
  Rewrite: -(size_maps gmbE) Degmb /gmdartseq size_cat /cm_frame.
  Case: {1}bb => [x0 x1 y0 y1]; Rewrite: !size_cat !size_traject ~{x0 x1 y0 y1}.
  Rewrite: size_gm_grid addnC /ngm double_add; Congr addn.
  By Apply esym; Rewrite: addnC double_addnn -!addnA.
Step EgmbE: (fcard edge gmb) = ngm.
  Apply: eqP; Rewrite: -(order_div_card (Iedge gmb) gm_plain) // Engm.
  By Apply/eqP; Rewrite: /= !addnI addn0 double_addnn.
Step EgmbN: (fcard node gmb) = (S (garea bb)).
  Pose ebf := (preimage_seq gmbE (rev bbf)).
  Step Debf : (maps gmbE ebf) = (rev bbf).
    Apply: maps_preimage=> [x Hx]; Apply/set0Pn.
    Case: (subdIoptP gmdartseq x) => [u _ [] | ]; LeftBy Exists u; Apply: set11.
    By Rewrite: /gmdartseq mem_cat /setU -mem_rev Hx.
  Step Uebf: (uniq ebf) By Rewrite: -(uniq_maps HgmbE) Debf uniq_rev uniq_cm_frame.
  Step Hebf: (fcycle node ebf).
    Apply: (cycle_from_next Uebf) {u Hu} => [u Hu]; Apply/eqP; Apply HgmbE.
    Rewrite: -(next_maps HgmbE Uebf) Debf (next_rev uniq_cm_frame) /= -/(gmbE u).
    By Rewrite: /gmnode -mem_rev -Debf (mem_maps HgmbE) Hu.
  Rewrite: -add1n (n_compC ebf); Congr addn.
    Step [u Hu]: (EX u | (ebf u)).
      Step [x Hx]: (EX x | (rev bbf x)).
        Move: Hbb0; Rewrite: /garea /cm_frame mult_sym.
        Case: {3}bb => [x0 x1 y0 y1]; Case: (gheight bb) => // [n] _.
        By Exists (frs_base Gb00 x0 y0); Rewrite: mem_rev /= setU11.
      By Rewrite: -Debf in Hx; Case/mapsP: Hx=> [u Hu _]; Exists u.
    Apply: (etrans (esym (eq_n_comp_r ? ?)) (n_comp_connect (Snode gmb) u)).
    By Apply: fconnect_cycle.
  Step Hebf4: (subset (setC ebf) (order_set node (4))).
    Apply/subsetP=> [[x Hx] Hex]; Rewrite: /setC -(mem_maps HgmbE) Debf /= in Hex.
    Pose p := (halfg x); Move: Hx Hx => Hp Hx; Rewrite: /gmdartseq mem_cat in Hp.
    Rewrite: /setU -mem_rev (negbE Hex) gm_grid_def /= -/p in Hp.
    Step Hpd: (d : gbits) (gmdartseq (consg d p)).
      Move=> d; Rewrite: /gmdartseq mem_cat /setU gm_grid_def halfg_cons Hp.
      Apply: orbT.
    Pose pd := [d]((subdI (Hpd d)) :: gmb).
    Step Epd: (injective pd).
      Move=> d d' H; Move: {H}(congr [u](oddg (gmbE u)) H).
      By Rewrite: /pd /= !oddg_cons.
    Step EpdN: (d : gbits) (node (pd d)) = (pd (ccw (ccw (ccw d)))).
      Move=> d; Apply HgmbE; Rewrite: /= /gmnode cm_frame_def /pd halfg_cons.
      Rewrite: Hp andbF; Apply esym; Apply (monic_move gmonicF).
      By Rewrite: /gface halfg_cons oddg_cons ccw4.
    Apply/eqP; Apply: (order_cycle 3!(maps pd (Seq Gb01 Gb11 Gb10 Gb00))).
        By Rewrite: /= /eqdf !EpdN !(inj_eqd Epd).
      By Rewrite: /= /setU1 !(inj_eqd Epd).
    Rewrite: -(mem_maps HgmbE) {maps}lock /= -!lock.
    Step []: (gmbE (pd (oddg x))) = x By Rewrite: /= /p consg_odd_half.
    By Rewrite: (mem_maps HgmbE) /= /setU1 !(inj_eqd Epd); Case (oddg x).
  Step HebfN: (fclosed node (setC ebf)).
    Apply setC_closed; Apply: (intro_closed (Snode ?))=> [x y] Dy Hx.
    By Rewrite: -(? =P y Dy) -(fconnect_cycle Hebf Hx) fconnect1.
  Apply: eqP; Rewrite: -(order_div_card (Inode gmb) Hebf4 HebfN) //; Apply/eqP.
  Rewrite: /= !addnI addn0 addnA -2!double_addnn -size_gm_grid.
  Pose ebb := (preimage_seq gmbE gbg); Step Debb: (maps gmbE ebb) = gbg.
    Apply: maps_preimage=> [x Hx]; Case: (subdIoptP gmdartseq x).
      By Move=> u _ []; Rewrite: codom_f.
    By Rewrite: /gmdartseq mem_cat /setU Hx orbT.
  Step Uebb: (uniq ebb).
    Rewrite: -(uniq_maps HgmbE) Debb; Apply: uniq_enum_grect.
  Rewrite: -Debb size_maps; Apply: (etrans (eq_card ?) (card_uniqP Uebb)).
  Move=> u; Rewrite: -(mem_maps HgmbE) Debb /setC -(mem_maps HgmbE) Debf mem_rev.
  Case: u => [x] /=; Rewrite: /gmdartseq mem_cat /setU orbC.
  Case Hx: (gbg x); RightBy Rewrite: /=; Case/esym.
  By Clear; Rewrite: cm_frame_def -!gm_grid_def Hx andbF.
Pose rgmc := let (x0, x1, y0, y1) = bb in (Grect x0 (incz x1) y0 (incz y1)).
Step Ergmc: (garea rgmc) = (mult (S (gwidth bb)) (S (gheight bb))).
  Rewrite: ~/rgmc; Case: bb Hbb0 => [x0 x1 y0 y1]; Rewrite: /garea /=.
  Rewrite: /zwidth !incz_def -!(addzC (Znat 1)) -!addz_subA.
  By Case: (subz x1 x0) => // [w]; Rewrite mult_sym; Case (subz y1 y0).
Pose dnbb := [p : gpoint] let (x, y) = p in let (x0, x1, y0, y1) = bb in
             (oddg (Gpoint (Zpos (leqz x x1)) (Zpos (leqz y y1)))).
Step Hnbb: (p : gpoint) (rgmc p) ->
           (gmdartseq (addg (addg (dnbb p) neg1g) (addg p p))).
  Move=> p Hp; Rewrite: /gmdartseq mem_cat; Apply/orP; Right.
  Move: Hp; Rewrite: gm_grid_def halfg_add_double addgC /rgmc /dnbb.
  Case Dbb: bb p => [x0 x1 y0 y1] [x y] /=.
  Rewrite: (leqz_inc y) orbC (leqz_inc x) orbC !leqz_inc2.
  Step [Hx01 Hy01]: (leqz x0 x1) /\ (leqz y0 y1).
    Step [[x' y'] Hp]: (EX p | (enum_grect bb p)).
      Move: Hbb0; Rewrite: -size_enum_grect.
      Case: (enum_grect bb) => // [p bb']; Exists p; Apply: setU11.
   Rewrite: mem_enum_grect Dbb in Hp; Case/and4P: Hp.
   Split; EApply leqz_trans; EAuto.
  Case Hx1: (leqz x x1); Case Hy1: (leqz y y1);
  Move/and4P=> /= [Hx0 Dx1 Hy0 Dy1]; Rewrite: ?addz0 -?decz_def;
  By Apply/and4P; Split; Auto;
    Try (By Rewrite: leqz_inc incz_def; Apply/orP; Right);
    Rewrite: ?(eqP Dy1) ?(eqP Dx1) decz_inc ?leqzz.
Step EgmbF: (fcard face gmb) = (garea rgmc).
  Pose e0gm := [u](end0g (gmbE u)).
  Pose ergmc := (preimage_seq e0gm (enum_grect rgmc)).
  Step Dergmc: (maps e0gm ergmc) = (enum_grect rgmc).
    Apply: maps_preimage=> [x Hx]; Rewrite: mem_enum_grect in Hx.
    Apply/set0Pn; Exists ((subdI (Hnbb ? Hx))::gmb).
    Rewrite: /preimage /e0gm /= /end0g halfg_add_double oddg_add_double.
    By Rewrite: -addgA addgCA; Case: (dnbb x); Rewrite: addg0 set11.
  Step UergmcF: (uniq (maps (froot face) ergmc)).
    Case: Dergmc (uniq_enum_grect rgmc).
    Elim: ergmc=> //= [u ec Hrec]; Move/andP=> [Hu Hec].
    Rewrite: ~Hrec ~{Hec}// andbT; Apply/mapsP=> [[v Hv Dv]].
    Case/mapsP: Hu; Exists v; LeftDone.
    By Apply: eqP; Rewrite: /e0gm  -end0g_gmcface; Apply/(rootP (Sface gmb)).
  Rewrite: -size_enum_grect -Dergmc size_maps -(size_maps (froot (!face gmb))).
  Rewrite: -(card_uniqP UergmcF); Apply: eq_card=> [u]; Apply/idP/idP.
    Rewrite: /roots; Case/andP; Case/eqP; Clear.
      Step Hu: (rgmc (e0gm u)).
        Step Hbb: (p : gpoint) (bb (halfg p)) -> (rgmc (end0g p)).
          Rewrite: /rgmc /end0g; Case: {}bb => [x0 y0 x1 y1] p.
          Case/halfg: p (oddg p) => [x y] d /=; Move/and4P=> [Hx0 Hx1 Hy0 Hy1].
          Case: d => /=; Rewrite: -?incz_def ?addz0 ?leqz_inc2;
          Repeat Rewrite: ?Hx0 ?Hx1 ?Hy0 ?Hy1 ?orbT // leqz_inc leqz_inc2.
       Case: u => [x Hx]; Rewrite: /e0gm /= /gmdartseq mem_cat in Hx *.
       Case/orP: Hx => [Hx]; RightBy Rewrite: Hbb -?gm_grid_def.
       Rewrite: cm_frame_def in Hx; Case/andP: Hx=> [Hex _].
       By Rewrite: -end1g_edge -end0g_face Hbb ?halfg_face.
     Rewrite: -mem_enum_grect -Dergmc in Hu; Case/mapsP: Hu => [v Hv Dv].
     Apply/mapsP; Exists v; LeftDone; Apply: (rootP (Sface ?)).
     By Rewrite: end0g_gmcface; Apply/eqP.
  By  Case/mapsP=> [v _ []]; Rewrite: /setI (roots_root (Sface gmb)).
Apply/eqP; Rewrite: /genus /genus_lhs Engm (? =P (1) gm_connected).
Rewrite: /genus_rhs EgmbE EgmbN EgmbF Ergmc /= !double_addnn addn1 !addSn.
Rewrite: !addnS add0n !subSS subn_add2l /ngm double_addnn -!addnA subn_add2l.
By Rewrite: mult_sym /= mult_sym !addnI addnC -!addnA addnCA subnn.
Qed.

Inductive gm_cutout [n : nat] : Type :=
 GmCutout : (g : hypermap; h : g -> gmb)
   (injective h) ->
   (planar g) ->
   ((u : gmb)
    ((EX i | (ltn i n) & (diskE (gm_ring i) u)) \/ (EX x | (h x) = u))) ->
   ((x : g) (h (edge x)) = (edge (h x))) ->
   ((x : g)
    ((EX i | (ltn i n) & (gm_ring i (h x))) \/ (h (node x)) = (node (h x)))) ->
   ((x, y : g) (cface (h x) (h y)) = (cface x y)) ->
   ((i : nat) (ltn i n) -> (fcycle node (rev (preimage_seq h (gm_ring i))))) ->
   (gm_cutout n).

Lemma has_cutout : (gm_cutout nbreg).
Proof.
Elim: {-2}nbreg (leqnn nbreg) => [|j Hrec] Hj.
  Exists gmb [u : gmb]u; Auto; Try By Move.
    Exact gm_planar.
  By Move=> u; Right; Exists u.
Case: {Hrec}(Hrec (ltnW Hj)) => [g h Ih Hg Hh HhE HhN HhF HgN].
Pose rj := (preimage_seq h (gm_ring j)).
Step Drj: (maps h rj) = (gm_ring j).
  Apply: maps_preimage => [u Hu].
  Case: (Hh u) => [[i Hi Hui] | [x []]]; RightBy Apply codom_f.
  Step Hij : (regpair i j) By Apply/andP; Split.
  Case/set0Pn: (disjoint_gm_disk Hij); Exists u.
  By Rewrite: /setI !diskN_E /setU Hu Hui orbT.
Step Hrj: (scycle rlink rj).
  Case/andP: (scycle_gm_ring Hj) => [Hgrj Ugrj].
  Step Urj: (simple rj) By Rewrite: -(simple_maps HhF) Drj.
  Rewrite: /scycle Urj andbT; Move/simple_uniq: Urj => Urj.
  Apply: cycle_from_next => // [x]; Rewrite: -(mem_maps Ih) /rlink -HhF.
  Rewrite: -(next_maps Ih Urj) Drj HhE; Apply: (next_cycle Hgrj).
Step HhjN: (x : g) (diskN rj x) = (diskN (gm_ring j) (h x)).
  Step HdN: (y : g) (diskN (gm_ring j) (h y)) -> (node (h y)) = (h (node y)).
    Move=> y Hy; Case: (HhN y) => // [[i Hi Hiy]].
    Step Hij: (regpair i j) By Apply/andP; Split.
    Case/set0Pn: (disjoint_gm_disk Hij); Exists (h y).
    By Rewrite: /setI diskN_E /setU Hy Hiy.
  Def: ErjN := (fclosed1 (diskN_node (gm_ring j))).
  Def: ErjE := (fclosed1 (diskE_edge gm_planar (scycle_gm_ring Hj))).
  Step HdN': (y : g) (diskN (gm_ring j) (h (node y))) ->
     (node (h y)) = (h (node y)).
    Move=> y Hy; Apply HdN; Rewrite: -{y}(finv_f (Inode g)) /finv.
    Elim: {y}(pred (order node (node y))) {-2}(node y) Hy => // [k Hrec] y Hy. 
    By Rewrite: -iter_f; Apply: Hrec; Rewrite: -(HdN ? Hy) -ErjN.
  Move=> x; Apply/idP/idP.
    Move/hasP=> [y Hy]; Case/connectP=> [p Hp []] {x}; Move: Hp.
    Pose x := (finv node y); Step Hx: (diskN (gm_ring j) (h (node x))).
      By Rewrite: /x (f_finv (Inode g)) diskN_E /setU -Drj mem_maps ?Hy.
    Elim: p {y Hy}x Hx => [|y p Hrec] x Hx /=; LeftBy Move=> _; Rewrite: ErjN HdN'.
    Move/andP=> [Hxy]; Apply: Hrec {Hrec}; Case/andP: Hxy => [Hrjx].
    Case/clinkP=> [[]]; LeftBy Rewrite: ErjN HdN'.
    Rewrite diskN_E; Apply/orP; Right; Rewrite: ErjE -HhE Eface.
    By Rewrite: /diskE /setD -Drj (mem_maps Ih) Hrjx Drj ErjN HdN'.
  Move=> Hx; Case: (hasP Hx)=> [u Hu]; Case/connectP=> [p].
  Elim/last_ind: p x Hx => [|p v Hrec] x Hx.
    Rewrite: (fclosed1 (diskN_node rj)) diskN_E /setU  -(mem_maps Ih) Drj -HdN //.
    By Move=> _ []; Rewrite: /last (f_finv (Inode gmb)) Hu.
  Rewrite: last_add_last -cats1 path_cat; Move/and3P=> [Hp Huv _] Dv.
  Rewrite: (fclosed1 (diskN_node rj)); Rewrite: ~{v}Dv in Huv.
  Case/andP: Huv => [Hrv]; Case/clinkP=> [Ep].
    Move: {}Hx Hp Ep; Rewrite: ErjN HdN //; Apply: Hrec.
  Rewrite: diskN_E /setU; Case Hnx: (rj (node x)) => //.
  Move: {Ep}(monic_move (Eface ?) Ep) => Ep.
  Rewrite: (fclosed1 (diskE_edge Hg Hrj)) /diskE /setD -(mem_maps Ih) Drj HhE.
  Rewrite: -HdN // -Ep Hrv; Move: Hp {}Ep; Rewrite: HdN // -HhE; Apply: Hrec.
  Rewrite: diskN_E; Apply/orP; Right; Rewrite: HhE -ErjE /diskE /setD.
  By Rewrite: -Drj (mem_maps Ih) Hnx Drj -HdN // -ErjN.
Step HhjE: (x : g) (diskE rj x) = (diskE (gm_ring j) (h x)).
 By Move=> x; Rewrite: /diskE /setD -HhjN -Drj (mem_maps Ih).
Def: H := (snip_patch Hg Hrj); Case: H (patch_face_r H).
Move=> _ Ih' _ Hrj' _ _ _ _; Move: (codom_snipr Hg Hrj) Ih' Hrj'.
Move: (snipr 2!Hg 4!Hrj) (snipr_ring Hg Hrj) (maps_snipr_ring Hg Hrj).
Pose g' := (snip_rem Hg Hrj); Move=> h' rj' Drj' Hh' Ih' Hrj' Hh'E Hh'N Hh'F.
Exists g' (comp h h'); Rewrite: /comp.
 By Apply: (inj_comp Ih).
 By Apply: planar_snipr.
 Move=> u; Case: (Hh u) => [[i Hi Hu] | [x []]].
    By Left; Exists i; LeftBy Apply ltnW.
  Case Hx: (codom h' x); LeftBy Right; Exists (iinv Hx); Rewrite f_iinv.
  By Left; Exists j; [Apply leqnn | Rewrite: Hh' /setC HhjE in Hx; Move/idP: Hx].
 By Move=> x'; Rewrite: Hh'E HhE.
 Move=> x'; Case Hx': (gm_ring j (h (h' x'))).
    By Left; Exists j; LeftBy Apply leqnn.
  Case: (HhN (h' x')) => [[i Hi Hhx'] | []].
    By Left; Exists i; LeftBy Apply ltnW.
  Right; Congr h; Apply Hh'N; Rewrite: /setC -(mem_maps Ih') Drj'.
  By Rewrite: mem_rev -(mem_maps Ih) Drj Hx'.
 By Move=> *; Rewrite: HhF Hh'F.
Move=> i; Rewrite: ltnS leq_eqVlt; Case/setU1P=> [Di | Hi].
  Rewrite Di; Step []: (rev rj') = (preimage_seq [x:g'](h (h' x)) (gm_ring j)).
    Apply esym; Apply: (inj_maps Ih'); Apply: (inj_maps Ih).
    Rewrite: -maps_comp maps_rev Drj' rev_rev Drj; Apply: maps_preimage.
    Move=> u Hu; Case: (Hh u) => [[i' Hi' Hui] | [x Du]].
      Step Hi'j: (regpair i' j) By Apply/andP; Split.
      Case/set0Pn: (disjoint_gm_disk Hi'j); Exists u.
      By Rewrite: /setI !diskN_E /setU Hu Hui orbT.
    Step Hx: (codom h' x).
      By Rewrite: Hh' /setC /diskE /setD -(mem_maps Ih) Drj Du Hu.
    Rewrite: -Du -(f_iinv Hx); Apply: codom_f.
  By Rewrite: rev_rev; Case/andP: Hrj'.
Move: (HgN ? Hi); Pose ri := (preimage_seq h (gm_ring i)); Move=> Hri.
Step Dri: (maps h ri) = (gm_ring i).
  Apply: maps_preimage => [u Hu].
  Case: (Hh u) => [[i' Hi'j Hui] | [x []]]; RightBy Apply codom_f.
  Case: (ltnP i' i) => [Hi'].
    Step Hi'i: (regpair i' i).
      By Apply/andP; Split; RightBy EApply ltn_trans; EAuto.
    Case/set0Pn: (disjoint_gm_disk Hi'i); Exists u.
    By Rewrite: /setI !diskN_E /setU Hu Hui orbT.
  Rewrite: leq_eqVlt in Hi'; Case/setU1P: Hi' => [Di' | Hi'].
    By Rewrite: -Di' /diskE /setD Hu in Hui.
  Step Hii': (regpair i i').
    By Apply/andP; Split; RightBy EApply ltn_trans; EAuto.
  Case/set0Pn: (disjoint_gm_disk Hii'); Exists u.
  By Rewrite: /setI !diskN_E /setU Hu Hui orbT.
Pose ri' := (preimage_seq h' ri).
Step Hij: (regpair i j) By Apply/andP; Split.
Step Dri': (maps h' ri') = ri.
  Apply: maps_preimage => [x Hx]; Rewrite: Hh' /setC HhjE; Apply/nandP; Right.
  Move: (negbI (set0P (disjoint_gm_disk Hij) (h x))).
  By Rewrite: /setI diskN_E /setU -Dri (mem_maps Ih) Hx.
Step []: ri' = (preimage_seq [x:g'](h (h' x)) (gm_ring i)).
  Apply (inj_maps Ih'); Apply (inj_maps Ih); Rewrite: Dri' Dri -maps_comp.
  Apply esym; Apply: maps_preimage=> [u Hu].
  Rewrite: -Dri -Dri' -maps_comp in Hu; Case/mapsP: Hu => [x _ []]; Apply codom_f.
Step Uri': (uniq (rev ri')).
  Rewrite: uniq_rev -(uniq_maps Ih') Dri' -(uniq_maps Ih) Dri; Apply simple_uniq.
  By Case/andP: (scycle_gm_ring (ltn_trans Hi Hj)).
Apply: (cycle_from_next Uri') => [x Hx]; Apply/eqP; Apply Ih'.
Rewrite: -(next_maps Ih' Uri') -(mem_maps Ih') maps_rev Dri' in Hx *.
Rewrite: -((node (h' x)) =P ? (next_cycle Hri Hx)); Apply Hh'N.
Rewrite: /setC -(mem_maps Ih') Drj' mem_rev; Apply/idP=> [Hxj].
Case/set0Pn: (disjoint_gm_disk Hij); Exists (h (h' x)).
By Rewrite: /setI !diskN_E /setU -Dri -Drj !(mem_maps Ih) Hxj -mem_rev Hx.
Qed.

Definition grid_map : hypermap :=
  let (g, _, _, _, _, _, _, _, _) = has_cutout in (dual g).

Lemma planar_bridgeless_grid_map : (planar_bridgeless grid_map).
Proof.
Rewrite: /grid_map; Case: has_cutout => [g h Ih Hg Hh HhE HhN HhF Hgr].
Split; Rewrite: ?planar_dual ?bridgeless_dual //.
Step EitS: (n : nat) (iter n S (0)) = n By Elim=> // *; Congr S.
Pose ri := [i](preimage_seq h (gm_ring i)).
Step Eri: (i : nat) (ltn i nbreg) -> (maps h (ri i)) = (gm_ring i).
  Move=> i Hi; Apply: maps_preimage=> [u Hu].
  Case: (Hh u) => [[j Hj Huj] | [x []]]; RightBy Apply codom_f.
  Case: (ltnP i j) => [Hij].
    Step Hijn: (regpair i j) By Rewrite: /regpair Hij.
    Case/idP: (set0P (disjoint_gm_disk Hijn) u).
    By Rewrite: /setI !diskN_E /setU Hu Huj orbT.
  Rewrite: leq_eqVlt in Hij; Case/setU1P: Hij => [Dj | Hji].
    By Rewrite: /diskE /setD Dj Hu in Huj.
  Step Hjin: (regpair j i) By Rewrite: /regpair Hji.
  Case/idP: (set0P (disjoint_gm_disk Hjin) u).
  By Rewrite: /setI !diskN_E /setU Hu Huj orbT.
Step Hri: (i : nat) (ltn i nbreg) ->
  (x : g) (gm_ring i (h x)) -> (cnode x) =1 (ri i).
  Move=> i Hi x Hx y; Rewrite: -mem_rev; Apply: fconnect_cycle; LeftBy Apply: Hgr.
  By Rewrite: mem_rev -(mem_maps Ih) Eri.
Apply/set0P=> [x]; Case: (hasPx [i](gm_ring i (h x)) (traject S (0) nbreg)).
  Case=> [i']; Case/trajectP=> [i Hi []] {i'}; Rewrite: EitS.
  Move=> Hx; Rewrite: (Hri ? Hi) // -(mem_maps Ih) HhE Eri //.
  Move: Hx; Rewrite: -!(mem_maps HgmbE) maps_gm_ring //= !mring_def gedge2.
  By Case/andP; Case/esym; Rewrite andbF.
Move=> Hx'; Step Hx: (i : nat) (ltn i nbreg) -> (gm_ring i (h x)) = false.
  Move=> i Hi; Apply/idP=> [Hx]; Case: Hx'; Exists i; RightDone.
  By Apply/trajectP; Exists i.
Apply/idP=> [Hex] {Hx'}; Step Hhex: (cnode (h x) (h (edge x))).
  Case/connectP: Hex => [p Hp []].
  Elim: p x Hx Hp => [|y p Hrec] x Hx; LeftBy Rewrite connect0.
  Case: (HhN x) => [[i Hi Hix] | Dnx]; LeftBy Rewrite: Hx in Hix.
  Rewrite: cnode1 -Dnx; Case/andP; Case/eqP=> [] {y}; Apply: Hrec.
  Move=> i Hi; Apply/idP=> [Hnx]; Case/idP: (Hx ? Hi); Rewrite: -Eri ?maps_f //.
  By Rewrite: -(Hri ? Hi ? Hnx) Snode fconnect1.
Rewrite: HhE in Hhex; Move/h: x Hhex {Hx Hex} => u Hu.
Case Hfu: (bbf (gmbE u)).
  Pose ebf := (preimage_seq gmbE (rev bbf)).
  Step Debf : (maps gmbE ebf) = (rev bbf).
    Apply: maps_preimage=> [x Hx]; Apply/set0Pn.
    Case: (subdIoptP gmdartseq x) => [v _ [] | ]; LeftBy Exists v; Apply: set11.
    By Rewrite: /gmdartseq mem_cat /setU -mem_rev Hx.
  Step Uebf: (uniq ebf) By Rewrite: -(uniq_maps HgmbE) Debf uniq_rev uniq_cm_frame.
  Step Hebf: (fcycle node ebf).
    Apply: (cycle_from_next Uebf) {u Hu Hfu} => [u Hu]; Apply/eqP; Apply HgmbE.
    Rewrite: -(next_maps HgmbE Uebf) Debf (next_rev uniq_cm_frame) /= -/(gmbE u).
    By Rewrite: /gmnode -mem_rev -Debf (mem_maps HgmbE) Hu.
  Step Hfeu: (bbf (gmbE (edge u))).
    Rewrite: -mem_rev -Debf (mem_maps HgmbE) in Hfu.
    By Rewrite: -mem_rev -Debf (mem_maps HgmbE) -(fconnect_cycle Hebf Hfu).
  Move: Hfu Hfeu; Rewrite: !cm_frame_def /=; Case/andP; Case/esym.
  By Rewrite andbF.
Cut (halfg (gmbE u)) = (halfg (gmbE (edge u))).
  Apply: (elimF eqP); Apply: neq_halfg_edge.
Case/connectP: Hu => [p Hp []]; Elim: p u Hfu Hp => //= [v p Hrec] u Hu.
Rewrite: {1}/eqdf /eqd /= -/(gmbE u) -/(gmbE v) {1}/gmnode Hu; Case/andP.
Rewrite: -{2 (gmbE u)}gmonicN halfg_face; Move/eqP=> Dv; Rewrite Dv; Apply: Hrec.
Rewrite: -Dv cm_frame_def andbC -halfg_face gmonicN -gm_grid_def.
Move: (subd_mem u); Rewrite: -/(gmbE u) /gmdartseq mem_cat /setU Hu /=.
By Case/esym.
Qed.

Lemma grid_map_coloring : (four_colorable grid_map) ->
  (EX k | (i : nat) (ltn i nbreg) -> (ltn (k i) (4))
        & (i, j : nat) (regpair i j) -> (ab_adj ab0 i j) -> (negb (k i) =d (k j))).
Proof.
Rewrite: /grid_map; Case: has_cutout => [g h Ih Hg Hh HhE HhN HhF Hgr].
Case: (four_colorable_dual g) => [H _] H'; Case/H: H' {H} => [k [HkE HkN]].
Pose ri := [i](preimage_seq h (gm_ring i)).
Step Eri: (i : nat) (ltn i nbreg) -> (maps h (ri i)) = (gm_ring i).
  Move=> i Hi; Apply: maps_preimage=> [u Hu].
  Case: (Hh u) => [[j Hj Huj] | [x []]]; RightBy Apply codom_f.
  Case: (ltnP i j) => [Hij].
    Step Hijn: (regpair i j) By Rewrite: /regpair Hij.
    Case/idP: (set0P (disjoint_gm_disk Hijn) u).
    By Rewrite: /setI !diskN_E /setU Hu Huj orbT.
  Rewrite: leq_eqVlt in Hij; Case/setU1P: Hij => [Dj | Hji].
    By Rewrite: /diskE /setD Dj Hu in Huj.
  Step Hjin: (regpair j i) By Rewrite: /regpair Hji.
  Case/idP: (set0P (disjoint_gm_disk Hjin) u).
  By Rewrite: /setI !diskN_E /setU Hu Huj orbT.
Step Hri: (i : nat) (ltn i nbreg) -> (x : g) (ri i x) -> (cnode x) =1 (ri i).
  Move=> i Hi x Hx y; Rewrite: -mem_rev.
  By Apply: fconnect_cycle; [Apply: Hgr | Rewrite mem_rev].
Pose sc := (Seq Color0 Color1 Color2 Color3).
Exists [i](if pick x in (ri i) then (index (k x) sc) else (0)).
  By Move=> i _; Case: (pick (ri i)) => // [x]; Case (k x).
Move=> i j Hij; Rewrite: -ab_adj_refine; Move/(Habcm2 Hij); Rewrite: /cm_adj.
Case/hasP=> [x0]; Case: (andP Hij) => [Hi' Hj]; Def: Hi := (ltn_trans Hi' Hj).
Rewrite: -!maps_gm_ring //; Move/mapsP=> [u Hui Dx0].
Step []: (gmbE (edge u)) = (gedge x0) By Rewrite: -Dx0.
Rewrite: ~{x0 Dx0}(mem_maps HgmbE); Move: Hui; Rewrite: -!Eri //.
Case/mapsP=> [x Hx []] {u}; Rewrite: -HhE (mem_maps Ih); Move=> Hex.
Case: (pickP (ri i)) => [ex' Hex' | Dri']; RightBy Rewrite Dri' in Hex.
Rewrite: -(Hri ? Hi ? Hex') in Hex; Rewrite: (fconnect_invariant HkN Hex).  
Case: (pickP (ri j)) => [x' Hx' | Drj']; RightBy Rewrite Drj' in Hx.
Rewrite: -(Hri ? Hj ? Hx') in Hx; Rewrite: (fconnect_invariant HkN Hx).  
By Move: (HkE x); Rewrite: /invariant; Case (k x); Case (k (edge x)).
Qed.

End GridMap.

Unset Implicit Arguments.


