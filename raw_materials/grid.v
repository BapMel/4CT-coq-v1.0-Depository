(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require tacticext.
Require boolprop.
Require funs.
Require hypermap.
Require dataset.
Require natprop.
Require seq.
Require paths.
Require znat.

Set Implicit Arguments.

(*    Geometry over an integer grid, that is, raster graphics.         *)
(* We define integer point arithmetic, which we then use to define     *)
(* coordinates for four kinds of basic geometric objects:              *)
(*   - grid points                                                     *)
(*   - grid squares (pixels), whose vertices are adjacent gid points   *)
(*     They are referenced by their lower left corner.                 *)
(*   - grid darts, the sides of the grid squares, oriented counter-    *)
(*     clockwise. The coordinates of a dart is the sum of the          *)
(*     coordinates of its start point and the coordinates of the       *)
(*     square it belongs to.                                           *)
(*   - rectangles composed of grid squares. The coordinates of a       *)
(*     rectangle are the coordinates of the left/right/top/bottom-most *)
(*     pixel it contains (thus the top/right coordinates are one less  *)
(*     than the coordiates of the top/right-most grid points in the    *)
(*     frame).                                                         *)
(* The coordinate system for darts has some nice properties: it's easy *)
(* to recover the coordinates of the corresponding pixel (just divide  *)
(* the coordinates by 2) and the orientation (the remainder of that    *)
(* division by 2). Thus we can use integer arithmetic to put an        *)
(* infinite hypermap structure on the integer grid. These coordinates  *)
(* also behave nicely with respect to binary subdivision, which we use *)
(* heavily in the discretization proof.                                *)
(*   Finally, we define some intersection and union operations on      *)
(* integer rectangles (with half-planes and individual pixels, resp.). *)

Inductive gpoint : Set := Gpoint : znat -> znat -> gpoint.

Definition eqgp [p1, p2 : gpoint] : bool := 
 let (x1, y1) = p1 in let (x2, y2) = p2 in (andb x1 =d x2 y1 =d y2).

Lemma eqgpP : (reflect_eq eqgp).
Proof.
Move=> [x1 y1] [x2 y2]; Apply: (iffP andP) => /=; LeftBy Case; Do 2 Case/eqP.
By Injection=> [] []; Split; Apply set11.
Qed.

Canonical Structure gpointData := (DataSet eqgpP).

Definition gpointset : Set := (set gpointData).

Definition gpointseq : Set := (seq gpointData).

Identity Coercion seq_gpointseq : gpointseq >-> seq.
Identity Coercion set_gpointset : gpointset >-> set.

Definition addg [p1, p2 : gpoint] : gpoint :=
  let (x1, y1) = p1 in let (x2, y2) = p2 in (Gpoint (addz x1 x2) (addz y1 y2)).

Lemma addgA : (p1, p2, p3 : gpoint)
  (addg p1 (addg p2 p3)) = (addg (addg p1 p2) p3).
Proof. By Move=> [x1 y1] [x2 y2] [x3 y3]; Rewrite: /= !addzA. Qed.

Lemma addgC : (p1, p2 : gpoint)
  (addg p1 p2) = (addg p2 p1).
Proof. By Move=> [x1 y1] [x2 y2]; Rewrite: /= addzC (addzC y1). Qed.

Lemma addgCA : (p1, p2, p3 : gpoint)
  (addg p1 (addg p2 p3)) = (addg p2 (addg p1 p3)).
Proof. By Move=> *; Rewrite: !addgA (addgC p1). Qed.

Definition halfg [p : gpoint] : gpoint :=
  let (x, y) = p in (Gpoint (halfz x) (halfz y)).

Lemma halfg_add_double : (p1, p2 : gpoint)
  (halfg (addg p1 (addg p2 p2))) = (addg (halfg p1) p2).
Proof. By Move=> [x1 y1] [x2 y2]; Rewrite: /= !halfz_add_double. Qed.

Lemma halfg_double : (p : gpoint) (halfg (addg p p)) = p.
Proof. By Move=> [x y]; Rewrite: /= !halfz_double. Qed.

(* An explicit enumeration for the parity of points on an even grid.         *)

Inductive gbits : Set := Gb00 : gbits | Gb10 : gbits | Gb11 : gbits | Gb01 : gbits.

Definition eqgb [d1, d2 : gbits] : bool :=
  Cases d1 d2 of
    Gb00 Gb00 => true
  | Gb10 Gb10 => true
  | Gb11 Gb11 => true
  | Gb01 Gb01 => true
  | _ _ => false
  end.

Lemma eqgbP : (reflect_eq eqgb). Proof. By Do 2 Case; Constructor. Qed.

Canonical Structure gbitsData := (DataSet eqgbP).

Coercion gbits_to_gpoint :=
  [d]Cases d of
    Gb00 => (Gpoint (Znat 0) (Znat 0))
  | Gb10 => (Gpoint (Znat 1) (Znat 0))
  | Gb11 => (Gpoint (Znat 1) (Znat 1))
  | Gb01 => (Gpoint (Znat 0) (Znat 1))
  end.

Definition oddg [p : gpoint] : gbits :=
  let (x, y) = p in Cases (oddz x) (oddz y) of
    false false => Gb00
  | true  false => Gb10
  | true  true  => Gb11
  | false true  => Gb01
  end.

Lemma oddg_add_double : (p1, p2 : gpoint)
  (oddg (addg p1 (addg p2 p2))) = (oddg p1).
Proof. By Move=> [x1 y1] [x2 y2] /=; Rewrite: !oddz_add !addbb !addbF.  Qed.

Lemma oddg_double : (p : gpoint) (oddg (addg p p)) = Gb00.
Proof. By Move=> [x y] /=; Rewrite: !oddz_add !addbb. Qed.

Lemma oddg_bits : (d : gbits) (oddg d) = d. Proof. By Case. Qed.

Lemma halfg_bits : (d : gbits) (halfg d) = Gb00. Proof. By Case. Qed.

Lemma gb00I : (Gpoint (Znat 0) (Znat 0)) = Gb00. Proof. Done. Qed.
Lemma gb11I : (Gpoint (Znat 1) (Znat 1)) = Gb11. Proof. Done. Qed.

Lemma add0g : (p : gpoint) (addg Gb00 p) = p.
Proof. By Case=> [[mx|nx] [my|ny]]. Qed.

Lemma addg0 : (p : gpoint) (addg p Gb00) = p.
Proof. By Move=> *; Rewrite: addgC add0g. Qed.

Definition oppg [p : gpoint] : gpoint :=
  let (x, y) = p in (Gpoint (oppz x) (oppz y)).

Lemma addg_opp : (p : gpoint) (addg p (oppg p)) = Gb00.
Proof. By Move=> [x y]; Rewrite: /= !addz_opp. Qed.

Lemma addg_inv : (p : gpoint) (monic (addg p) (addg (oppg p))).
Proof. By Move=> p1 p2; Rewrite: addgCA addgA addg_opp add0g. Qed.

Definition consg [d : gbits; p : gpoint] : gpoint := (addg d (addg p p)).

Lemma consgI : (d : gbits; p : gpoint) (addg d (addg p p)) = (consg d p).
Proof. Done. Qed.

Lemma consg_odd_half : (p : gpoint) (consg (oddg p) (halfg p)) = p.
Proof.
Move=> [x y]; Rewrite: -{3 x}odd_double_halfz -{3 y}odd_double_halfz /=.
By Case (oddz x); Case (oddz y).
Qed.

Lemma oddg_cons : (d : gbits; p : gpoint) (oddg (consg d p)) = d.
Proof. By Move=> *; Rewrite: /consg oddg_add_double oddg_bits. Qed.

Lemma halfg_cons : (d : gbits; p : gpoint) (halfg (consg d p)) = p.
Proof. By Move=> *; Rewrite: /consg halfg_add_double halfg_bits add0g. Qed.

Lemma halfg_add : (p1, p2 : gpoint)
  (halfg (addg p1 p2)) = (addg (halfg (addg p1 (oddg p2))) (halfg p2)).
Proof.
By Move=> p1 p2; Rewrite: -{1 p2}consg_odd_half /consg addgA halfg_add_double.
Qed.

Lemma oddg_add : (p1, p2 : gpoint)
  (oddg (addg p1 p2)) = (oddg (addg p1 (oddg p2))).
Proof.
By Move=> p1 p2; Rewrite: -{1 p2}consg_odd_half /consg addgA oddg_add_double.
Qed.

(* Turning counterclockwise around a pixel square.   *)

Definition ccw [d : gbits] : gbits :=
  Cases d of Gb00 => Gb10 | Gb10 => Gb11 | Gb11 => Gb01 | Gb01 => Gb00 end.

Lemma ccw4 : (d : gbits) (ccw (ccw (ccw (ccw d)))) = d. Proof. By Case. Qed.

Lemma addg_ccw2 : (d : gbits) (addg d (ccw (ccw d))) = Gb11. Proof. By Case. Qed.

(* The dart interpretation of points: the half point gives the coordinates of *)
(* the origin of the square, the parity bits specify the side. The origin and *)
(* target of each dart (end0g and end1g, respectively) are computed using the *)
(* functions above.                                                           *)

Definition end0g [p : gpoint] : gpoint := (addg (halfg p) (oddg p)).
Definition end1g [p : gpoint] : gpoint := (addg (halfg p) (ccw (oddg p))).

Lemma halfg_add_odd : (p : gpoint) (halfg (addg p (oddg p))) = (end0g p).
Proof. By Move=> p; Rewrite: addgC halfg_add halfg_double addgC. Qed.

Lemma halfg_add1 : (p : gpoint) (halfg (addg p Gb11)) = (end0g p).
Proof. By Move=> p; Rewrite: addgC halfg_add addgC /end0g; Case (oddg p). Qed.

(* The infinite hypermap of a grid. *)

Definition gedge [p : gpoint] : gpoint :=
  let d = (ccw (oddg p)) in (addg p (addg d (oppg (ccw (ccw d))))).

Lemma oddg_edge : (p : gpoint) (oddg (gedge p)) = (ccw (ccw (oddg p))).
Proof. By Move=> p; Rewrite: /gedge addgC oddg_add; Case (oddg p). Qed.

Lemma gedge2 : (p : gpoint) (gedge (gedge p)) = p.
Proof.
Move=> p; Rewrite: {1}/gedge oddg_edge /gedge ccw4 -!addgA addg_inv addg_opp.
Apply: addg0.
Qed.

Definition neg1g : gpoint := (Gpoint (Znat -1) (Znat -1)).

Lemma halfg_edge : (p : gpoint)
  (halfg (gedge p)) = (addg (halfg p) (addg (oddg p) (addg (ccw (oddg p)) neg1g))).
Proof. By Move=> p; Rewrite: /gedge addgC halfg_add addgC; Case (oddg p). Qed.

Lemma neq_halfg_edge : (p : gpoint) ((halfg p) =d (halfg (gedge p))) = false.
Proof.
Move=> p; Rewrite: -{(halfg p)}addg0 halfg_edge (monic_eqd (addg_inv (halfg p))).
By Case (oddg p).
Qed.

Lemma end0g_edge : (p : gpoint) (end0g (gedge p)) = (end1g p).
Proof.
By Move=> p; Rewrite: /end0g halfg_edge oddg_edge -addgA /end1g; Case (oddg p).
Qed.

Lemma end1g_edge : (p : gpoint) (end1g (gedge p)) = (end0g p).
Proof.
By Move=> p; Rewrite: /end1g halfg_edge oddg_edge -addgA /end0g; Case (oddg p).
Qed.

Definition gnode [p : gpoint] : gpoint :=
  (addg p (addg (oddg p) (oppg (ccw (oddg p))))).

Definition gface [p : gpoint] : gpoint :=
  (consg (ccw (oddg p)) (halfg p)).

Lemma gface_def : (p : gpoint)
 (gface p) = (addg p (addg (ccw (oddg p)) (oppg (oddg p)))).
Proof.
By Move=> p; Rewrite: -{2 p}consg_odd_half addgC /consg -!addgA addg_inv.
Qed.

Lemma gface4 : (p : gpoint) (gface (gface (gface (gface p)))) = p.
Proof.
By Move=> p; Rewrite: /gface !oddg_cons !halfg_cons ccw4 consg_odd_half.
Qed.

Lemma oddg_face : (p : gpoint) (oddg (gface p)) = (ccw (oddg p)).
Proof. Move=> p; Apply: oddg_cons. Qed.

Lemma halfg_face : (p : gpoint) (halfg (gface p)) = (halfg p).
Proof. Move=> p; Apply: halfg_cons. Qed.

Lemma end0g_face : (p : gpoint) (end0g (gface p)) = (end1g p).
Proof. By Move=> p; Rewrite: /end0g oddg_face halfg_face. Qed.

Lemma gnode_face : (p : gpoint) (gnode (gface p)) = (gedge p).
Proof.
Move=> p; Rewrite: /gedge addgC /gnode oddg_face /gface addgC.
By Rewrite: -{7 p}consg_odd_half /consg !addgA; Case (oddg p).
Qed.

Lemma gmonicE : (monic3 gedge gnode gface).
Proof. By Move=> p; Rewrite: /= gnode_face gedge2. Qed.

Lemma gmonicF : (monic3 gface gedge gnode).
Proof. By Move=> p; Rewrite: /= gnode_face gedge2. Qed.

Lemma gmonicN : (monic3 gnode gface gedge).
Proof. By Move=> p; Rewrite: -{p}gface4 gnode_face gedge2. Qed.

Lemma end0g_node : (p : gpoint) (end0g (gnode p)) = (end0g p).
Proof. By Move=> p; Rewrite: -{2 p}gmonicN end0g_face end1g_edge. Qed.

Lemma oddg_node : (p : gpoint) (oddg (gnode p)) = (ccw (oddg p)).
Proof. By Move=> p; Rewrite: -{2 p}gmonicN oddg_face oddg_edge ccw4. Qed.

Lemma gnode4 : (p : gpoint) (gnode (gnode (gnode (gnode p)))) = p.
Proof.
Move=> p; Do 4 Rewrite: {1}/gnode ?oddg_node ?ccw4.
By Rewrite: -!addgA !addg_inv addg_opp addg0.
Qed.

Lemma same_end0g : (p, q : gpoint)
  (end0g p) = (end0g q) -> (traject gnode p (4) q).
Proof.
Move=> p q; Move/esym=> Epq; Rewrite: /end0g addgC in Epq.
Rewrite: -{q}consg_odd_half /consg addgA Epq.
Rewrite: (monic_move (addg_inv ?) Epq) addgCA addgC -!addgA addgCA 2!addgA.
Rewrite: -(addgA (oddg p)) consgI consg_odd_half.
Rewrite: /= /setU1 {1 2 4}/gnode !oddg_node {1 2}/gnode oddg_node.
Rewrite: /gnode -!addgA !addg_inv -{1 p}addg0 !(monic_eqd (addg_inv p)).
By Case (oddg p); Case (oddg q).
Qed.

Lemma halfg_iter_face : (i : nat; p : gpoint) (halfg (iter i gface p)) = (halfg p).
Proof. By Elim=> //= [i Hrec] p; Rewrite: halfg_face. Qed.

Lemma oddg_iter_face : (i : nat; p : gpoint)
  (oddg (iter i gface p)) = (iter i ccw (oddg p)).
Proof. By Elim=> //= [i Hrec] p; Rewrite: oddg_face Hrec. Qed.

(* Local grid refinement. *)

Definition refined_in [m, r : gpointset] : Prop :=
  (p, q : gpoint) (r p) -> (halfg q) = (halfg p) -> (m q) = (m p).

Lemma refined_in_face : (m, r : gpointset) (refined_in m r) ->
  (p : gpoint) (r p) -> (i : nat) (m (iter i gface p)) = (m p).
Proof. By Move=> m r Hm p Hp i; Apply: Hm; RightBy Apply halfg_iter_face. Qed.

(* Rectangles on the grid. *)

Inductive grect : Set := Grect : (xmin, xmax, ymin, ymax : znat) grect.

Definition mem_grect [r : grect] : gpointset := [p]
  let (xmin, xmax, ymin, ymax) = r in let (x, y) = p in
  (and4b (leqz xmin x) (leqz x xmax) (leqz ymin y) (leqz y ymax)).

Coercion mem_grect : grect >-> gpointset.

Definition zwidth [xmin, xmax : znat] : nat :=
  if (subz xmax xmin) is (Zpos w) then (S w) else (0).

Definition gwidth [r : grect] : nat :=
  let (xmin, xmax, _, _) = r in (zwidth xmin xmax).

Definition gheight [r : grect] : nat :=
  let (_, _, ymin, ymax) = r in (zwidth ymin ymax).

Definition zspan [xmin, xmax : znat] : (seq znatData) :=
  (traject incz xmin (zwidth xmin xmax)).

Lemma size_zspan : (xmin, xmax : znat)
  (size (zspan xmin xmax)) = (zwidth xmin xmax).
Proof. By Move=> *; Rewrite: /zspan size_traject. Qed.

Lemma mem_zspan : (xmin, xmax, x : znat)
  (zspan xmin xmax x) = (andb (leqz xmin x) (leqz x xmax)).
Proof.
Move=> x0 x1 x; Rewrite: -{2 x1}(subz_add x0) -addz_subA /zspan /zwidth.
Case: {x1}(subz x1 x0) => [n|m].
  Elim: n x0 => [|n Hrec] x0; LeftBy Rewrite: addz0 -eqz_leq /= /setU1 orbF.
  Rewrite: leqz_inc /= {1}/setU1; Case: (x0 =P x) => [[] | _].
    By Rewrite: /= -{1 x0}addz0 leqz_add2l.
  By Rewrite: -add1n zpos_addn addzA -incz_def /= -Hrec.
By Rewrite: /leqz -subz_sub -oppz_sub; Case: (subz x x0) => [[|n]|m'].
Qed.

Lemma uniq_zspan : (xmin, xmax : znat) (uniq (zspan xmin xmax)).
Proof.
Move=> x0 x1; Rewrite: /zspan /zwidth; Case: {x1}(subz x1 x0) => // [n].
Elim: {n}(S n) x0 => //= [n Hrec] x0; Rewrite: ~Hrec andbT; Case: n => // [n].
Apply negbI; Move: (mem_zspan (incz x0) (addz (incz x0) (Zpos n)) x0).
By Rewrite: {1}/leqz {3 (incz x0)}incz_def /zspan /zwidth !subz_add.
Qed.

Definition enum_grect [r : grect] : gpointseq :=
  let (xmin, xmax, ymin, ymax) = r in
  (foldr [x](cat (maps (Gpoint x) (zspan ymin ymax))) seq0 (zspan xmin xmax)).

Lemma mem_enum_grect : (r : grect) (enum_grect r) =1 r.
Proof.
Move=> [x0 x1 y0 y1] [x y] /=; Rewrite: andbA -!mem_zspan.
Elim: {x0 x1}(zspan x0 x1) => //= [x0 xs Hrec].
Rewrite: /setU1 demorgan2 mem_cat /setU ~Hrec; Congr orb.
Rewrite andbC; Elim: {y0 y1}(zspan y0 y1) => //= [y0 ys Hrec].
By Rewrite: /setU1 demorgan2 ~Hrec; Congr orb; Rewrite andbC.
Qed.

Lemma uniq_enum_grect : (r : grect) (uniq (enum_grect r)).
Proof.
Move=> [x0 x1 y0 y1] /=.
Elim: {x0 x1}(zspan x0 x1) (uniq_zspan x0 x1) => //= [x0 xs Hrec].
Move/andP=> [Hx0 Hxs]; Rewrite: uniq_cat ~Hrec ~{Hxs}// andbT.
Rewrite: uniq_maps ?uniq_zspan; RightBy Move=> y y'; Injection=> Dy.
Elim: xs Hx0 => //= [x1 xs Hrec]; Move/norP=> [Hx01 Hx0].
Rewrite: has_cat ~{Hrec Hx0}(negbE (Hrec Hx0)) orbF.
Apply/hasP=> [[p]]; Move/mapsP=> [y _ []]; Move/mapsP=> [y' _].
By Injection=> _ Dx0; Case/eqP: Hx01.
Qed.

Definition garea [r : grect] : nat := (mult (gwidth r) (gheight r)).

Lemma size_enum_grect :  (r : grect) (size (enum_grect r)) = (garea r).
Proof.
Move=> [x0 x1 y0 y1]; Rewrite: /garea /= -!size_zspan.
Elim: {x0 x1}(zspan x0 x1) => //= [x0 xs Hrec].
By Rewrite: size_cat size_maps Hrec.
Qed.
   
Lemma ltn0_garea : (r : grect; p : gpoint) (r p) -> (ltn (0) (garea r)).
Proof.
By Move=> r p; Rewrite: -mem_enum_grect -size_enum_grect; Case (enum_grect r).
Qed.

Definition sub_grect [r1, r2 : grect] : bool :=
  let (xmin1, xmax1, ymin1, ymax1) = r1 in
  let (xmin2, xmax2, ymin2, ymax2) = r2 in
  (and4b (leqz xmin2 xmin1) (leqz xmax1 xmax2)
         (leqz ymin2 ymin1) (leqz ymax1 ymax2)).

Lemma mem_sub_grect : (r1, r2 : grect) (sub_grect r1 r2) -> (sub_set r1 r2).
Proof.
Move=> [x10 x11 y1x y11] [x20 x21 y20 y21]; Move/and4P=> [Hx0 Hx1 Hy0 Hy1] [x y].
Move/and4P=> [Hxx0 Hxx1 Hyy0 Hyy1]; Apply/and4P; Split; EApply leqz_trans; EAuto.
Qed.

Lemma garea_sub_rect : (r1, r2 : grect)
  (sub_set r1 r2) -> (leq (garea r1) (garea r2)).
Proof.
Move=> r1 r2 Hr12; Rewrite: -!size_enum_grect; Move: (uniq_enum_grect r1).
Pose p1 := (enum_grect r1); Pose p2 := (enum_grect r2).
Step Hp12: (sub_set p1 p2).
  By Move=> p; Rewrite: /p1 /p2 !mem_enum_grect; Apply: Hr12.
Elim: p1 p2 Hp12 {Hr12} => //= [p p1 Hrec] p2 Hp12; Move/andP=> [Hp1p Hp1].
Case/rot_to: (Hp12 ? (setU11 ? ?)) => [i p2' Dp2].
Rewrite: -(size_rot i p2) Dp2 /= ltnS ~Hrec //.
Move=> q Hq; Move: (Hp12 ? (setU1r ? Hq)); Rewrite: -(mem_rot i) Dp2.
By Case/setU1P=> // [Dp]; Case/idP: Hp1p; Rewrite Dp.
Qed.

Lemma ltn_garea_sub_rect : (r1, r2 : grect)
  (sub_set r1 r2) -> (p : gpoint) (setD r2 r1 p) -> (ltn (garea r1) (garea r2)).
Proof.
Move=> r1 r2 Hr12 p0; Rewrite: /setD -!mem_enum_grect -!size_enum_grect.
Move: (uniq_enum_grect r1); Pose p1 := (enum_grect r1); Pose p2 := (enum_grect r2).
Step Hp12: (sub_set p1 p2).
  By Move=> p; Rewrite: /p1 /p2 !mem_enum_grect; Apply: Hr12.
Elim: p1 p2 Hp12 {Hr12} => [|p p1 Hrec] p2 Hp12; LeftBy Case p2.
Move/andP=> [Hp1p Hp1] Hp0.
Case/rot_to: (Hp12 ? (setU11 ? ?)) => [i p2' Dp2].
Rewrite: -(size_rot i p2) Dp2 /= ltnS ~Hrec //.
  Move=> q Hq; Move: (Hp12 ? (setU1r ? Hq)); Rewrite: -(mem_rot i) Dp2.
  By Case/setU1P=> // [Dp]; Case/idP: Hp1p; Rewrite Dp.
By Move: Hp0; Rewrite: -(mem_rot i p2) Dp2 /= /setU1; Case (p =d p0).
Qed.

(* Grid refinement simply doubles the rectangle bounds. *)

Definition refine_rect [r : grect] : grect :=
  let (xmin, xmax, ymin, ymax) = r in
  (Grect (addz xmin xmin) (incz (addz xmax xmax))
         (addz ymin ymin) (incz (addz ymax ymax))).

Lemma mem_refine_rect : (r : grect; x : gpoint)
  (refine_rect r x) = (r (halfg x)).
Proof. By Move=> [x0 x1 y0 y1] [x y] /=; Rewrite: !leqz_halfl !leqz_halfr. Qed.

Lemma garea_refine_rect : (r : grect)
  (garea (refine_rect r)) = (double (double (garea r))).
Proof.
Step Ezw: (x, y : znat)
    (zwidth (addz x x) (incz (addz y y))) = (double (zwidth x y)).
  Move=> x y; Rewrite: /zwidth incz_def addzC -addz_subA -subz_sub -addz_subA.
  Rewrite: addzC -incz_def addzC -addz_subA; Case: (subz y x) => [n|m] //=.
  By Rewrite: -double_addnn doubleS.
Move=> [x0 x1 y0 y1]; Rewrite: /garea /gwidth /gheight /= !Ezw !double_addnn.
By Rewrite: /addn mult_plus_distr !mult_plus_distr_r.
Qed.

Lemma refine_rect_refined : (r : grect) (refined_in (refine_rect r) [_]true).
Proof. By Move=> r p q _ Hpq; Rewrite: !mem_refine_rect Hpq. Qed.

(* The 3x3 rectangle of squares that surround a central square. *)

Definition gtouch [p : gpoint] : grect :=
  let (x, y) = p in (Grect (decz x) (incz x) (decz y) (incz y)).

Lemma gtouch_refl : (p : gpoint) (gtouch p p).
Proof. By Move=> [x y]; Rewrite: /= !leq_z_incz !leq_decz_z. Qed.

Lemma gtouch_edge : (p : gpoint) (gtouch (halfg p) (halfg (gedge p))).
Proof.
Move=> p; Rewrite: halfg_edge; Case: (halfg p) => [x y].
Case (oddg p); Rewrite: /= addz0 -?incz_def -?decz_def;
  By Rewrite: leqzz leq_decz_incz leq_decz_z leq_z_incz.
Qed.

Lemma zspan_dec_inc : (x : znat)
  (zspan (decz x) (incz x)) = (Seq (decz x) x (incz x)).
Proof.
Move=> x; Rewrite: /zspan /zwidth incz_def decz_def subz_add2l -incz_def -decz_def.
By Rewrite: /= incz_dec.
Qed.

(* The half-grid that lies counter-clockwise from a dart. *)

Definition gchop [p, q : gpoint] : bool :=
  let (xp, yp) = (halfg p) in let (xq, yq) = q in
  Cases (oddg p) of
    Gb00 => (leqz yp yq)
  | Gb10 => (leqz xq xp)
  | Gb11 => (leqz yq yp)
  | Gb01 => (leqz xp xq)
  end.

Lemma gchop_halfg : (p : gpoint) (gchop p (halfg p)).
Proof.
By Move=> p; Rewrite: /gchop; Case: (halfg p) => *; Case (oddg p); Apply leqzz.
Qed.

Lemma eq_gchop_halfg : (p, q : gpoint) (halfg p) = q -> (gchop p q).
Proof. By Move=> p q []; Apply gchop_halfg. Qed.

Lemma gchop_edge : (p : gpoint) (gchop (gedge p)) =1 (setC (gchop p)).
Proof.
Move=> p; Rewrite: /gchop halfg_edge oddg_edge; Case: (halfg p) => [x y] [x' y'].
Case (oddg p); Rewrite: /= /addn /setC /= -?incz_def -?decz_def negb_leqz //;
  By Rewrite: -leqz_inc_dec.
Qed.

Lemma gchopFEF : (p : gpoint) (gchop (gface (gedge (gface p)))) = (gchop p).
Proof.
Move=> p; Do 2 Rewrite: /gchop halfg_face oddg_face ?halfg_edge ?oddg_edge.
By Case: (halfg p) => [x y]; Case (oddg p); Rewrite: /= addz0.
Qed.

(* Same as above, but extended by a unit band.              *)

Definition gchop1 [p : gpoint] : gpointset :=
  (gchop (gface (gface (gedge p)))).

Lemma gchop1I : (p : gpoint) (gchop (gface (gface (gedge p)))) = (gchop1 p).
Proof. Done. Qed.

Lemma gchop_chop1 : (p : gpoint) (sub_set (gchop p) (gchop1 p)).
Proof.
Move=> p; Rewrite: /gchop1 /gchop !halfg_face halfg_edge !oddg_face !oddg_edge.
Case: (halfg p) => [x y] [x' y']; Case: (oddg p) => *;
  Rewrite: /= /addn /= -?incz_def -?decz_def leqz_inc ?incz_dec ?leqz_inc2;
  By Apply/orP; Right.
Qed.

Lemma gtouch_chop1 : (p : gpoint) 
  (gtouch (halfg p)) =1 [q](all [p'](gchop1 p' q) (traject gface p (4))).
Proof.
Move=> p [x' y']; Rewrite: /traject /all /gchop1 /gchop andbT.
Rewrite: !halfg_face !halfg_edge !halfg_face !oddg_face !oddg_edge !oddg_face.
By Case: (halfg p) => [x y]; Case (oddg p);
  Rewrite: /gtouch /= /addn /setC /= -?incz_def -?decz_def; Repeat BoolCongr.
Qed.

Section ChopRect.

(* Chopping off half of a rectangle (and excluding the boundary). *)
(* The dividing line is given as the side of an internal square.  *)

Variable r : grect.

Definition gchop_rect [p : gpoint] : grect :=
  let (xmin, xmax, ymin, ymax) = r in let (x, y) = (halfg p) in
 Cases (oddg p) of
    Gb00 => (Grect xmin xmax (if (leqz ymin y) then y else ymin) ymax)
  | Gb10 => (Grect xmin (if (leqz x xmax) then x else xmax) ymin ymax)
  | Gb11 => (Grect xmin xmax ymin (if (leqz y ymax) then y else ymax))
  | Gb01 => (Grect (if (leqz xmin x) then x else xmin) xmax ymin ymax)
  end.

Lemma mem_gchop_rect : (p : gpoint) (gchop_rect p) =1 (setI r (gchop p)).
Proof.
Move=> p; Rewrite: /gchop_rect /gchop /setI.
Case: {}r (halfg p) => [x0 x1 y0 y1] [xp yp] [x y]; Rewrite: andbC.
Case: (oddg p) => /=; Repeat BoolCongr; Rewrite: ?andbA; Repeat Congr andb.
 Case Hyp: (leqz y0 yp); Case Hy: (leqz y0 y); Rewrite: ?andbF ?andbT //.
    By Apply: (introF idP ?)=> [H]; Case: (elimTn negPf (leqz_trans Hyp H)).
  By Symmetry; Apply: (leqz_trans ? Hy); Rewrite: leqz_inc -negb_leqz Hyp orbT.
 Case Hxp: (leqz xp x1); Case Hx: (leqz x x1); Rewrite: ?andbF ?andbT //.
    By Apply: (introF idP ?)=> [H]; Case: (elimTn negPf (leqz_trans H Hxp)).
  By Symmetry; Apply: (leqz_trans Hx ?); Rewrite: leqz_inc -negb_leqz Hxp orbT.
 Case Hyp: (leqz yp y1); Case Hy: (leqz y y1); Rewrite: ?andbF ?andbT //.
    By Apply: (introF idP ?)=> [H]; Case: (elimTn negPf (leqz_trans H Hyp)).
  By Symmetry; Apply: (leqz_trans Hy ?); Rewrite: leqz_inc -negb_leqz Hyp orbT.
 Case Hxp: (leqz x0 xp); Case Hx: (leqz x0 x); Rewrite: ?andbF ?andbT //.
    By Apply: (introF idP ?)=> [H]; Case: (elimTn negPf (leqz_trans Hxp H)).
  By Symmetry; Apply: (leqz_trans ? Hx); Rewrite: leqz_inc -negb_leqz Hxp orbT.
Qed.

Lemma gchop_rect_sub : (p : gpoint) (sub_set (gchop_rect p) r).
Proof. By Move=> p q; Rewrite: mem_gchop_rect; Case/andP. Qed.

Lemma gchop_rect_edge : (p : gpoint) (r (halfg (gedge p))) ->
  (q : gpoint) (gchop_rect p q) -> (gchop_rect p (halfg p)).
Proof.
Move=> p Hep [x' y']; Rewrite: !mem_gchop_rect /setI gchop_halfg andbT /gchop.
Case: {}r Hep => [x0 x1 y0 y1]; Rewrite: halfg_edge; Move: (halfg p) => [x y].
Case: {p}(oddg p); Rewrite: /= /addn /= ?addz0 -?incz_def -?decz_def -!andbA;
  Move/and4P=> [Hx0 Hx1 Hy0 Hy1]; Move/and5P=> [Hx0' Hx1' Hx2' Hx3' Hq];
  Apply/and4P; Split; First [
    Assumption
  | By Rewrite: leqz_dec; Apply/orP; Right
  | By Rewrite: leqz_inc; Apply/orP; Right
  | EApply leqz_trans; EAuto].
Qed.

Definition gchop1_rect [p : gpoint] : grect :=
  (gchop_rect (gface (gface (gedge p)))).

Lemma gchop1_rectI : (p : gpoint)
  (gchop_rect (gface (gface (gedge p)))) = (gchop1_rect p).
Proof. Done. Qed.

Lemma mem_gchop1_rect : (p : gpoint) (gchop1_rect p) =1 (setI r (gchop1 p)).
Proof. Move=> *; Apply: mem_gchop_rect. Qed.

End ChopRect.

(* Extending a recangle to cover a specific pixel.                          *)

Definition extend_grect [p : gpoint; r : grect] : grect :=
  let (xmin, xmax, ymin, ymax) = r in let (x, y) = p in
  (Grect (if (leqz xmin x) then xmin else x)
         (if (leqz x xmax) then xmax else x)
         (if (leqz ymin y) then ymin else y)
         (if (leqz y ymax) then ymax else y)).

Lemma mem_extend_grect : (p : gpoint; r : grect)
  (sub_set (setU1 p r) (extend_grect p r)).
Proof.
Move=> [x y] [x0 x1 y0 y1] q; Case/setU1P=> [[]|] /=.
  Apply/and4P; Split.
  By Case Hx: (leqz x0 x); RightBy Apply leqzz.
  By Case Hx: (leqz x x1); RightBy Apply leqzz.

  By Case Hy: (leqz y0 y); RightBy Apply leqzz.
  By Case Hy: (leqz y y1); RightBy Apply leqzz.
Case: q => [x' y'] /=; Move/and4P=> [Hx0 Hx1 Hy0 Hy1]; Apply/and4P.
  Split; Rewrite: -if_negb negb_leqz.
  Case Hx: (leqz (incz x) x0); RightDone.
  By Rewrite: leqz_inc; Apply/orP; Right; EApply leqz_trans; EAuto.
  Case Hx: (leqz (incz x1) x); RightDone.
  By Apply: (leqz_trans Hx1 ?); Rewrite: leqz_inc Hx orbT.
  Case Hy: (leqz (incz y) y0); RightDone.
  By Rewrite: leqz_inc; Apply/orP; Right; EApply leqz_trans; EAuto.
  Case Hy: (leqz (incz y1) y); RightDone.
  By Apply: (leqz_trans Hy1 ?); Rewrite: leqz_inc Hy orbT.
Qed.

Unset Implicit Arguments.


