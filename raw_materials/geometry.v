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

(* The geometrical interpretation of hypermaps, the definition of most of the *)
(* geometrical notions relevant to the statement and proof of the four color  *)
(* theorem :                                                                  *)
(*   - bridgeless and loopless maps.                                          *)
(*   - plain, precubic, cubic, quasicubic, and pentagonal maps.               *)
(*   - arities, simple paths, their bands and projections.                    *)
(*   - ring paths and adjacency.                                              *)
(* We also define a set of records that regroup various sets of geometrical   *)
(* properties of hypermaps, that are required at various points in the proof: *)
(*   - walkup jordan sew patch cube  no assumptions                           *)
(*   - snip                          planar                                   *)
(*   - revsnip                       planar, bridgeless, plain, connected     *)
(*   - proof induction               planar, bridgeless, plain, precubic (add *)
(*     (birkhoff contract embed)      cubic, pentagonal, connected later on)  *)
(*   - configuration (embed)         planar, bridgeless, plain, quasicubic,   *)
(*                                   connected, simple ring                   *)
(*   - kempe                         planar, plain, quasicubic, uniq ring     *)
(*   - quiz, quiztree                plain, cubic                             *)
(*   - quiz                          plain, quasicubic                        *)
(*   - part, redpart, hubcap         plain, cubic, pentagonal                 *)
(*   - discharge                     planar, plain, cubic, connected          *)
(* quiz and embed build and use an isomorphism from a configuration map to    *)
(* the coloring map, so they use two sets of assumptions.                     *)

Set Implicit Arguments.

Section BridgeAndLoopLess.

Variable g : hypermap. 

Definition bridgelessb : bool := (set0b [x : g](cface x (edge x))).
Definition bridgeless : Prop := (set0b [x : g](cface x (edge x))).

Lemma bridgeless_cface : bridgeless -> (x : g) (cface x (edge x)) = false.
Proof. By Move/set0P. Qed.

Definition loopless : Prop := (set0b [x : g](cnode x (edge x))).

End BridgeAndLoopLess.

Lemma bridgeless_dual : (g : hypermap) (bridgeless (dual g)) == (loopless g).
Proof.
Move=> g; PropCongr; Apply/set0P/set0P => [] /= Hg x.
  By Rewrite: Snode -(same_fconnect_finv (Inode g)) -{2 x}(finv_f (Iedge g)) Hg.
By Rewrite: (same_fconnect_finv (Inode g)) Snode -{2 x}(f_finv (Iedge g)) Hg.
Qed.

Lemma bridgeless_mirror : (g : hypermap) (bridgeless (mirror g)) == (bridgeless g).
Proof.
Move=> g; PropCongr; Apply/set0P/set0P => [] /= Hg x.
  Rewrite: Sface -{2 x}Eedge cface1 cface1r -(same_fconnect_finv (Iface g)).
  Apply: Hg.
Rewrite: (same_fconnect_finv (Iface g)) Sface /comp -cface1 -{2 x}Enode -cface1r.
Apply: Hg.
Qed.

Section EqmBridgeLess.

Variables g, g' : hypermap.
Hypothesis Eg': g =m g'.

Lemma eqm_bridgeless : (bridgeless g) == (bridgeless g').
Proof.
PropCongr; Case: {}g {}Eg' => [d e n f EgE] [e' n' f' Eg'E Ee _ Ef].
Congr [n](n =d (0)); Apply: eq_card => [x].
By Rewrite: /= Ee; Apply: eq_fconnect.
Qed.

Lemma eqm_loopless : (loopless g) == (loopless g').
Proof.
PropCongr; Case: {}g {}Eg' => [d e n f EgE] [e' n' f' Eg'E Ee En _].
Congr [n](n =d (0)); Apply: eq_card => [x].
By Rewrite: /= Ee; Apply: eq_fconnect.
Qed.

End EqmBridgeLess.

(*   Since edge and node arity are fixed, face arity plays a central role    *)
(* in the theory, so we use a special `arity' syntax to refer to it.         *)

Syntax constr level 0:
  arity_form [<<(APPLIST <<order>> (APPLIST (CONST hypermap.face) $_) $x)>>] ->
  [(OPFORM arity $x)]
| arity_noform [<<(APPLIST <<order>> (APPLIST (CONST hypermap.face) $_))>>] ->
  ["arity"].

Grammar constr constr10 : constr :=
  arity_explicit1 ["!" "arity" constr9($g)] -> [(!order $g face)]
| arity_explicit2 ["!" "arity" constr9($g) constr9($x)] -> [(!order $g face $x)]
with constr0 : constr :=
  arity_implicit ["arity"] -> [(order face)].

Section FacePaths.

(* Arity lemmas, and the other face-centric notions: simple paths, their    *)
(* projection, ring band, and (outer) ring kernel.                          *)

Variables n0 : nat; g : hypermap.

Lemma arity_cface : (x, y : g) (cface x y) -> (arity x) = (arity y).
Proof. By Move=> x y Hxy; Exact (eq_card (same_cface Hxy)). Qed.

Lemma arity_iter_face : (n : nat; x : g) (arity (iter n face x)) = (arity x).
Proof. By Move=> *; Apply: arity_cface; Rewrite: Sface fconnect_iter. Qed.

Lemma arity_face : (x : g) (arity (face x)) = (arity x).
Proof. Exact (arity_iter_face (1)). Qed.

Lemma iter_face_arity : (x : g) (iter (arity x) face x) = x.
Proof. Apply: iter_order; Exact (Iface g). Qed.

Lemma iter_face_subn : (n : nat; x : g)
  (leq n (arity x)) -> (iter (subn (arity x) n) face (iter n face x)) = x.
Proof.
Move=> n x Hn; Rewrite: -iter_plus addnI addnC (leq_add_sub Hn).
Apply iter_face_arity.
Qed.

Lemma arity_mirror : (!arity (mirror g)) =1 (!arity g).
Proof. Move=> x; Apply: eq_card; Exact (cface_mirror x). Qed.

Section SimplePaths.

Variables e : (rel g); p : (seq g).

Definition fband : (set g) := [x](has (cface x) p).

Lemma ring_fband : (subset p fband).
Proof.
By Apply/subsetP=> [x Hx]; Apply/hasP; Exists x; RightBy Apply connect0.
Qed.

Lemma fbandF : (fclosed face fband).
Proof.
Apply: (intro_closed (Sface ?)) => [x y Dy Hx]; Apply/hasP.
By Case/hasP: Hx => [z Hz Hxz]; Exists z; RightBy Rewrite: -(eqP Dy) -cface1.
Qed.

(* kernel can be defined as the complement of band, since it is only used *)
(* when r is the outer ring of a configuration.                           *)

Definition kernel : (set g) := (setC fband).

Lemma kernel_off_ring : (subset kernel (setC p)).
Proof. Rewrite: -disjoint_subset disjoint_sym; Exact ring_fband. Qed.

Lemma kernelF : (fclosed face kernel).
Proof. Apply: setC_closed; Exact fbandF. Qed.

Definition fproj [x : g] : g := (sub (froot face x) p (find (cface x) p)).

Lemma fprojP : (x : g) (fband x) -> (p (fproj x)) /\ (cface x (fproj x)).
Proof. By Move=> x Hx; Rewrite: /fproj mem_sub ?sub_find // -has_find. Qed.

Lemma fproj_cface : (x, y : g) (cface x y) -> (fproj x) = (fproj y).
Proof.
Move=> x y Hxy; Rewrite: /fproj (rootP (Sface g) Hxy).
Congr (!sub g); Apply: eq_find; Exact (same_cface Hxy).
Qed.

Definition simple : bool := (uniq (maps (froot face) p)).

Lemma simple_uniq : simple -> (uniq p).
Proof. Move=> Up; Exact (maps_uniq Up). Qed.

(* scycle is a coercion target. *)
Definition scycleb : bool := (andb (cycle e p) simple).
Definition scycle : Prop := (andb (cycle e p) simple).

Lemma scycle_cycle : scycle -> (cycle e p).
Proof. By Case/andP. Qed.

Lemma scycle_simple : scycle -> simple.
Proof. By Case/andP. Qed.

Lemma scycle_uniq : scycle -> (uniq p).
Proof. Move/scycle_simple; Exact simple_uniq. Qed.

Lemma scycle_ucycle : scycle -> (ucycle e p).
Proof. By Case/andP=> [Hp Up]; Rewrite: /ucycle Hp simple_uniq. Qed.

Coercion scycle_ucycle : scycle >-> ucycle.

Lemma simple_fproj : simple -> (x : g) (p x) -> (fproj x) = x.
Proof.
Rewrite: /simple /fproj; Move=> Up x Hx; Case/splitPr: Hx Up => [p1 p2].
Rewrite: maps_cat uniq_cat /=; Case/and3P; Clear; Case/norP=> [Up1 _] _.
Rewrite: find_cat; Case Hp1: (has (cface x) p1).
  Case/mapsP: Up1; Case/hasP: Hp1 => [y Hy Hxy]; Exists y; Auto.
  Symmetry; Exact (rootP (Sface g) Hxy).
By Rewrite: /= connect0 addn0 sub_cat /= ltnn subnn.
Qed.

Lemma scycle_fproj : scycle -> (x : g) (p x) -> (fproj x) = x.
Proof. Case/andP; Clear; Exact simple_fproj. Qed.

Lemma simple_cface : simple -> (x, y : g) (cface x y) -> (p x) -> (p y) -> x = y.
Proof.
Move=> Up x y Hxy Hx Hy.
By Rewrite: -(simple_fproj Up Hx) (fproj_cface Hxy) simple_fproj.
Qed.

Lemma scycle_cface : scycle -> (x, y : g) (cface x y) -> (p x) -> (p y) -> x = y.
Proof. Case/andP; Clear; Exact simple_cface. Qed.

Lemma simple_fcard_fband : simple -> (fcard face fband) = (size p).
Proof.
Move=> Up; Rewrite: -(size_maps (froot face) p) -(card_uniqP Up).
Apply: eq_card => [x]; Apply/andP/mapsP=> [[Dx Hpx] | [y Hy []]].
  Case/hasP: Hpx => [y Hy Hxy]; Exists y; LeftDone.
  By Rewrite: -(rootP (Sface?) Hxy) (eqP Dx).
Split; LeftBy Exact (roots_root (Sface g) y).
By Apply/hasP; Exists y; RightBy Rewrite: Sface connect_root.
Qed.

Lemma scycle_fcard_fband : scycle -> (fcard face fband) = (size p).
Proof. Case/andP; Clear; Exact simple_fcard_fband. Qed.

End SimplePaths.

Lemma fband_adds : (x : g; p : (seq g); y : g)
  (fband (Adds x p) y) = (orb (cface y x) (fband p y)).
Proof. Done. Qed.

Lemma fband_seqn : (x, y : g) (cface x y) ->
  (n : nat) (fband (seqn n x)) =1 (fband (seqn n y)).
Proof.
Move=> x y Hxy n z; Elim: n => //= [n []].
By Rewrite: !(Sface ? z) (same_cface Hxy).
Qed.

Fixpoint simple_rec [p : (seq g)] : bool :=
  if p is (Adds x p') then (andb (negb (fband p' x)) (simple_rec p')) else true.

Lemma simple_recI : simple =1 simple_rec.
Proof.
Rewrite: /simple; Elim=> // [x p Hrec]; Rewrite: /= ~Hrec; Congr andb.
Apply/mapsP/hasP=> [[y Hy Dy] | [y Hy Hxy]]; (Exists y; LeftDone).
  By Apply/(rootP (Sface g)).
Exact (esym (rootP (Sface g) Hxy)).
Qed.

Lemma simple_adds : (x : g; p : (seq g))
 (simple (Adds x p)) = (andb (negb (fband p x)) (simple p)).
Proof. By Move=> *; Rewrite: !simple_recI. Qed.

Lemma fband_cat : (p1, p2 : (seq g); x : g)
  (fband (cat p1 p2) x) = (orb (fband p1 x) (fband p2 x)).
Proof. Move=> *; Apply: has_cat. Qed.

Lemma fproj_adds : (x : g; p : (seq g); y : g)
  (fproj (Adds x p) y) = (if (cface x y) then x else (fproj p y)).
Proof. By Move=> x p y; Rewrite: /fproj /= Sface; Case (cface x y). Qed.

Lemma fproj_cat : (p1, p2 : (seq g); x : g)
  (fproj (cat p1 p2) x) = (fproj (if (fband p1 x) then p1 else p2) x).
Proof.
Move=> p1 p2 x; Elim: p1 => [|y p1 Hrec] //=; Rewrite: fproj_adds Hrec Sface.
Case Hxy: (cface x y) => /=; LeftBy Rewrite: fproj_adds Sface Hxy.
By Case (fband p1 x); LeftBy Rewrite: fproj_adds Sface Hxy.
Qed.

Lemma has_fband_sym : (p1, p2 : (seq g))
  (has (fband p1) p2) = (has (fband p2) p1).
Proof.
By Move=> p1 p2; Apply/hasP/hasP => [[x Hx]]; Move/hasP=> [y Hy Hxy];
   (Exists y; LeftDone); Apply/hasP; (Exists x; LeftDone); Rewrite Sface.
Qed.

Lemma simple_cat : (p1, p2 : (seq g))
  (simple (cat p1 p2)) =
     (and3b (simple p1) (negb (has (fband p1) p2)) (simple p2)).
Proof.
Move=> p1 p2; Rewrite: !simple_recI has_fband_sym.
Elim: p1 => [|x p1 Hrec] //=.
By Rewrite: fband_cat Hrec !negb_orb -!andbA; Repeat BoolCongr.
Qed.

Lemma simple_add_last : (x : g; p : (seq g))
 (simple (add_last p x)) = (andb (negb (fband p x)) (simple p)).
Proof.
By Move=> *; Rewrite: -cats1 simple_cat {2}/simple /= orbF andbT andbC.
Qed.

Lemma simple_catC : (p1, p2 : (seq g)) (simple (cat p1 p2)) = (simple (cat p2 p1)).
Proof. By Move=> *; Rewrite: /simple !maps_cat uniq_catC. Qed.

Lemma simple_catCA : (p1, p2, p3 : (seq g))
  (simple (cat p1 (cat p2 p3))) = (simple (cat p2 (cat p1 p3))).
Proof. By Move=> *; Rewrite: /simple !maps_cat uniq_catCA. Qed.

Lemma fband_rot : (p : (seq g)) (fband (rot n0 p)) =1 (fband p).
Proof. Move=> p x; Apply: has_rot. Qed.

Lemma fproj_rot : (p : (seq g)) (simple p) -> (fproj (rot n0 p)) =1 (fproj p).
Proof.
Move=> p Up x; Case Hx: (fband (rot n0 p) x).
  Case/fprojP: Hx; Rewrite mem_rot; Move: (fproj (rot n0 p) x) => y Hy Hxy.
  By Rewrite: (fproj_cface p Hxy) simple_fproj.
Move: {}Hx; Rewrite fband_rot in Hx; Move: Hx; Rewrite: /fband !has_find !ltnNge.
By Move/idP=> Hx; Move/idP=> Hx'; Rewrite: /fproj !sub_default.
Qed.

Lemma simple_rot : (p : (seq g)) (simple (rot n0 p)) = (simple p).
Proof. By Move=> *; Rewrite: /simple maps_rot uniq_rot. Qed.

Lemma scycle_rot : (e : (rel g); p : (seq g))
  (scycle e (rot n0 p)) == (scycle e p).
Proof. By Move=> *; Rewrite: /scycle cycle_rot simple_rot. Qed.

Lemma simple_perm : (p, q : (seq g)) (fband p) =1 (fband q) ->
  (size p) = (size q) -> (simple p) = (simple q).
Proof.
Move=> p q Epq Hpq; Apply: uniq_perm; RightBy Rewrite: !size_maps.
Move=> x; Apply/mapsP/mapsP=> [[y Hy []]] {x}.
  Step Hz: (fband q y) By Rewrite: -Epq; Apply: (subsetP (ring_fband ?)).
  By Case/hasP: Hz => [z Hz Hyz]; Exists z; RightBy Rewrite: (rootP (Sface g) Hyz).
Step Hz: (fband p y) By Rewrite: Epq; Apply: (subsetP (ring_fband ?)).
By Case/hasP: Hz => [z Hz Hyz]; Exists z; RightBy Rewrite: (rootP (Sface g) Hyz).
Qed.

Lemma simple_rev : (p : (seq g)) (simple (rev p)) = (simple p).
Proof. By Move=> *; Rewrite: /simple maps_rev uniq_rev. Qed.

Lemma fband_rev : (p : (seq g)) (fband (rev p)) =1 (fband p).
Proof. Move=> p x; Apply: eq_has_r => [y] {x}; Apply: mem_rev. Qed.

End FacePaths.

Lemma simple_maps : (g, g' : hypermap; h : g -> g')
  ((x, y : g) (cface (h x) (h y)) = (cface x y)) -> 
    (p : (seq g)) (simple (maps h p)) = (simple p).
Proof.
Move=> g g' h HhF; Elim=> [|x p Hrec] //.
Rewrite: maps_adds !simple_adds Hrec; Congr andb; Congr negb.
By Elim: p {Hrec} => [|y p Hrec] //=; Rewrite: HhF Hrec.
Qed.

Syntax constr level 0 :
  fun_scycle1_pp [(scycle (eqdf $f) $p)] ->
  [ "(sfcycle " [<hov 0> $f:E [1 1] $p:E ")" ]]
| fun_scycle0_pp [(scycle (eqdf $f))] -> [ "(sfcycle " $f:E ")" ].

Grammar constr constr0 : constr :=
  fun_scycle1 ["(" "sfcycle" constr9($f) constr9($p) ")"] ->
  [(scycle (eqdf $f) $p)]
| fun_scycle0 ["(" "sfcycle" constr9($f) ")"] ->
  [(scycle (eqdf $f))].

(* Special geometries: plain maps (binary edges), cubic maps (ternary nodes) *)
(* precubic maps (at most ternary nodes), pentagonal maps (faces 5-ary, at   *)
(* least). The reduction to plain cubic maps will be established in cube.v.  *)
(* All these predicates take a set argument, as we also consider quasi-plain *)
(* /quasi-cubic maps, that are only plain/cubic on a subset of the darts.    *)

Section SpecialMaps.

Variable g : hypermap.

Definition plainb [a : (set g)] : bool := (subset a (order_set edge (2))).
Definition plain : Prop := (plainb g).

Lemma plainPx : (a : (set g))
  (reflect (x : g) (a x) -> (edge (edge x)) = x /\ ((edge x) =d x) = false
           (plainb a)).
Proof.
Move=> a; Apply: (iffP subsetP) => [Ha x Hx].
  Split; LeftBy Rewrite: -{2 x}(iter_order (Iedge g)) (eqnP (Ha x Hx)).
  Apply/idPn; Move: (uniq_orbit edge x).
  By Rewrite: /orbit (eqnP (Ha x Hx)) /= andbT /setU1 orbF.
Move: {Ha Hx}(Ha x Hx) => [De2x He1x].
Apply/eqP; Apply: (order_cycle 3!(seq2 x (edge x)) ? ? ?); Try Apply: setU11.
  By Rewrite: /= /eqdf De2x ?set11.
By Rewrite: /= /setU1 He1x.
Qed.

Lemma plain_eq : plain -> (x : g) (edge (edge x)) = x.
Proof. By Move/(plainPx ?) => HgE x; Case (HgE x). Qed.

Lemma plain_eq' : plain -> (x : g) (node (face x)) = (edge x).
Proof. By Move=> HgE x; Rewrite: -{2 x}Eface plain_eq. Qed.

Lemma plain_neq : plain -> (x : g) ((edge x) =d x) = false.
Proof. By Move/(plainPx ?) => HgE x; Case (HgE x). Qed.

Lemma plain_orbit : plain -> (x : g) (cedge x) =1 (seq2 x (edge x)).
Proof.
Move=> HgE x; Move: (fconnect_orbit edge x).
By Rewrite: /orbit (eqnP (subsetA HgE x)).
Qed.

Definition cubicb [a : (set g)] : bool := (subset a (order_set node (3))).
Definition cubic : Prop := (cubicb g).
Definition precubic : Prop := (subset g [x](leq (order node x) (3))).

Lemma cubicPx : (a : (set g))
  (reflect (x : g) (a x) -> (node (node (node x))) = x /\ ((node x) =d x) = false
           (cubicb a)).
Proof.
Move=> a; Apply: (iffP subsetP) => [Ha x Hx].
  Split; LeftBy Rewrite: -{2 x}(iter_order (Inode g)) (eqnP (Ha x Hx)).
  Apply/idPn; Move: (uniq_orbit node x).
  By Rewrite: /orbit (eqnP (Ha x Hx)); Case/andP; Case/norP.
Move: {Ha Hx}(Ha x Hx) => [Dn3x Hn1x].
Apply/eqP; Apply: (order_cycle 3!(traject node x (3)) ? ? ?); Try Apply: setU11.
  By Rewrite: /= /eqdf Dn3x ?set11.
By Rewrite: /= /setU1 -{4 x}Dn3x !(inj_eqd (Inode g)) (eqd_sym x) Hn1x.
Qed.

Lemma cubic_eq : cubic -> (x : g) (node (node (node x))) = x.
Proof. By Move/(cubicPx ?) => HgN x; Case (HgN x). Qed.

Lemma cubic_eq' : cubic -> (x : g) (node (node x)) = (face (edge x)).
Proof. By Move=> HgN x; Rewrite: -{1 x}Eedge cubic_eq. Qed.

Lemma cubic_neq : cubic -> (x : g) ((node x) =d x) = false.
Proof. By Move/(cubicPx ?) => HgN x; Case (HgN x). Qed.

Lemma cubic_orbit : cubic ->
  (x : g) (cnode x) =1 (seq3 x (node x) (node (node x))).
Proof.
Move=> HgN x; Move: (fconnect_orbit node x).
By Rewrite: /orbit (eqnP (subsetA HgN x)).
Qed.

Lemma precubic_leq : precubic -> (x : g) (leq (order node x) (3)).
Proof. By Move/subsetA. Qed.

Lemma cubic_precubic : cubic -> precubic.
Proof. By Move/subsetA=> HgN; Apply/subsetP=> [x _]; Rewrite: (eqnP (HgN x)). Qed.

Definition pentagonal : Prop := (x : g) (ltn (4) (arity x)).

(* Requirement for the four color theorem. *)
Record planar_bridgeless : Prop :=
  PlanarBridgeless {
    planar_bridgeless_is_planar     :> (planar g);
    planar_bridgeless_is_bridgeless :> (bridgeless g)
  }.

(* Required by quiz, quiztree, part. *)
Record plain_cubic : Prop :=
  PlainCubic {
    plain_cubic_connected_is_plain :> plain;
    plain_cubic_connected_is_cubic :> cubic
  }.

(* Required for special Euler formula. *)
Record plain_cubic_connected : Prop :=
  PlainCubicConnected {
    plain_cubic_connected_base         :> plain_cubic;
    plain_cubic_connected_is_connected :> (connected g)
  }.

(* Required by discharge. *)
Record planar_plain_cubic_connected : Prop :=
  PlanarPlainCubicConnected {
    planar_plain_cubic_connected_base      :> plain_cubic_connected;
    planar_plain_cubic_connected_is_planar :> (planar g)
  }.

(* Required by part, redpart, hubcap. *)
Record plain_cubic_pentagonal : Prop :=
  PlainCubicPentagonal {
    plain_cubic_pentagonal_base          :> plain_cubic;
    plain_cubic_pentagonal_is_pentagonal :> pentagonal
  }.

(* Factored intermediate signature. *)
Record planar_bridgeless_plain : Prop :=
  PlanarBridgelessPlain {
    planar_bridgeless_plain_base     :> planar_bridgeless;
    planar_bridgeless_plain_is_plain :> plain
  }.

(* Required by revsnip. *)
Record planar_bridgeless_plain_connected : Prop :=
  PlanarBridgelessPlainConnected {
    planar_bridgeless_plain_connected_base         :> planar_bridgeless_plain;
    planar_bridgeless_plain_connected_is_connected :> (connected g)
  }.

(* Inductive assumption. *)
Record planar_bridgeless_plain_precubic : Prop :=
  PlanarBridgelessPlainPrecubic {
    planar_bridgeless_plain_precubic_base        :> planar_bridgeless_plain;
    planar_bridgeless_plain_precubic_is_precubic :> precubic
  }.

Section QuasicubicMaps.

Variable r : (seq g).

Definition quasicubic : Prop := (cubicb (setC r)).

Lemma quasicubic_eq : quasicubic ->
  (x : g) (setC r x) -> (node (node (node x))) = x.
Proof. By Move/(cubicPx ?)=> H x Hx; Case (H x Hx). Qed.

(* Required by quiz. *)
Record plain_quasicubic : Prop :=
  PlainQuasicubic {
    plain_quasicubic_is_plain :> plain;
    plain_quasicubic_is_quasicubic :> quasicubic
  }.

(* Intermediate common base *)
Record ucycle_plain_quasicubic : Prop :=
  UcyclePlainQuasicubic {
    ucycle_plain_quasicubic_base      :> plain_quasicubic;
    ucycle_plain_quasicubic_is_ucycle :> (ufcycle node r)
  }.

(* Required by kempe. *)
Record ucycle_planar_plain_quasicubic : Prop :=
  UcyclePlanarQuasicubicConnected {
    ucycle_planar_plain_quasicubic_base      :> ucycle_plain_quasicubic;
    ucycle_planar_plain_quasicubic_is_planar :> (planar g)
  }.

(* Required by for special Euler formula *)
Record ucycle_plain_quasicubic_connected : Prop :=
  UcyclePlainQuasicubicConnected {
    ucycle_plain_quasicubic_connected_base         :> ucycle_plain_quasicubic;
    ucycle_plain_quasicubic_connected_is_connected :> (connected g)
  }.

(* Required by embed and redpart. Two additional geometrical conditions *)
(* are also needed; these will be defined below, but will only be added *)
(* in reducible.v, along with reducibility.                             *)
Record scycle_planar_bridgeless_plain_quasicubic_connected : Prop :=
  ScyclePlanarBridgelessPlainQuasicubicConnected {
    scycle_planar_bridgeless_plain_quasicubic_connected_base
      :> ucycle_plain_quasicubic_connected;
    scycle_planar_bridgeless_plain_quasicubic_connected_is_simple
      : (simple r);
    scycle_planar_bridgeless_plain_quasicubic_connected_is_planar
      :> (planar g);
    scycle_planar_bridgeless_plain_quasicubic_connected_is_bridgeless
      :> (bridgeless g)
  }.

Lemma scycle_planar_bridgeless_plain_quasicubic_connected_is_scycle :
  scycle_planar_bridgeless_plain_quasicubic_connected -> (sfcycle node r).
Proof. By Do 3 Case; Clear; Case/andP=> *; Apply/andP; Split. Qed.

Coercion scycle_planar_bridgeless_plain_quasicubic_connected_is_scycle
       : scycle_planar_bridgeless_plain_quasicubic_connected >-> scycle.

Definition scycle_planar_bridgeless_plain_quasicubic_connected_pbpc_base :
  scycle_planar_bridgeless_plain_quasicubic_connected ->
     planar_bridgeless_plain_connected.
By Do 4 Case; Repeat Split. Defined.

Coercion scycle_planar_bridgeless_plain_quasicubic_connected_pbpc_base :
  scycle_planar_bridgeless_plain_quasicubic_connected >->
     planar_bridgeless_plain_connected.

(* The special form of the Euler formula for plain quasicubic connected maps. *)

Lemma quasicubic_Euler : ucycle_plain_quasicubic_connected ->
  let exterior = (negb r =d seq0) in
  let nb_face = (addn exterior (fcard face g)) in
  let ring_darts = (double (size r)) in
  (planar g) == ((mult (6) nb_face) =d (addn (card g) (addn ring_darts (12)))).
Proof.
Do 2 Case; Move=> [HgE HgN]; Move/andP=> [Hr Ur] Hcg exterior; PropCongr.
Transitivity (mult (6) (genus_lhs g)) =d (mult (6) (genus_rhs g)).
  Rewrite: /planar even_genusP; Move: (genus g) (genus_rhs g) => m m'.
  By Rewrite: /= addnI -!addnA; Repeat Rewrite: -?(addnCA m') !eqn_addl; Case m.
Pose ne := (fcard edge g); Pose nf := (fcard face g); Pose sr := (size r).
Step Hne: (card g) = (mult (2) ne).
  By Apply: eqP; Rewrite: (order_div_card (Iedge g) HgE) // set11.
Step [nn Dnn Hnn]: (EX nn | (fcard node g) = (addn exterior nn)
                          & (card g) = (addn sr (mult (3) nn))).
  Exists (fcard node (setC r)).
    Rewrite: (n_compC r) /exterior /sr; Congr addn; Case Dr: {2}r => [|x r'].
      By Apply: eqP; Apply/set0P => [x]; Rewrite: Dr /= /setI /= andbF.
    Apply: etrans (n_comp_connect (Snode g) x); Symmetry; Apply: eq_n_comp_r.
    By Apply: fconnect_cycle; Rewrite: // Dr /= setU11.
  Step Ha: (fclosed node (setC r)).
    Apply: setC_closed; Apply: (intro_closed (Snode g)) => [x y Dy Hx].
    By Rewrite: -(fconnect_cycle Hr Hx) -(eqP Dy) fconnect1.
  Rewrite: -(card_uniqP Ur) -(cardC r); Congr addn; Apply: eqP.
  By Rewrite: (order_div_card (Inode g) HgN) // set11.
Rewrite: /genus_lhs (eqnP Hcg) /= addnI -!addnS !addn0.
Rewrite: {1 2 (card g)}Hnn Hne !addnA /genus_rhs Dnn -/ne -/nf.
Rewrite: -(addnC sr) (addnA sr) -double_addnn /= addnI !addn0 -!addnA.
Rewrite: !(addnCA (double sr)) eqd_sym; Repeat Rewrite: -?(addnCA nn) eqn_addl.
By Repeat Rewrite: -?(addnCA ne) eqn_addl.
Qed.

End QuasicubicMaps.

(* The special form of the Euler formula for plain cubic connected maps. *)

Lemma cubic_Euler : plain_cubic_connected ->
  (planar g) == ((mult (6) (fcard face g)) =d (addn (card g) (12))).
Proof.
By Case; Case=> *; Rewrite: (!quasicubic_Euler seq0); Repeat Split.
Qed.

End SpecialMaps.

Syntactic Definition plainP := plainPx | 1.
Syntactic Definition cubicP := cubicPx | 1.

Section MirrorSpecials.

Variable g : hypermap.

Lemma plain_dual : (plain (dual g)) == (plain g).
Proof.
PropCongr; Apply: eq_subset_r => [x].
By Rewrite: /order_set /= (order_finv (Iedge g)).
Qed.

Lemma plain_mirror : (plain (mirror g)) == (plain g).
Proof.
PropCongr; Apply/subsetP/subsetP=> [] HgE x _.
  By Rewrite: /order_set -{x}Eedge -order_mirror_edge; Apply: HgE.
By Rewrite: /order_set order_mirror_edge; Apply: HgE.
Qed.

Lemma cubic_mirror : (cubic (mirror g)) == (cubic g).
Proof.
PropCongr; Apply: eq_subset_r => [x].
By Rewrite: /order_set /= (order_finv (Inode g)).
Qed.

Lemma precubic_mirror : (precubic (mirror g)) == (precubic g).
Proof.
PropCongr; Apply: eq_subset_r => [x].
By Rewrite: /order_set /= (order_finv (Inode g)).
Qed.

End MirrorSpecials.

Section Adj.

Variables n0 : nat; g : hypermap.

Definition rlink : (rel g) := [x](cface (edge x)).

Lemma rlinkE : (x : g) (rlink x (edge x)).
Proof. Move=> x; Apply: connect0. Qed.

Lemma rlinkFr : (y1, y2 : g) (cface y1 y2) ->
  (x : g) (rlink x y1) = (rlink x y2).
Proof.
By Move=> y1 y2 Hy12 x; Rewrite: /rlink !(!Sface g (edge x)) (same_cface Hy12).
Qed.

Fixpoint srpath [x0, x : g; p : (seq g)] : bool :=
  if p is (Adds y p') then
    (and3b (cface (edge x) y) (all [z](negb (cface x z)) p') (srpath x0 y p'))
  else (cface (edge x) x0).

Definition srcycle [r : (seq g)] : bool :=
  if r is (Adds x p) then (srpath x x p) else true.

Lemma srcycleI : (bridgeless g) -> (r : (seq g)) (scycle rlink r) == (srcycle r).
Proof.
Move=> Hbg [|x0 p] //; Rewrite: /scycle simple_recI /=; PropCongr.
Elim: p {1 3 5}x0 => [|y p Hrec] x /=; LeftBy Rewrite: !andbT.
Rewrite: -~Hrec -!andbA -/(rlink x y); Case Hxy: (rlink x y) => //=.
BoolCongr; Congr andb; Rewrite: Sface -(same_cface Hxy) Sface (set0P Hbg) /=.
By Rewrite: /fband -all_setC.
Qed.

Definition rlink_connected [a : (set g)] : Prop :=
  (x, y : g) (a x) -> (a y) ->
    (EX p | (path rlink (node (face x)) (add_last p y)) & (all a p)).

Lemma simplify_rlink : (x : g; p : (seq g)) (path rlink x p) ->
  (EX p' | (path rlink x p') /\ (simple p')
         & (and3 (last x p) = (last x p') (p =d seq0) = (p' =d seq0) (all p p'))).
Proof.
Move=> x p; Elim: {p}(S (size p)) x {-2}p (ltnSn (size p)) => // [n Hrec] x.
Case=> [|y p] Hn Hp; LeftBy Exists (Seq0 g); Split; Rewrite: // connect0.
Rewrite: /= ltnS in Hn Hp; Case/andP: Hp => [Hxy Hp].
Case Hpy: (fband p y).
  Case/fprojP: Hpy; Move: (fproj p y) {Ep} => z Hpz Hyz.
  Case/splitPr: Hpz Hp Hn => [p1 p2]; Rewrite: -cat_adds path_cat size_cat.
  Move/andP=> [_ Hp2] Hn; Case: {Hrec}(Hrec x (Adds z p2)) => //.
    By Apply: leq_trans Hn; Rewrite: /= !ltnS leq_addl.
    By Rewrite: /= -(rlinkFr Hyz) Hxy; Case/andP: Hp2.
  Rewrite last_cat; Move=> p' [Hp' Up'] [Ep' Ep'0 Hp2p']; Exists p'; Split; Auto.
  By Apply/allP=> [t Ht]; Rewrite: mem_cat /setU orbC (allP Hp2p').
Case: {Hrec Hn Hp}(Hrec y p Hn Hp) => [p' [Hp' Up'] [Ep' _ Hpp']].
Exists (Adds y p'); Split; Auto; Try By Rewrite: /= Hxy.
  Rewrite: simple_adds Up' andbT; Apply/hasP=> [[z Hz Hyz]]; Case/hasP: Hpy.
  By Exists z; LeftBy Apply (allP Hpp').
By Apply/allP=> [z]; Rewrite: /= /setU1; Case (y =d z); RightBy Apply: (allP Hpp').
Qed.

Definition adj : (rel g) := [x, y](has [x'](rlink x' y) (orbit face x)).

Lemma adjPx : (x, y : g) (reflect (EX z | (cface x z) & (rlink z y)) (adj x y)).
Proof.
By Move=> x y; Apply: (iffP hasP) => [[z Hxz Hyz]]; Exists z; Auto;
  Move: Hxz; Rewrite: fconnect_orbit.
Qed.

Syntactic Definition adjP := adjPx | 2.

Lemma rlink_adj : (x, y : g) (rlink x y) -> (adj x y).
Proof. By Move=> x *; Apply/adjP; Exists x; LeftBy Apply connect0. Qed.

Lemma adjE : (x : g) (adj x (edge x)).
Proof. Move=> x; Apply rlink_adj; Apply rlinkE. Qed.

Lemma adjF : (x1, x2 : g) (cface x1 x2) -> (adj x1) =1 (adj x2).
Proof.
Move=> x1 x2 Hx12 y; Apply: eq_has_r {y} => [y].
By Rewrite: -!fconnect_orbit (same_cface Hx12).
Qed.

Lemma adjFr : (y1, y2 : g) (cface y1 y2) ->
  (x : g) (adj x y1) = (adj x y2).
Proof.
Move=> y1 y2 Hy12 x; Apply: eq_has {x} => [x].
By Rewrite: /rlink !(!Sface g (edge x)) (same_cface Hy12).
Qed.

Lemma adjF1 : (x : g) (adj x) =1 (adj (face x)).
Proof. Move=> x y; Apply adjF; Apply fconnect1. Qed.

Lemma adjF1r : (x, y : g) (adj x y) = (adj x (face y)).
Proof. Move=> x y; Apply adjFr; Apply fconnect1. Qed.

Lemma adjN : (x : g) (adj (node x) x).
Proof. By Move=> x; Rewrite: -{2 x}Enode -adjF1r adjE. Qed.

Lemma Sadj : (plain g) -> (x, y : g) (adj x y) = (adj y x).
Proof.
Move=> HgE x y; Apply/adjP/adjP=> [[z Hxz Hzy] | [z Hyz Hzx]];
  By Exists (edge z); Rewrite: /rlink Sface ?plain_eq.
Qed.

Lemma no_adj_adj : (x, y1 : g) (negb (adj x y1)) ->
  (y2 : g) (adj x y2) -> (cface y1 y2) = false.
Proof.
Move=> x y1 Hxy1 y2 Hxy2; Apply/idP=> [Hy12]; Case/idP: Hxy1.
By Rewrite (adjFr Hy12).
Qed.

Lemma adj_no_cface : (bridgeless g) ->
  (x, y : g) (adj x y) -> (cface x y) = false.
Proof.
Move=> Hbg x y; Move/adjP=> [z Hxz Hzy].
By Rewrite: (same_cface Hxz) Sface -(same_cface Hzy) Sface (set0P Hbg).
Qed.

Definition chordless [r : (seq g)] : bool :=
  (subset r [x](disjoint (adj x) (setD1 (setD1 r (prev r x)) (next r x)))).

Lemma chordless_rot : (r : (seq g)) (uniq r) ->
  (chordless (rot n0 r)) = (chordless r).
Proof.
Move=> r Ur; Rewrite: /chordless (eq_subset (mem_rot n0 r)).
Apply: eq_subset_r => [x]; Rewrite: (next_rot n0 Ur) (prev_rot n0 Ur).
Rewrite: !(disjoint_sym (adj x)); Apply: eq_disjoint => [y].
By Rewrite: /setD1 mem_rot.
Qed.

(* Edge closure of a sequence, in a plain graph; used mainly for contracts.  *)

Fixpoint insertE [p : (seq g)] : (seq g) :=
  if p is (Adds x p') then (Adds x (Adds (edge x) (insertE p'))) else seq0.

Lemma insertE_seqb : (b : bool; x : g)
  (insertE (seqn b x)) = (cat (seqn b x) (seqn b (edge x))).
Proof. By Case. Qed.

Lemma size_insertE : (p : (seq g)) (size (insertE p)) = (double (size p)).
Proof. By Elim=> //= [x p1 Hrec]; Do 2 Congr S. Qed.

Lemma insertE_cat : (p1, p2 : (seq g))
  (insertE (cat p1 p2)) = (cat (insertE p1) (insertE p2)).
Proof. By Move=> p1 p2; Elim: p1 => //= [x p1 Hrec]; Do 2 Congr Adds. Qed.

Lemma mem_insertE : (plain g) ->
  (p : (seq g); x : g) (insertE p x) = (has (cedge x) p).
Proof.
Move=> HgE p x; Elim: p => //= [y p []].
By Rewrite: Sedge (plain_orbit HgE) /= /setU1 -!orbA.
Qed.

Lemma insertE_rot : (p : (seq g))
  (insertE (rot n0 p)) = (rot (double n0) (insertE p)).
Proof.
Move=> p; Case: (ltnP n0 (size p)) => [Hn0].
  Rewrite: -{2 p}(cat_take_drop n0) {1}/rot !insertE_cat -rot_size_cat.
  By Rewrite: size_insertE (size_takel (ltnW Hn0)).
By Rewrite: !rot_oversize // size_insertE leq_double.
Qed.

End Adj.

Syntactic Definition adjP := adjPx | 2.

Syntax constr level 0 :
  map_rlink_pp [(rlink 1!$_)] -> ["rlink"]
| map_adj_pp [(adj 1!$_)] -> ["adj"].

Grammar constr constr0 : constr :=
  map_rlink ["rlink"] -> [(!rlink ?)]
| map_adj ["adj"] -> [(!adj ?)].

Unset Implicit Arguments.
