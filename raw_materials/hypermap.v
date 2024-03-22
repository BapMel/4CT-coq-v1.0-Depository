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

Set Implicit Arguments.

(* A (finite) hypermap is just a triplet of functions over a finite set that *)
(* are mutually inverse -their composite is the identity. This is equivalent *)
(* to an arbitrary pair of permutations, but the three function presentation *)
(* has better symmetries. In particular, the generalizations of the Euler    *)
(* and genus formulae to hypermaps are completely symmetric. The Jordan      *)
(* characterization of planarity also has a nice hypermap formulation, but   *)
(* it is not as symmetrical (it requires singling out two of the three       *)
(* functions). Indeed, while it is relatively straightforward to show that   *)
(* swapping the two functions yields an equivalent definition (see below),   *)
(* is not at all obvious that substituting the third function also gives an  *)
(* equivalent definition; we will in fact only obtain this as a corollary of *)
(* the equivalence of the Jordan property with the Euler, in file jordan.v.  *)
(*    Although we conspicuously call the three functions edge, node, and     *)
(* face, we only give symmetrical definitions in this file. In particular,   *)
(* all the derived map constructions given here are symmetrical, and apply   *)
(* to arbitrary maps. The individual geometrical interpretation of these     *)
(* functions will only be introduced in file colormap.v.                     *)
(*    The precise triangular identity forces us to make several subtle       *)
(* choices in some of our definitions, that are easily overlooked in the     *)
(* more traditional relational/simplicial fomalization of geometry (e.g.,    *)
(* the inverion of funtions in the defition of the Jordan property and the   *)
(* dual graph. This extra attention to detail pays off handsomely in the     *)
(* rest of the devellopment, where we can establish many geometrical         *)
(* using only rewriting with the basic triangular identity and its           *)
(* permutations.                                                             *)
(*   Properties on maps, such as connectedness and planarity defined here,   *)
(* are usually defined as boolean predicates, so that we can state           *)
(* equivalence lemmas (e.g., the map obtained by sewing up two submaps along *)
(* their outer rings is planar iff the two submaps are). However we also     *)
(* need to define explicit shorthand for the equivalent Prop statement,      *)
(* because the coercion of a bool to Prop is not a good coercion target      *)
(* (all such assumptions are in the class is_true!).                         *)

Grammar constr constr0 : constr :=
   monic3_fun ["(" "monic3" constr9($f) constr9($g) constr9($h) ")" ] ->
     [(monic $f [x]($g ($h x)))]
|  explicit_monic3_fun ["(" "!" "monic3" constr9($d)
                             constr9($f) constr9($g) constr9($h) ")" ] ->
     [(!monic $d $d $f [x]($g ($h x)))].

Record hypermap : Type := Hypermap {
  dart :> finSet;
  edge : dart -> dart;
  node : dart -> dart;
  face : dart -> dart;
  Eedge : (monic3 edge node face)
}.

Implicits Eedge [].

(* Pretty-print must precede grammar. *)

Syntax constr level 0:
  map_edge_pp [(edge 1!$_)] -> [ "edge" ]
| map_node_pp [(node 1!$_)] -> [ "node" ]
| map_face_pp [(face 1!$_)] -> [ "face" ].

Grammar constr constr0 : constr :=
  map_edge ["edge"] -> [(!edge ?)]
| map_node ["node"] -> [(!node ?)]
| map_face ["face"] -> [(!face ?)].

Syntactic Definition cedge := (fconnect edge).
Syntactic Definition cnode := (fconnect node).
Syntactic Definition cface := (fconnect face).

Section FiniteMap.

Variable g : hypermap.

Lemma Eface : (!monic3 g face edge node).
Proof. Exact (monicF_sym (Eedge g)). Qed.

Lemma Enode : (!monic3 g node face edge).
Proof. Exact (monicF_sym Eface). Qed.

Lemma Iedge : (!injective g g edge). Proof. Exact (monic_inj (Eedge g)). Qed.
Lemma Inode : (!injective g g node). Proof. Exact (monic_inj Enode). Qed.
Lemma Iface : (!injective g g face). Proof. Exact (monic_inj Eface). Qed.

Lemma Sedge : (x, y : g) (cedge x y) = (cedge y x).
Proof. Exact (fconnect_sym Iedge). Qed.
Lemma Snode : (x, y : g) (cnode x y) = (cnode y x).
Proof. Exact (fconnect_sym Inode). Qed.
Lemma Sface : (x, y : g) (cface x y) = (cface y x).
Proof. Exact (fconnect_sym Iface). Qed.

Lemma same_cedge : (x, y : g) (cedge x y) -> (cedge x) =1 (cedge y).
Proof. Exact (same_connect Sedge). Qed.
Lemma same_cnode : (x, y : g) (cnode x y) -> (cnode x) =1 (cnode y).
Proof. Exact (same_connect Snode). Qed.
Lemma same_cface : (x, y : g) (cface x y) -> (cface x) =1 (cface y).
Proof. Exact (same_connect Sface). Qed.

Lemma cedge1 : (x : g) (cedge x) =1 (cedge (edge x)).
Proof. Exact (same_fconnect1 Iedge). Qed.
Lemma cedge1r : (y, x : g) (cedge x y) = (cedge x (edge y)).
Proof. Exact [y,x](same_fconnect1_r Iedge x y). Qed.

Lemma cnode1 : (x : g) (cnode x) =1 (cnode (node x)).
Proof. Exact (same_fconnect1 Inode). Qed.
Lemma cnode1r : (y, x : g) (cnode x y) = (cnode x (node y)).
Proof. Exact [y,x](same_fconnect1_r Inode x y). Qed.

Lemma cface1 : (x : g) (cface x) =1 (cface (face x)).
Proof. Exact (same_fconnect1 Iface). Qed.
Lemma cface1r : (y, x : g) (cface x y) = (cface x (face y)).
Proof. Exact [y,x](same_fconnect1_r Iface x y). Qed.

End FiniteMap.

Implicits Enode [].
Implicits Eface [].
Implicits Iedge [2 3].
Implicits Inode [2 3].
Implicits Iface [2 3].
Implicits Sedge [].
Implicits Snode [].
Implicits Sface [].

Section Components.

Variable g : hypermap.

Definition glink : (rel g) := (relU (eqdf edge) (relU (eqdf node) (eqdf face))).

Lemma glinkE : (x : g) (glink x (edge x)).
Proof. By Move=> *; Rewrite: /glink /relU /setU /eqdf set11. Qed.

Lemma glinkN : (x : g) (glink x (node x)).
Proof. By Move=> *; Rewrite: /glink /relU /setU /eqdf set11 !orbT. Qed.

Lemma glinkF : (x : g) (glink x (face x)).
Proof. By Move=> *; Rewrite: /glink /relU /setU /eqdf set11 !orbT. Qed.

Lemma Sglink : (connect_sym glink).
Proof.
Apply: relU_sym; LeftBy Exact (Sedge ?).
Apply: relU_sym; [Exact (Snode ?) | Exact (Sface ?)].
Qed.

Definition connectedb : bool := (n_comp glink g) =d (1).
Definition connected : Prop := (n_comp glink g) =d (1).

End Components.

Implicits Sglink [].

Syntax constr level 0: map_glink_pp [(glink 1!$_)] -> [ "glink" ].
Grammar constr constr0 : constr := map_glink ["glink"] -> [(!glink ?)].

Syntactic Definition gcomp := (connect glink).

Section Genus.

Variable g : hypermap.

Definition genus_lhs : nat :=
  (addn (double (n_comp glink g)) (card g)).

Definition genus_rhs : nat :=
  (addn (fcard edge g) (addn (fcard node g) (fcard face g))).

Definition genus : nat := (half (subn genus_lhs genus_rhs)).

Definition even_genus : Prop := genus_lhs = (addn (double genus) genus_rhs).

Definition planarb : bool := genus =d (0).
Definition planar : Prop := genus =d (0).

End Genus.

Section Jordan.

Variable g : hypermap.

Definition clink : (rel g) := (relU (eqdf (finv node)) (eqdf face)).

Lemma clinkPx : (x, y : g) (reflect x = (node y) \/ (face x) = y (clink x y)).
Proof.
Move=> x y; Apply: (iffP orP); Rewrite: /eqdf.
  Case; Case/eqP; Rewrite: ?(f_finv (Inode g)); Auto.
Case=> [H | H]; Rewrite: H ?(finv_f (Inode g)) eqd_refl; Auto.
Qed.

Syntactic Definition clinkP := clinkPx | 2.

Lemma clinkN : (x : g) (clink (node x) x).
Proof. Move=> x; Apply/clinkP; Auto. Qed.

Lemma clinkF : (x : g) (clink x (face x)).
Proof. Move=> x; Apply/clinkP; Auto. Qed.

Lemma Sclink : (connect_sym clink).
Proof.
Apply: relU_sym; [Exact (fconnect_sym (finv_inj (Inode ?))) | Exact (Sface ?)].
Qed.

Lemma clink_glink : (connect clink) =2 gcomp.
Proof.
Move=> x; Apply: subset_eqP; Apply/andP.
Split; Apply/subsetP; Move: x; Apply: connect_sub => [x y Hy].
  Case/clinkP: Hy => [Hy | Hy].
    Rewrite: Sglink Hy; Exact (connect1 (glinkN ?)).
  Rewrite: -Hy; Exact (connect1 (glinkF ?)).
Case/setU1P: Hy => [Dy | Hy].
  Rewrite: -{x}Eedge Dy; Apply: (connect_trans (connect1 (clinkN ?))).
  Rewrite Sclink; Exact (connect1 (clinkF ?)).
Case/orP: Hy; Case/eqP.
  Rewrite: Sclink; Exact (connect1 (clinkN ?)).
Exact (connect1 (clinkF ?)).
Qed.

Lemma connected_clink : (connected g) ->
  (x, y : g) (EX p | (path clink x p) & (last x p) = y).
Proof.
Move=> Hcg x y; Apply: connectP; Rewrite: clink_glink.
Apply/(rootP (Sglink ?)); Pose rx := (root glink x); Pose ry := (root glink y).
Rewrite: /connected /n_comp (cardD1 rx) (cardD1 ry) in Hcg.
Rewrite: /setI /setD1 {1}/rx {2}/ry !(roots_root (Sglink g)) /setA /= andbT in Hcg.
By Case: (rx =P ry) Hcg.
Qed.

Definition moebius [p : (seq g)] : bool :=
  if p is (Adds x p') then (and3b
    (mem2 p' (finv node (last x p')) (node x)) 
    (uniq p)
    (path clink x p')
  ) else false.

Definition jordan : Prop := (p : (seq g)) (moebius p) = false.

Lemma jordan_face : jordan ->
  (x : g; p : (seq g)) (and3b
    (mem2 p (face (last x p)) (finv face x))
    (uniq (Adds x p))
    (path clink x p)
  ) = false.
Proof.
Move=> Hj x p; Apply/and3P; Def Dy: y := (last x p); Move=> [Hxy Up Hp].
Case/splitP2r: p / Hxy Up Hp Dy => [p1' p23 Hx].
Rewrite: -cat_adds uniq_cat last_cat path_cat; Pose p1 := (Adds x p1').
Move/and3P=> [Up1 Up123 Up23] /=; Move/and3P=> [Hp1 Hfy Hp23] Dy.
Case/clinkP: Hfy => [Dnfy | Hfy];
  RightBy Case/hasP: Up123; Exists y;
   [Rewrite: {2 y}Dy | Rewrite: -(Iface ? Hfy)]; Apply: mem_last.
Case/splitPl: p23 / Hx Up123 Up23 Hp23 Dy => [p2' p3 Dx].
Rewrite: -cat_adds has_cat uniq_cat; Pose p2 := (Adds (face y) p2').
Move/norP=> [Up12 Up13]; Move/and3P=> [Up2 Up23 Up3].
Rewrite: path_cat last_cat Dx; Case Dp3: p3 => [|feenx p3'] /=.
  By Move=> _ Dy; Rewrite: /p1 /p2 Dy /= (f_finv (Iface g)) setU11 in Up12.
Move/and3P=> [Hp2 Hx Hp3] Dy; Case/clinkP: Hx => [Dfeenx | Hfx];
  RightBy Rewrite: /p1 Dp3 -Hfx /= (f_finv (Iface g)) setU11 in Up13.
Case/and3P: (Hj (Adds feenx (cat p3' (cat p2 p1)))); Split.
    Rewrite: !last_cat -Dy /= Dnfy (finv_f (Inode g)) mem2_cat mem2_adds set11.
    By Rewrite: -Dfeenx -mem_adds -cat_adds mem_cat /setU -Dx mem_last /= orbT.
  Rewrite: -cat_adds -Dp3 !uniq_cat has_cat negb_orb.
  By Rewrite: Up3 has_sym Up23 has_sym Up13 has_sym Up12 Up2.
By Rewrite: !path_cat -Dy /p1 /p2 /= Dx -{2 x}(f_finv (Iface g)) !clinkF Hp3 Hp2.
Qed.

End Jordan.

Syntactic Definition clinkP := clinkPx | 2.

Implicits Sclink [].

Syntax constr level 0: map_clink_pp [(clink 1!$_)] -> [ "clink" ].
Grammar constr constr0 : constr := map_clink ["clink"] -> [(!clink ?)].

Section DerivedMaps.

Variable g : hypermap.

(* Left permutation (edge -> node) *)

Definition permN : hypermap := (Hypermap (Enode g)::(monic3 node face edge)).

Remark gcomp_permN : (gcomp :: (rel permN)) =2 (gcomp :: (rel g)).
Proof. By Apply: eq_connect => [x y]; Rewrite: /glink /relU /setU orbA orbC. Qed.

Lemma connected_permN : (connected permN) == (connected g).
Proof. By Rewrite: /connected (eq_n_comp gcomp_permN). Qed.

Lemma genus_permN : (genus permN) = (genus g).
Proof.
By Rewrite: /genus /genus_rhs /= addnA addnC /genus_lhs (eq_n_comp gcomp_permN).
Qed.

Lemma planar_permN : (planar permN) == (planar g).
Proof. By Rewrite: /planar genus_permN. Qed.

(* Right permutation (edge -> face) *)

Definition permF : hypermap := (Hypermap (Eface g)::(monic3 face edge node)).

Remark gcomp_permF : (gcomp :: (rel permF)) =2 (gcomp :: (rel g)).
Proof. By Apply: eq_connect => [x y]; Rewrite: /glink /relU /setU orbC orbA. Qed.

Lemma connected_permF : (connected permF) == (connected g).
Proof. By Rewrite: /connected (eq_n_comp gcomp_permF). Qed.

Lemma genus_permF : (genus permF) = (genus g).
Proof.
By Rewrite: /genus /genus_rhs /= addnC addnA /genus_lhs (eq_n_comp gcomp_permF).
Qed.

Lemma planar_permF : (planar permF) == (planar g).
Proof. By Rewrite: /planar genus_permF. Qed.

Remark hmap_dualP : (!monic3 g (finv edge) (finv face) (finv node)).
Proof.
Move=> x; Rewrite: -{1 x}Eface (finv_f (Iedge g)) (finv_f (Inode g)).
Exact (finv_f (Iface g) x).
Qed.

(* Dual: invert all functions, and transpose node and face *)

Definition dual : hypermap := (Hypermap hmap_dualP).

Remark gcomp_dual : (gcomp :: (rel dual)) =2 (gcomp :: (rel g)).
Proof.
Move=> x y; Rewrite: -!clink_glink; Apply: eq_connect => []{x y} x y.
By Rewrite: /clink /relU /setU /eqdf /= (finv_inv (Iface g)) orbC.
Qed.

Lemma connected_dual : (connected dual) == (connected g).
Proof. By Rewrite: /connected (eq_n_comp gcomp_dual). Qed.

Lemma genus_dual : (genus dual) = (genus g).
Proof.
Rewrite: {1}/genus /genus_rhs /= addnCA addnC -addnA /genus_lhs.
Rewrite: (eq_n_comp gcomp_dual) (fcard_finv (Iedge g)).
By Rewrite: (fcard_finv (Inode g)) (fcard_finv (Iface g)).
Qed.

Lemma planar_dual : (planar dual) == (planar g).
Proof. By Rewrite: /planar genus_dual. Qed.

(* Mirror: invert node and face in place, garble edge *)

Remark hmap_mirrorP : (!monic3 g (comp face node) (finv node) (finv face)).
Proof.
Move=> x; Rewrite: /comp (finv_f (Iface g)); Exact (finv_f (Inode g) x).
Qed.

Definition mirror : hypermap := (Hypermap hmap_mirrorP).

Lemma cnode_mirror : (cnode :: (rel mirror)) =2 (cnode :: (rel g)).
Proof. Exact (same_fconnect_finv (Inode g)). Qed.

Lemma cface_mirror : (cface :: (rel mirror)) =2 (cface :: (rel g)).
Proof. Exact (same_fconnect_finv (Iface g)). Qed.

Remark mirror_edge_adj :
  (!rel_adjunction mirror g face (eqdf edge) (eqdf (finv edge)) g).
Proof.
Apply: strict_adjunction; Try Done; Try Apply: Iface; Try Exact (Sedge dual).
  By Apply/subsetP=> [x _]; Rewrite: -(Enode g x) codom_f.
Move; Simpl; Move=> x _ y.
By Rewrite: /eqdf /comp (inj_eqd (Iface g)) (finv_eq_monic (Eedge g)).
Qed.

Lemma order_mirror_edge : (x : g) (!order mirror edge x) = (order edge (node x)).
Proof.
Move=> x; Move: {}mirror_edge_adj => [_ De'].
Apply: (etrans ? (card_image (Iface g) ?)); Apply: eq_card => [y].
Rewrite: cedge1 {2}/edge {4}/mirror /comp -(Enode g y) (image_f (Iface g)).
By Rewrite: -De' // (same_fconnect_finv (Iedge g)).
Qed.

Lemma gcomp_mirror : (gcomp :: (rel mirror)) =2 (gcomp :: (rel g)).
Proof.
Move=> x y; Rewrite: -!clink_glink (same_connect_rev (Sclink g)).
Apply: eq_connect {x y} => [x y]; Rewrite: /clink /relU /setU /eqdf /=. 
Rewrite: (monic2F_eqd (f_finv (finv_inj (Inode g)))) eqd_sym; Congr orb.
By Rewrite: (monic2F_eqd (f_finv (Iface g))) eqd_sym.
Qed.

Lemma connected_mirror : (connected mirror) == (connected g).
Proof. By Rewrite: /connected (eq_n_comp gcomp_mirror). Qed.

Lemma genus_mirror : (genus mirror) = (genus g).
Proof.
Rewrite: {1}/genus /genus_rhs /genus_lhs (eq_n_comp gcomp_mirror).
Step []: (fcard edge g) = (fcard edge mirror).
  Pose Ea := [H](adjunction_n_comp (Sedge mirror) (Sedge dual) H mirror_edge_adj).
  Symmetry; Apply: (etrans (Ea ?)); LeftDone.
  Apply: eq_n_comp; Exact (same_fconnect_finv (Iedge g)).
By Rewrite: (eq_n_comp cnode_mirror) (eq_n_comp cface_mirror).
Qed.

Lemma planar_mirror : (planar mirror) == (planar g).
Proof. By Rewrite: /planar genus_mirror. Qed.

End DerivedMaps.

Section EqualHypermap.

Variable g : hypermap.

Inductive eqm : hypermap -> Prop :=
  EqHypermap : (e, n, f : g -> g; Eenf : (monic3 e n f))
    edge =1 e -> node =1 n -> face =1 f -> (eqm (Hypermap Eenf)).

Variable g' : hypermap.
Hypothesis Hg' : (eqm g').

Remark eqm_gcomp : (n_comp glink g) = (n_comp glink g').
Proof.
Case: {}Hg' => [e n f Eenf Ee En Ef]; Apply: eq_n_comp.
By Apply: eq_connect => [x y]; Rewrite: {1}/glink /relU /setU /eqdf Ee En Ef.
Qed.

Lemma eqm_connected : (connected g) == (connected g').
Proof. By Rewrite: {2}/connected -eqm_gcomp. Qed.

Lemma eqm_genus : (genus g) = (genus g').
Proof.
Rewrite: {2}/genus /genus_lhs -eqm_gcomp; Case: {}Hg' => [e n f Eenf Ee En Ef].
By Rewrite: /genus_rhs /= -(eq_fcard Ee) -(eq_fcard En) -(eq_fcard Ef).
Qed.

Lemma eqm_planar : (planar g) == (planar g').
Proof. By Rewrite: {2}/planar -eqm_genus. Qed.

End EqualHypermap.

Grammar constr constr1 : constr :=
  eq_hypermap [constr0($x) "=m" constr0($y) ] -> [ (eqm $x $y) ].

Syntax constr level 1:
  pp_eq_hypermap [ (eq_hypermap $t1 $t2) ] ->
      [ [<hov 0> $t1:E [0 1]  " =m " $t2:E ] ].

Lemma eqm_sym : (g, g' : hypermap) g =m g' -> g' =m g.
Proof.
Move=> [d e n f Eg] g'; Case {g'} => *; Apply: EqHypermap => [x]; Auto.
Qed.

Lemma dual_inv : (g : hypermap) (dual (dual g)) =m g.
Proof.
Move=> g; Case: g (Iedge g) (Inode g) (Iface g) => [d e n f Eenf] /= *.
By Rewrite: /dual /=; Apply: EqHypermap; Apply: finv_inv.
Qed.

Lemma mirror_inv : (g : hypermap) (mirror (mirror g)) =m g.
Proof.
Move=> g; Case: g (Inode g) (Iface g) => [d e n f Eeg] /= Ing Ifg.
Rewrite: /dual /=; Apply: EqHypermap; Try By Apply: finv_inv.
By Move=> x; Rewrite: -{1 x}Eeg /= /comp !finv_f.
Qed.

Unset Implicit Arguments.
