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

Set Implicit Arguments.

(* The walkup construction (due to Stahl) removes a point from the domain of *)
(* a hypermap, suppressing it from two of the three permutations. The third  *)
(* permutation then needs a slightly more complex adjustment in order to     *)
(* reestablish the triangular identity. Because of this asymmetry, there are *)
(* are actually three ways of applying the transformation. It turns out that *)
(* all three variants are useful in proving the Jordan/Euler equivalence,    *)
(* and later in the four color theorem proof (walkupE is used in cubic.v,    *)
(* walkupN in kempe.v, and walkupF in contract.v)!                           *)

Section Walkup.

Variables g : hypermap; z : g.

Local d' : finSet := (subFin (setC1 z)).
Local to_d' : (x : g) (setC1 z x) -> d' := (subdI 2!?).
Local to_g : d' -> g := (subdE 2!?).

Remark z_to_g : (u : d') (z =d (to_g u)) = false.
Proof. By Move=> [x Hx]; Apply negbE. Qed.

Remark to_g_inj : (injective to_g). Proof. Exact (subdE_inj 2!?). Qed.

Section Skip.

Variable f : g -> g.
Hypothesis Hf : (injective f).

Definition skip1 [x : g] : g := if z =d (f x) then (f z) else (f x).

Lemma skipP : (u : d') (setC1 z (skip1 (to_g u))).
Proof.
Move=> [x Hx]; Rewrite: /skip1 /setC1 /=.
Case Hfx: (z =d (f x)); RightBy Rewrite Hfx.
By Apply/eqP=> [Dfz]; Case/idP: Hx; Rewrite: -(inj_eqd Hf) -Dfz.
Qed.

Definition skip [u : d'] : d' := (to_d' (skipP u)).

Remark inj_skip : (injective skip).
Proof.
Move=> [x Hx] [y Hy]; Injection=> Hxy; Apply: to_g_inj.
Move: Hxy; Rewrite: /= /skip1.
Case: (z =P (f x)) => [Dfx | _].
  Rewrite: {2 z}Dfx (inj_eqd Hf); Case: (x =P y) => [H|_] //.
  By Move=> Dy; Rewrite: (Hf Dy) setC11 in Hy.
Case (z =d (f y)); RightBy Apply Hf.
By Move=> Dx; Rewrite: (Hf Dx) setC11 in Hx.
Qed.

Lemma subdE_skip : (u, v : d') (subdE v) = (f (subdE u)) -> v = (skip u).
Proof.
Move=> [x Hx] [y Hy] /= Dy; Apply: to_g_inj.
By Rewrite: /= /skip1 -Dy (negbE Hy).
Qed.

Lemma base_skip :
  (rel_base to_g (eqdf f) (eqdf skip) (setC1 (finv f z))).
Proof.
Move=> [x Hx]; Rewrite: /eqdf {2}/eqd /= /skip1 /setC1.
By Rewrite: (monic2F_eqd (f_finv Hf)); Move/negbE=> H; Rewrite: H.
Qed.

Lemma fconnect_skip : (u, v : d')
  (fconnect skip u v) = (fconnect f (to_g u) (to_g v)).
Proof.
Move=> u v; Apply/idP/idP; Move/connectP=> [p Hp Ep].
  Rewrite: -~{v}Ep; Elim: p u Hp => [|v p Hrec] u; LeftBy Rewrite: connect0.
  Move/andP=> [Dv H]; Apply: (connect_trans ? (Hrec ? H)) {H Hrec}.
  Rewrite: -~{v Dv}(eqP Dv); Case: u => [x Hx]; Rewrite: /= /skip1.
  Case: (z =P (f x)) => [Dfx | _]; RightBy Apply fconnect1.
  Rewrite: Dfx; Exact (fconnect_iter f (2) (x)).
Elim: {p}(S (size p)) {-2}p u (ltnSn (size p)) Hp Ep => [|n Hrec] // [|y p] u /=.
  By Move=> _ _ Dv; Apply eq_connect0; Apply: to_g_inj.
Move=> Hn; Move/andP=> [Dy Hp] Ep.
Case Hy: (setC1 z y).
  Apply: (connect_trans (connect1 ?) (Hrec p (to_d' Hy) Hn Hp Ep)).
  By Rewrite: /eqdf /= /eqd /= /skip1 (eqP Dy) (negbE Hy) set11.
Case: p Hn Hp Ep => [|fy p] Hn /= Hp Ep; LeftBy Rewrite: /setC1 Ep z_to_g in Hy.
Step Hfy: (setC1 z (f y)).
  Rewrite: /setC1 (eqP (negbEf Hy)) -{1 y}(eqP Dy) (inj_eqd Hf).
  By Rewrite: -(eqP (negbEf Hy)) eqd_sym z_to_g.
Case/andP: Hp => [Dfy Hp]; Rewrite: (eqP Dfy) in Hfy.
Apply: (connect_trans (connect1 ?) (Hrec p (to_d' Hfy) (ltnW Hn) Hp Ep)).
By Rewrite: /eqdf /= /eqd /= /skip1 (eqP Dy) (eqP (negbEf Hy)) set11.
Qed.

Lemma fcard_skip : (addn z =d (f z) (fcard skip d')) = (fcard f g).
Proof.
Def: Hfg := (fconnect_sym Hf); Def: Hsf := (fconnect_sym inj_skip); Simpl.
Pose a := (fconnect f z); Step Ha: (fclosed f (setC a)).
  Apply setC_closed; Apply (intro_closed Hfg); Move=> x y Hxy Hx.
  Exact (connect_trans Hx (connect1 Hxy)).
Step Haf: (rel_adjunction to_g (eqdf f) (eqdf skip) (setC a)).
  Apply: (strict_adjunction Hsf Ha to_g_inj).
    Apply/subsetP=> [x Hax]; Case Hx: (z =d x).
      By Rewrite: -(eqP Hx) /setC /a connect0 in Hax.
    Exact (codom_f ? (to_d' (negbI Hx))).
  Move=> u Hu; Apply: base_skip; Apply/eqP=> [] /= Du.
  By Rewrite: -Du /setC /a fconnect_finv in Hu.
Rewrite: (n_compC a) (n_compC (preimage to_g a)) {3}/a (n_comp_connect Hfg).
Rewrite: (adjunction_n_comp Hfg Hsf Ha Haf) addnA; Congr addn.
Case Hfz: (z =d (f z)).
  Apply: eqP; Apply/set0P=> [[x Hx]]; Apply/andP=> [[_ Hzx]].
  Rewrite: /preimage /= in Hzx; Case/eqP: Hx; Case/connectP: Hzx => [p Hp []] {x}.
  Elim: p {}z (eqP Hfz) Hp => [|y p Hrec] x //= Dx; Case/andP; Case/eqP.
  Rewrite: -Dx; Exact (Hrec ? Dx).
Apply: etrans (n_comp_connect Hsf (to_d' (negbI Hfz))); Apply: eq_n_comp_r.
Move=> u; Apply/idP/idP => [Hu | Hu].
  Rewrite: /preimage /a Hfg in Hu; Case/connectP: Hu => [p Hp Dz].
  Rewrite Hsf; Elim: p u Hp Dz => [|x p Hrec] u /=.
    By Move=> _ Dz; Case/eqP: (z_to_g u); Rewrite: -Dz.
  Case/andP; Move/eqP=> Hx Hp Dz; Case Hv: (z =d x).
    By Apply connect1; Rewrite: /eqdf /eqd /= /skip1 Hx eqd_sym Hv set11.
  Apply: (connect_trans (connect1 ?) (Hrec (to_d' (negbI Hv)) Hp Dz)).
  By Rewrite: /eqdf /eqd /= /skip1 Hx eqd_sym Hv set11.
Rewrite: Hsf in Hu; Case/connectP: Hu => [p Hp Dfz].
Elim: p u Hp Dfz => [|v p Hrec] u /=.
  By Move=> _ Du; Rewrite: Du /preimage /= /a fconnect1.
Move/andP=> [Huv Hp] Dfz.
Case: u Huv => [x Hx]; Rewrite: /eqdf /eqd /= -/to_g /skip1.
Case: (z =P (f x)) => [Dz|_] Dfx.
  By Rewrite: /preimage /a /= Dz Hfg fconnect1.
By Apply: (connect_trans (Hrec ? Hp Dfz)); Rewrite: Hfg; Apply connect1.
Qed.

End Skip.

Definition skip_edge1 [x : g] :=
  if z =d (edge z) then (edge x) else
  if z =d (face (edge x)) then (edge z) else
  if z =d (edge x) then (edge (node z)) else (edge x).

Lemma skip_edgeP : (u : d') (setC1 z (skip_edge1 (to_g u))).
Proof.
Move=> [x Hx]; Rewrite: /= /skip_edge1 /setC1; Case Hez: (z =d (edge z)).
  By Rewrite: (eqP Hez) (inj_eqd (Iedge g)).
Case Hfex: (z =d (face (edge x))); LeftBy Rewrite Hez.
Case Hex: (z =d (edge x)); RightBy Rewrite Hex.
By Rewrite: -(inj_eqd (Iface g)) {1 z}(eqP Hex) Enode eqd_sym Hfex.
Qed.

Definition skip_edge [u : d'] : d' := (to_d' (skip_edgeP u)).

Lemma Eskip : (monic3 skip_edge (skip (Inode g)) (skip (Iface g))).
Proof.
Move=> [x Hx]; Apply: to_g_inj; Rewrite: /= /skip_edge1 /skip1.
Case Hez: (z =d (edge z)).
  Case: (z =P (face (edge x))) => [Dz|_]; RightBy Rewrite: Eedge (negbE Hx).
  By Rewrite: {2 z}(eqP Hez) Eedge set11 Dz Eedge.
Case Hfex: (z =d (face (edge x))).
  Rewrite: {2 6 z}(eqP Hfex) (inj_eqd (Iface g)) (inj_eqd (Iedge g)).
  By Rewrite: (eqd_sym x) (negbE Hx) !Eedge set11.
Case Hex: (z =d (edge x)); RightBy Rewrite: Hfex Eedge (negbE Hx).
By Rewrite: Enode set11 {2 4 z}(eqP Hex) Eedge (negbE Hx).
Qed.

Definition walkupE : hypermap := (Hypermap Eskip).

Syntactic Definition g' := walkupE.

Definition walkupI [u : g'; x : g] : g' :=
  if (subdIopt (setC1 z) x) is (Some v) then v else u.

Syntactic Definition to_g' := walkupI.

Lemma walkup_seq : (p : (seq g); Hp : (setC p z))
  {q : (seq g') | p = (maps to_g q)}.
Proof.
Elim=> [|x p Hrec]; [By Exists (Seq0 g') | Rewrite: /= /setU1].
Move/norP=> [Hx Hp]; Rewrite eqd_sym in Hx.
By Case: (Hrec Hp) => [q Dp]; Exists (Adds (to_d' Hx) q); Rewrite Dp.
Qed.

Lemma walkupI_eq : (u : g'; x : g)
  (to_g (walkupI u x)) = (if z =d x then (to_g u) else x).
Proof.
Move=> u x; Rewrite: /walkupI; Case: (subdIoptP (setC1 z) x) => [v Hx Dv | Hx].
  By Rewrite: (negbE Hx).
By Rewrite: (negbE2 Hx).
Qed.

Lemma walkupI_id : (u, v : g') (walkupI u (to_g v)) = v.
Proof. By Move=> u v; Apply: to_g_inj; Rewrite: -/to_g walkupI_eq z_to_g. Qed.

Lemma not_glink_fp : (negb (glink z z)) ->
  (and3 (z =d (edge z)) = false (z =d (node z)) = false (z =d (face z)) = false).
Proof.
Case/norP; Move=> Hez; Move/norP=> [Hnz Hfz].
By Split; Rewrite eqd_sym; Apply negbE.
Qed.

Lemma base_skip_edge :
  (rel_base 2!g' to_g (eqdf (!edge?)) (eqdf (!edge?))
     (setC (seq2 (node (face z)) (node z)))).
Proof.
Move=> [x Hx]; Rewrite: /setC mem_seq2 /eqdf {2}/eqd /=.
Move/norP=> [Hex Hfex] [y Hy] /=.
Rewrite: (monic2F_eqd (monicF_sym (Eedge g))) in Hex.
Rewrite: (monic2F_eqd (Enode g)) in Hfex.
By Rewrite: /skip_edge1 (negbE Hex) (negbE Hfex) if_same eqd_sym.
Qed.

Lemma glink_fp_skip_edge : (glink z z) -> skip_edge =1 (skip (Iedge g)).
Proof.
Move=> H [x Hx]; Apply: to_g_inj; Move: H.
Rewrite: /glink /relU /setU /eqdf /= /skip1 /skip_edge1 eqd_sym.
Case: (z =P (edge z)) => [Dz | _].
  By Move=> _; Rewrite: Dz (inj_eqd (Iedge g)) (negbE Hx).
Case: ((node z) =P z) => [Dnz | _] Dfz.
  By Rewrite: -(monic2F_eqd (Enode g)) Dnz (negbE Hx).
By Rewrite: -{1 z}(eqP Dfz) (inj_eqd (Iface g)); Case (z =d (edge x)).
Qed.

Definition cross_edge : bool := (cedge z (node z)).

Local z_comp : (set g') := (closure (!clink g') (preimage to_g (clink z))).

Local z_barb : bool := (subset (clink z) (set1 z)).

Remark z_barb_z : z_barb = (and3b z =d (edge z) z =d (node z) z =d (face z)).
Proof.
Apply/subsetP/and3P => [Hbz | [_ Hnz Hfz] x].
  Def: Hfz := (Hbz ? (clinkF ?)); Rewrite: -{1 z}Eedge in Hbz.
  Def: Hfez := (Hbz ? (clinkN ?)); Split; Auto.
    By Rewrite: -(inj_eqd (Iface g)) -(eqP Hfz).
  By Rewrite: {2 z}(eqP Hfez) Eedge set11.
Rewrite: /clink /relU /setU /eqdf.
By Rewrite: {1 z}(eqP Hnz) (finv_f (Inode g)) -(eqP Hfz) orbb.
Qed.

Remark clink_to_g' : (u, v : g') (clink (to_g u) (to_g v)) -> (clink u v). 
Proof.
Move=> [x Hx] [y Hy] /= Hxy; Apply/clinkP; Case/clinkP: Hxy => [Dx | Dy].
  By Left; Apply to_g_inj; Rewrite: /= /skip1 -Dx (negbE Hx).
By Right; Apply to_g_inj; Rewrite: /= /skip1 Dy (negbE Hy).
Qed.

Remark clink_to_g : (u, v : g')
  (connect clink u v) -> (connect clink (to_g u) (to_g v)). 
Proof.
Pose y := [u]if u is (Some x) then (addn x (3)) else (9).

Move=> u v; Move/connectP=> [p Hp []] {v}.
Elim: p u Hp => [|v p Hrec] u /=; LeftBy Rewrite connect0.
Move/andP=> [Hu Hp]; Apply: (connect_trans ? (Hrec ? Hp)).
Case/clinkP: Hu; Move/(congr to_g 5!?); Rewrite: /= /skip1; Move=> Du.
  Rewrite: ~Du; Case Hnv: (z =d (node (to_g v))).
    Apply: (connect_trans (connect1 (clinkN ?))).
    Rewrite: {1 z}(eqP Hnv); Exact (connect1 (clinkN ?)).
  Exact (connect1 (clinkN ?)).
Rewrite: -~Du; Case: (z =P (face (to_g u))) => [Dz | _];
  Apply: (connect_trans (connect1 (clinkF ?))); RightBy Apply: connect0.
Rewrite: Dz; Exact (connect1 (clinkF ?)).
Qed.

Remark z_comp_preimage : z_comp =1 (preimage to_g (connect clink z)).
Proof.
Move=> v; Apply/set0Pn/idP.
  Case; Move=> u; Case/andP; Rewrite: /preimage Sclink; Move=> Huv Hu.
  Exact (connect_trans (connect1 Hu) (clink_to_g Huv)).
Case/connectP; Move=> p0; Case/shortenP; Move=> [|x p] /= Hp Up _ Dv {p0}.
  By Case/eqP: (z_to_g v); Rewrite: -Dv.
Case/andP: Hp => [Hu Hp]; Case/andP: Up; Rewrite: -mem_adds.
Case/(!walkup_seq?); Case=> [|x' p'] //=; Injection=> Dp Dx _.
Exists x'; Rewrite: /setI /preimage /= -Dx Hu andbT.
Apply: (etrans (Sclink g' ? ?)); Apply/connectP.
Exists p'; RightBy Rewrite: Dx Dp last_maps in Dv; Exact (to_g_inj Dv).
Apply/(pathP x') => [i Hi]; Apply clink_to_g'.
Rewrite: -!(sub_maps x' x) //; RightBy Exact (leqW Hi).
Rewrite: {1 sub}lock /= -Dx -Dp -lock.
By Apply: (pathP ? Hp); Rewrite: Dp size_maps.
Qed.

Remark z_barb_comp : z_barb = ((n_comp clink z_comp) =d (0)).
Proof.
Apply/subsetP/set0P=> [Hbz u | Hcz x Hx].
  Apply/andP; Case; Clear; Case/set0Pn; Move=> [x Hx]; Move/andP=> [_ Hzx].
  By Rewrite: /preimage /= in Hzx; Rewrite: /setC1 (Hbz ? Hzx) in Hx.
Apply/idPn => [Hv]; Pose v := ((to_d' Hv) :: g'); Pose u := (root (!clink?) v).
Case/idP: (Hcz u); Rewrite: /setI {1}/u (roots_root (Sclink g')).
By Apply/set0Pn; Exists v; Rewrite: /setI Sclink /u connect_root.
Qed.

Local disconnected : bool := (ltn (1) (n_comp clink z_comp)).

Local n_comp_z [disc : bool] : nat :=
  if (glink z z) then (S z_barb) else (negb disc).

Remark not_cross_edge_walkup : (negb cross_edge) ->
  (u, v : g') (to_g u) = (edge z) -> (to_g v) = (node (face z)) -> (cedge u v).
Proof.
Move=> Hznz u v Du Dv; Case Hez: (z =d (edge z)).
  By Case: u Du => [ez Hez'] Dez; Rewrite: -Dez /= (negbE Hez') in Hez.
Case/connectP: (etrans (Sedge g ? ?) (fconnect1 ? z)).
Move=> p0; Case/shortenP=> [p Hp Up _] Dz {p0}.
Elim/last_ind: p Dz Up Hp => [|p z'] Dz; LeftBy Case/eqP: Hez.
Rewrite: last_add_last -cats1 -cat_adds uniq_cat path_cat /= !andbT orbF.
Move=> Dz'; Rewrite: ~{z'}Dz' /setU1 eqd_sym Hez /= -uniq_adds.
Rewrite: {2}/eqdf (monic2F_eqd (Eedge g)) -Dv -Du.
Move/andP=> [Up Hpz]; Move/andP=> [Hp Ev].
Case: {Hpz}(walkup_seq Hpz) => [p' Dp]; Apply/connectP.
Exists p'; RightBy Rewrite: Dp last_maps in Ev; Exact (to_g_inj (eqP Ev)).
Rewrite: -(path_maps base_skip_edge); LeftBy Rewrite: Dp in Hp.
Apply: subsetP; Rewrite: -disjoint_subset disjoint_has has_sym.
Simpl in Dp; Rewrite: -belast_maps /= -Dp orbF -Dv.
Apply/orP=> [[Hpv | Hpnz]].
  By Rewrite: lastI (eqP Ev) -cats1 uniq_cat /= Hpv andbC in Up.
Case: (negP Hznz); Apply: (connect_trans (fconnect1 ? ?)).
Rewrite: -Du; Exact (path_connect Hp (mem_belast Hpnz)).
Qed.

Remark disconnected_cross_edge :
  disconnected -> (negb (glink z z)) /\ cross_edge.
Proof.
Move=> Hdz; Apply: andP; Apply/idPn=> [Hgze].
Step Huw: (u, w: g') (node (to_g u)) = z ->
  (face z) = (to_g w) -> (connect clink u w).
  Move=> u w Du Dw; Case Hez: (z =d (edge z)).
    Apply eq_connect0; Apply to_g_inj; Apply Inode.
    By Rewrite: -Dw (eqP Hez) Eedge.
  Case Hnz: (z =d (node z)).
    By Rewrite: -{1 z}Du (inj_eqd (Inode g)) eqd_sym z_to_g in Hnz.
  Case Hfz: (z =d (face z)); LeftBy Rewrite: Dw z_to_g in Hfz.
  Rewrite: /glink /relU /setU /eqdf -!(eqd_sym z) Hez Hnz Hfz /= in Hgze.
  Apply: (connect_trans ? (connect1 (clinkN ?))).
  Pose v := ((to_d' (negbI Hez)) :: g'); Apply connect_trans with v.
    Rewrite Sclink; Apply connect1; Apply/clinkP; Right.
    Apply to_g_inj; Apply Inode; Rewrite: /= /skip1 -(monic2F_eqd (Enode g)).
    By Rewrite: eqd_sym Hnz Eedge.
  Rewrite clink_glink; Apply: (connect_sub [u1,u2;H](connect1 (sub_relUl ? H))).
  Apply (not_cross_edge_walkup Hgze); [Done | Rewrite: /= -Dw /skip1].
  By Rewrite: -(monic2F_eqd (Eedge g)) eqd_sym Hez.
Rewrite: /disconnected ltnNge leq_eqVlt ltnS leqn0 -z_barb_comp orbC in Hdz.
Case/idP: Hdz {Hgze}; Case Hbz: z_barb; [Done | Apply/eqP].
Case/set0Pn: Hbz; Move=> x; Case/andP=> [Hzx Hx]; Pose u := ((to_d' Hx) :: g').
Rewrite: -(eq_n_comp_r 2!(closure (!clink?) (set2 u u))).
  By Rewrite: (n_comp_closure2 (Sclink g')) connect0.
Move=> v; Apply/set0Pn/set0Pn; Case; Move=> w; Case/andP=> [Hvw Dw].
  Exists w; Rewrite: /set2 orbb in Dw.
  By Rewrite: /setI Hvw /preimage -(u =P w Dw).
Exists u; Rewrite: /setI /set2 orbb set11 andbT; Apply: (connect_trans Hvw).
Case/clinkP: Dw; Case/clinkP: Hzx; Move=> Dx Dw; Auto.
    By Apply eq_connect0; Apply to_g_inj; Apply Inode; Rewrite: -Dw.
  Rewrite Sclink; Auto.
By Apply eq_connect0; Apply to_g_inj; Rewrite: -Dw.
Qed.

Local ae [x : g] : bool := (has (cedge x) (seq2 z (node z))).

Remark Hae : (fclosed edge (setC ae)).
Proof. By Move=> x y; Case/eqP; Rewrite: /setC /ae /= -!cedge1. Qed.

Remark adj_ae : (rel_adjunction to_g (!eqdf g edge) (!eqdf g' edge) (setC ae)).
Proof.
Apply: (strict_adjunction (Sedge g') Hae to_g_inj).
  Apply/subsetP=> [x Haex].
  Case Hx: (z =d x); RightBy Exact (codom_f ? (to_d' (negbI Hx))).
  By Rewrite: -(eqP Hx) /setC /ae /= connect0 in Haex.
Move=> [x Hx] Haex [y Hy]; Apply base_skip_edge; Clear: y Hy.
Rewrite: /setC mem_seq2 /=; Apply/orP=> [Dx]; Case/orP: Haex.
Rewrite: /seq1 /=; Case: Dx; Case/eqP {x Hx}.
  By Left; Rewrite: cedge1 Eface connect0.
By Right; Rewrite: connect0.
Qed.

Lemma same_cskip_edge : (u : g') (negb (ae (to_g u))) ->
  (v : g') (cedge u v) = (cedge (to_g u) (to_g v)).
Proof. By Case adj_ae; Auto. Qed.

Lemma sub_cskip_edge : (negb cross_edge) ->
  (u, v : g') (cedge (to_g u) (to_g v)) -> (cedge u v).
Proof.
Move=> Hz u v Huv; Case Hez: (z =d (edge z)).
  Apply: (etrans (eq_fconnect (glink_fp_skip_edge ?) ? ?)).
    By Apply/orP; Left; Rewrite eqd_sym in Hez.
  By Rewrite fconnect_skip.
Case/connectP: Huv; Move=> p.
Elim: {p}(S (size p)) {-2}p u (ltnSn (size p)) => [|n Hrec] //.
Move=> [|y p] u /= Hn; LeftBy Move=> *; Apply eq_connect0; Apply to_g_inj.
Move/andP=> [Dy Hp] Ep; Case Hy: (z =d y).
  Case: p Hn Hp Ep => [|ez p] /= *; LeftBy Rewrite: Ep z_to_g in Hy.
  Case/andP: Hp => [Dez Hp].
  Step Eu: (to_g u) = (node (face z)).
    By Rewrite: (eqP Hy) -(eqP Dy) Eedge.
  Step Eu': (to_g (to_d' (negbI Hez))) = (edge z) By Done.
  Rewrite: -(same_cedge (not_cross_edge_walkup Hz Eu' Eu)).
  Move: Hp Ep; Rewrite: -(eqP Dez) -(eqP Hy) -{1 2 (edge z)}Eu'.
  Exact (Hrec ? ? (ltnW Hn)).
Apply: (connect_trans ? (Hrec ? (to_d' (negbI Hy)) Hn Hp Ep)).
Case Hfy: (z =d (face y)).
  Step Eeu: (to_g (edge u)) = (edge z).
    By Rewrite: /= /skip_edge1 Hez (eqP Dy) Hfy.
  Step Hnfz: (negb z =d (node (face z))).
    By Rewrite: -(monic2F_eqd (Eedge g)) eqd_sym Hez.
  Rewrite cedge1; Pose u' := ((to_d' Hnfz) :: g').
  Apply: (connect_trans (not_cross_edge_walkup (?) 3!u' ? ?)); Auto.
  Apply: connect1; Rewrite: /eqdf /eqd /= /skip_edge1 Hez Eface set11.
  By Rewrite: {1 4 z}(eqP Hfy) Eface (inj_eqd (Iface g)) (eqd_sym y) Hy set11.
By Apply connect1; Rewrite: /eqdf /eqd /= /skip_edge1 Hez (eqP Dy) Hfy Hy set11.
Qed.

Lemma cskip_edge_merge : (negb cross_edge) ->
  (u, v : g') (ae (to_g u)) -> (cedge u v) = (ae (to_g v)).
Proof.
Move=> Hz u v Hu; Apply/idP/idP => [Huv|].
  Apply/idPn => [Hv]; Case/idPn: Hu.
  Rewrite: Sedge (same_cskip_edge Hv) Sedge in Huv.
  Exact (etrans (closed_connect Hae Huv) Hv).
Move: Hu; Rewrite: /ae /= !orbF.
Case Hez: (z =d (edge z)).
  Step Hzz: (fcycle (!edge?) (seq1 z)) By Rewrite: /= /eqdf eqd_sym Hez.
  Rewrite: -!(Sedge g z) !(fconnect_cycle Hzz (setU11 ? ?)) /= /setU1 !z_to_g.
  By Move=> Hu Hv; Apply (sub_cskip_edge Hz); Rewrite: (same_cedge Hu) Sedge.
Def: Hnfz := Hez; Rewrite: eqd_sym (monic2F_eqd (Eedge g)) in Hnfz.
Pose uez := (to_d' (negbI Hez)); Pose unfz := (to_d' (negbI Hnfz)).
Def: Henz := (!not_cross_edge_walkup Hz uez unfz (erefl ?) (erefl ?)).
Rewrite: cedge1r in Henz; Step Eenz: (to_g (!edge g' unfz)) = (edge (node z)).
  Rewrite: /= /skip_edge1 Hez Eface set11.
  Case: (z =P (face z)) => [Dfz | _] //; Case/idP: Hz.
  By Rewrite: /cross_edge -{1 z}Eface -Dfz Sedge fconnect1.
Case/orP=> [Hu|Hu]; Case/orP=> [Hv| Hv];
  Try By Apply (sub_cskip_edge Hz); Rewrite: (same_cedge Hu) Sedge.
  Apply: (connect_trans ? (connect_trans Henz ?)); Apply (sub_cskip_edge Hz).
    By Rewrite: /= -cedge1r.
  By Rewrite: Eenz -cedge1 Sedge.
Rewrite: Sedge in Henz.
Apply: (connect_trans ? (connect_trans Henz ?)); Apply (sub_cskip_edge Hz).
  By Rewrite: Eenz -cedge1r.
By Rewrite: /= -cedge1 Sedge.
Qed.
 
Remark fcard_skip_edge :
  (addn (if (glink z z) then (S z =d (edge z)) else (double (negb cross_edge)))
        (fcard edge g'))
    = (S (fcard edge g)).
Proof.
Case Hgzz: (glink z z).
  Congr S; Rewrite: -(fcard_skip (Iedge g)); Congr addn; Apply: eq_fcard.
  Exact (glink_fp_skip_edge Hgzz).
Case: {Hgzz}(not_glink_fp (negbI Hgzz)) => [Hez Hnz Hfz].
Def: Hnfz := Hez; Rewrite: eqd_sym (monic2F_eqd (Eedge g)) in Hnfz.
Pose unfz := ((to_d' (negbI Hnfz)) :: g').
Pose unz := ((to_d' (negbI Hnz)) :: g').
Def: Heg := (Sedge g); Def: Heg' := (Sedge g').
Rewrite: (n_compC ae) (n_compC (preimage to_g ae)).
Rewrite: (adjunction_n_comp Heg Heg' Hae adj_ae) -addSn !addnA; Congr addn.
Step Eae: ae =1 (fclosure (!edge?) (set2 z (node z))).
  Move=> x; Rewrite: /ae /= orbF; Apply/orP/set0Pn; Case.
      By Exists z; Rewrite: /setI /set2 set11 /= andbT.
    By Exists (node z); Rewrite: /setI /set2 set11 orbT andbT.
  Move=> y; Case/andP; Move=> Hxy.
  By Case/orP; Move/eqP=> Dy; Rewrite: -Dy in Hxy; Auto.
Rewrite: (eq_n_comp_r Eae) (n_comp_closure2 Heg).
Step Hag': (preimage to_g ae) =1 (fclosure (!edge?) (set2 unfz unz)).
  Move=> u; Rewrite: /preimage /ae /= orbF; Apply/idP/set0Pn => [Hu | [v Hv]].
    Step [y Huy Hy]: (EX y | (cedge (to_g u) y)
                           & (set2 (to_g unfz) (to_g unz) y)).
      Rewrite: /set2 /=; Case/orP: Hu.
        By Exists (node (face z)); [Rewrite: cedge1r Eface | Rewrite set11].
      By Exists (node z); RightBy Rewrite: set11 orbT.
    Case/connectP: Huy Hy {Hu} => [p Hp []] {y}.
    Elim: p u Hp => [|y p Hrec] u /=; LeftBy Exists u; Rewrite: /setI connect0.
    Move/andP=> [Dy Hp].
    Case Hex: (z =d (edge (to_g u))).
      Exists u; Rewrite: /setI connect0 /set2 /eqd /= {1 z}(eqP Hex) Eedge.
      By Rewrite: /to_g set11.
    Case Hfex: (z =d (face (edge (to_g u)))).
      Exists u; Rewrite: /setI connect0 /set2 /eqd /= {3 z}(eqP Hfex) Eedge.
      By Rewrite: /to_g set11 orbT.
    Step Hu': (setC1 z y) By Rewrite: /setC1 -(eqP Dy) Hex.
    Case/(Hrec (to_d' Hu') Hp) {Hrec}; Move=> v; Case/andP=> [Hu'v Dv].
    Exists v; Simpl in Dv; Rewrite: /setI Dv andbT.
    Apply: (connect_trans (connect1 ?) Hu'v).
    By Rewrite: /eqdf /eqd /= /skip_edge1 Hez -/to_g Hex Hfex.
  Case/andP: Hv; Move/connectP => [p Hp []] {v}.
  Elim: p u Hp => [| v p Hrec] [x Hx] /=.
    Rewrite: {1}/set2 /eqd /=; Clear; Case/orP; Move/eqP=> Dx.
      By Rewrite: -Dx cedge1 Eface connect0.
    By Rewrite: Dx connect0 orbT.
  Move=> H Ep; Case/andP: H; Rewrite: {1}/eqdf /eqd /= /skip_edge1 Hez.
  Case Hex: (z =d (edge x)); LeftBy Move=> _ _; Rewrite: (eqP Hex) fconnect1.
  Case Hfex: (z =d (face (edge x))).
    By Move=> _ _; Rewrite: (eqP Hfex) Eedge connect0 orbT.
  Move=> Dex Hp; Rewrite: !(cedge1 x) (eqP Dex); Exact (Hrec ? Hp Ep).
Rewrite: (eq_n_comp_r Hag') (n_comp_closure2 Heg') -/cross_edge.
Case Hznz: cross_edge; Rewrite: /cross_edge in Hznz.
  Rewrite: -{1 z}Eface -cedge1 in Hznz; Case/connectP: Hznz; Move=> q.
  Case/shortenP=> [[|z' p] Hp Up _] {q}/= Dnfz.
    By Rewrite: (Inode ? Dnfz) set11 in Hfz.
  Rewrite: /= {1}/eqdf Eface in Hp; Case/andP: Hp; Move=> Dz'.
  Case/eqP: z' / Dz' Up Dnfz; Simpl; Case/and3P.
  Move/norP=> [_ Hpnfz] Hpz Up Dnz Hp.
  Case: (walkup_seq Hpz) => [[|uez p'] Dp]; Simpl in Dp.
    By Rewrite: Dp in Dnz; Case/eqP: {}Hnz.
  Rewrite: Dp /= in Hp; Case/andP: Hp => [Dez Hp].
  Step Hunz: (!eqdf g' edge unz uez).
    By Rewrite: /eqdf /eqd /= -/to_g /skip_edge1 -(eqP Dez) Hez Enode !set11.
  Step Dunz: unz = (last uez p').
    By Apply: to_g_inj; Rewrite: -last_maps /= -Dnz Dp.
  Step Hp': (fcycle (!edge?) (Adds uez p')).
    Simpl in Dunz Hunz Dp; Rewrite: /= -cats1 path_cat -Dunz /= Hunz andbT.
    Rewrite: -(path_maps base_skip_edge) //; Apply: subsetP.
    Rewrite: -belast_maps -disjoint_subset disjoint_has has_sym /= orbF.
    Rewrite: -Dnz Dp /=; Apply/orP=> [[Hp'nfz | Hp'nz]].
      Case (negP Hpnfz); Rewrite Dp; Exact (mem_belast Hp'nfz).
    By Rewrite: Dp lastI -cats1 uniq_cat /= Hp'nz /= andbF in Up.
  Rewrite: Heg' (fconnect_cycle Hp'); RightBy Rewrite: Dunz mem_last.
  By Rewrite: Dp /= in Hpnfz; Rewrite: -(mem_maps to_g_inj) /= Hpnfz.
Step Hw: (cedge unfz unz); RightBy Rewrite Hw.
Rewrite: Heg' cedge1; Apply: (not_cross_edge_walkup (negbI Hznz)); RightDone.
By Rewrite: /= /skip_edge1 Hez Enode set11.
Qed.

Lemma base_clink_walkup :
  (!rel_base g g' to_g clink clink (setC (seq2 (edge (node z)) (node z)))).
Proof.
Move=> [x Hx]; Rewrite: /setC mem_seq2 /=; Move/norP=> [Hex Hfex] [y Hy].
Rewrite: /clink /relU /setU /eqdf ![g'](monic2F_eqd (f_finv (Inode g'))) /=.
Rewrite: {3 4}/eqd /= /skip1 -(monic2F_eqd (monicF_sym (Eface g))) (negbE Hex).
Case: (z =P (node y)) => [[]|_] //.
By Rewrite: !(eqd_sym x) (negbE Hfex) (negbE Hx).
Qed.

Lemma clink_walkup_path : (u : g'; x : g; p : (seq g))
  (negb (Adds x p z)) ->
  (negb (belast x p (node z))) -> (negb (belast x p (edge (node z)))) ->
  (!path g' clink (walkupI u x) (maps (walkupI u) p)) = (path clink x p).
Proof.
Move=> u x p Hpz Hpnz Hpenz.
Step Ep: (maps to_g (maps (walkupI u) (Adds x p))) = (Adds x p).
  Elim: {x p}(Adds x p) Hpz {Hpnz Hpenz} => [|x p Hrec] //=.
  By Move/norP=> [Hx Hp]; Rewrite: walkupI_eq eqd_sym (negbE Hx) -{2 p}(Hrec Hp).
Simpl in Ep; Injection: Ep => Dp Dx; Rewrite: -{2 p}Dp -{2 x}Dx.
Rewrite: (path_maps base_clink_walkup); [Done | Apply: subsetP].
Rewrite: -disjoint_subset disjoint_has -belast_maps has_sym /= Dp Dx orbF.
By Rewrite: (negbE Hpenz).
Qed.

Lemma card_walkup : (card walkupE) = (pred (card g)).
Proof. Exact (etrans (card_sub_dom ?) (cardC1 z)). Qed.

Lemma card_S_walkup : (card g) = (S (card walkupE)).
Proof. By Rewrite: card_walkup (cardD1 z). Qed.

Remark n_comp_glink_walkup :
  (addn (n_comp_z disconnected) (n_comp glink g')) = (S (n_comp glink g)).
Proof.
Def: Hsg := (Sclink g); Def: Hsg' := (Sclink g').
Pose a := (connect clink z); Step Ha : (closed clink (setC a)).
  Apply: setC_closed => [x y Hxy]; Apply: (same_connect_r Hsg).
  By Apply connect1.
Step Haa : (!rel_adjunction g g' to_g clink clink (setC a)).
  Apply (strict_adjunction Hsg' Ha to_g_inj).
    Apply/subsetP=> [x Hax]; Case Hx: (z =d x).
      By Rewrite: /setC /a -(eqP Hx) connect0 in Hax.
    Exact (codom_f to_g (to_d' (negbI Hx))).
  Move=> [x Hx] Hax; Apply base_clink_walkup; Simpl in Hax.
  Rewrite: /setC mem_seq2 ~{Hx}/=; Apply/orP=> [Dx]; Case/idP: Hax.
  Case: Dx; Case/eqP {x}; Rewrite: /a Hsg.
    Rewrite: -{2 z}Enode; Apply connect1; Apply clinkF.
  Apply connect1; Apply clinkN.
Rewrite: -2![g'](eq_n_comp (!clink_glink g')) (n_compC (preimage to_g a)).
Rewrite: (n_compC a) (adjunction_n_comp Hsg Hsg' Ha Haa) !addnA -addSn.
Congr addn; Rewrite: /a (n_comp_connect Hsg) -(eq_n_comp_r z_comp_preimage).
Rewrite: /n_comp_z; Case Hdz: disconnected.
  Case: (disconnected_cross_edge Hdz) => [Hgzz _]; Rewrite: (negbE Hgzz).
  Case: (not_glink_fp Hgzz) => [_ Hfez Hfz].
  Rewrite: eqd_sym (monic2F_eqd (Enode g)) in Hfez.
  Apply: eqP; Rewrite: /= add0n eqn_leq; Apply/andP; Split; RightBy Exact Hdz.
  Pose u := ((to_d' (negbI Hfez))::g'); Pose v := ((to_d' (negbI Hfz))::g').
  Rewrite: -(eq_n_comp_r 2!(closure (!clink g') (set2 u v))).
    By Rewrite: n_comp_closure2; Case (connect (!clink g') u v).
  Move=> w; Rewrite: /z_comp /closure !(disjoint_sym (connect (!clink g') w)).
  Congr negb; Apply: eq_disjoint => []{w} w; Apply/orP/clinkP.
    By Move=> [Dw | Dw]; [Left | Right]; Rewrite: -(? =P w Dw) /= ?Eedge.
  Rewrite: /eqd /= -/to_g.
  By Move=> [Dz|[]]; [Left | Right]; Rewrite: ?Dz ?Enode set11.
Move: (negbI Hdz); Rewrite: /disconnected -leqNgt leq_eqVlt ltnS leqn0.
Rewrite: -z_barb_comp orbC; Case Hbz: z_barb.
  Step Hez : (z =d (edge z)) By Rewrite z_barb_z in Hbz; Case (andP Hbz).
  Rewrite: {2 z}(eqP Hez) glinkE; Rewrite z_barb_comp in Hbz.
  By Rewrite (eqP Hbz).
By Simpl; Move/eqP=> H; Rewrite: H if_same.
Qed.

Remark genus_lhs_walkupE :
  (addn (double (n_comp_z disconnected)) (genus_lhs g')) = (S (genus_lhs g)).
Proof.
Rewrite: /genus_lhs card_walkup addnA -double_add n_comp_glink_walkup.
By Rewrite: (cardD1 z) addnCA.
Qed.

Remark genus_rhs_walkupE :
  (addn (double (n_comp_z cross_edge)) (genus_rhs g')) = (S (genus_rhs g)).
Proof.
Rewrite: /genus_rhs -(fcard_skip (Inode g)) -(fcard_skip (Iface g)).
Rewrite: -addSn -fcard_skip_edge addnC-!addnA; Symmetry.
Do 3 (Rewrite: addnC -!addnA; Congr addn).
Rewrite: /n_comp_z /glink /relU /setU /eqdf -!(eqd_sym z) z_barb_z.
Case Hnz: (z =d (node z)).
  Rewrite: -(eqd_sym (face z)) (monic2F_eqd (Eface g)) -(eqP Hnz).
  By Case (z =d (edge z)).
Case Hfz: (z =d (face z)); RightBy Case (z =d (edge z)).
By Rewrite: -(eqd_sym (edge z)) (monic2F_eqd (Eedge g)) -(eqP Hfz) Hnz.
Qed.

Lemma genus_walkupE_eq :
  (glink z z) \/ (negb cross_edge) -> (genus walkupE) = (genus g).
Proof.
Rewrite: {2}/genus -subSS -genus_lhs_walkupE -genus_rhs_walkupE /n_comp_z.
Move=> [Hgzz | Hznz]; LeftBy Rewrite: Hgzz subn_add2l.
Case Hdz: disconnected; RightBy Rewrite: Hznz /= subn_add2l.
By Case (negP Hznz); Case: (disconnected_cross_edge Hdz).
Qed.

Lemma le_genus_walkup: (leq (genus walkupE) (genus g)).
Proof.
Rewrite: {2}/genus -subSS -genus_lhs_walkupE -genus_rhs_walkupE /n_comp_z.
Case Hgzz: (glink z z); LeftBy Rewrite subn_add2l; Exact (leqnn ?).
Case Hdz: disconnected.
  Case: (disconnected_cross_edge Hdz) => [_ Hznz]; Rewrite: Hznz subn_add2l.
  Exact (leqnn ?).
Case cross_edge; RightBy Rewrite subn_add2l; Exact (leqnn ?).
Apply: half_leq; Apply: leq_sub2r; Apply leq_addl.
Qed.

Lemma planar_walkupE : (planar g) -> (planar walkupE).
Proof. Rewrite: /planar -!leqn0; Exact (leq_trans le_genus_walkup). Qed.

Lemma even_genus_walkup : (even_genus walkupE) -> (even_genus g).
Proof.
Move=> Elhs; Apply: eq_add_S; Rewrite: /genus -subSS -genus_lhs_walkupE Elhs.
Rewrite: -addnS -genus_rhs_walkupE !addnA subn_add2r -double_add -double_sub.
Rewrite: half_double -double_add -(addnC (n_comp_z cross_edge)) leq_add_sub //.
Apply: (leq_trans ? (leq_addr ? ?)).
Rewrite: /n_comp_z; Case (glink z z); LeftBy Exact (leqnn ?).
Case Hdz: disconnected; RightBy Case cross_edge.
By Case: (disconnected_cross_edge Hdz) => [_ Hznz]; Rewrite Hznz.
Qed.

Definition skip_clink : (rel g) :=
  [x,y](orb x =d (skip1 node y) (skip1 face x) =d y).

Lemma skip_clink_walkup : (x' : g'; p' : (seq g'))
  (path clink x' p') = (path skip_clink (to_g x') (maps to_g p')).
Proof.
Move=> x' p'; Elim: p' x' => [|y' p' Hrec] x' //=; Rewrite: ~Hrec.
By Congr andb; Congr orb; Rewrite: /eqdf (monic2F_eqd (f_finv (Inode g'))).
Qed.

Lemma skip_clinkf : (x, y : g) (skip_clink x y) -> (negb x =d (node z)) ->
  (clink x y) \/ (face x) = z /\ (face z) = y.
Proof.
Move=> x y Hxy' Hxnz; Case: {Hxy'}(orP Hxy'); Unfold skip1.
  Case (z =d (node y)); Move=> Dx; LeftBy Rewrite: Dx in Hxnz.
  By Left; Rewrite: (eqP Dx) clinkN.
Case: (z =P (face x)) => [Dfx | _] Dfy.
  By Right; Split; RightBy Exact (eqP Dfy).
By Left; Rewrite: -(eqP Dfy) clinkF.
Qed.

Remark splice_face_clink : (x : g; p : (seq g))
  (path skip_clink x p) -> (uniq (Adds x p)) -> (negb (belast x p (node z))) ->
    (path clink x p)
  \/ (EX p1 | (path (!clink?) x p1) /\ (face (last x p1)) = z
            & (EX p2 | (path clink (face z) p2)
                     & (cat p1 (Adds (face z) p2)) = p)).
Proof.
Move=> x p /=; Elim: p x => [|y p Hrec] x/=; LeftBy Left.
Move/andP=> [Hxy' Hp']; Move/andP=> [Hpx Up]; Move/norP=> [Hxnz Hpnz].
Case: {Hxy' Hxnz}(skip_clinkf Hxy' Hxnz) => [Hxy | [Dfx Dfz]].
  Case: {Hrec Hpnz}(Hrec ? Hp' Up Hpnz); LeftBy Left; Rewrite Hxy.
  Move=> [p1 [Hp1 Ep1] [p2 Hp2 Dp]]; Right; Exists (Adds y p1).
    By Split; LeftBy Rewrite: /= Hxy.
  By Exists p2; RightBy Rewrite: /= Dp.
Right; Exists (Seq0 g); [By Split | Exists p; Rewrite: Dfz // /=].
Elim: p y Hp' Hpx Hpnz {Hrec Dfz Up} => [|y2 p Hrec] y1 //=.
Move/andP=> [Hy' Hp']; Move/norP=> [Hy1x Hpx]; Move/norP=> [Hy1nz Hpnz].
Case: (skip_clinkf Hy' Hy1nz) => [Hy | [Hy _]]; LeftBy Rewrite: Hy /=; Auto.
By Case/eqP: Hy1x; Apply Iface; Rewrite Hy.
Qed.

Lemma jordan_walkupE : (jordan g) -> (jordan walkupE).
Proof.
Move=> Hj [|u pw] //; Apply/and3P; Rewrite: skip_clink_walkup.
Def: Einng := (finv_f (Inode g)).
Pose x := (to_g u); Pose p' := (maps to_g pw).
Pose y := (to_g (finv node (last u pw))); Pose p := (Adds x p').
Move=> [Hynu Upw Hpw]; Step Hpz: (negb (p z)).
  By Apply/(mapsPx ? (Adds ? ?) ?) => [[v _ Hv]]; Case/eqP: (z_to_g v).
Step Up: (uniq p) By Rewrite: -(uniq_maps to_g_inj) in Upw.
Step Hynx: (mem2 p' y (skip1 node x)).
  By Rewrite: -(mem2_maps to_g_inj) in Hynu.
Step Ep: (skip1 node y) = (last x p').
  Rewrite: /p' /x last_maps; Exact (congr to_g (f_finv (Inode ?) (last u pw))).
Case Hxy: (x =d y); LeftBy Rewrite: /p (eqP Hxy) /= (mem2l Hynx) in Up.
Step Hzy: (z =d y) = false By Exact (z_to_g ?).
ClearBody p' x y; Move: {pw Upw Hynu}Ep Hynx; Unfold skip1.
Case Hpnz: (negb (p (node z))).
  Case: (z =d (node y)).
    By Move=> Dnz; Rewrite: /p Dnz mem_last in Hpnz.
  Case: (z =d (node x)) => [|] Ep Hynx.
    By Rewrite: /p /= (setU1r x (mem2r Hynx)) in Hpnz.
  Case: {Hpw}(splice_face_clink Hpw Up).
      By Apply/idP=> [Hnz]; Case/idP: Hpnz; Apply: mem_belast.
    By Move=> Hp; Case/and3P: (Hj p); Split; Rewrite: // -Ep Einng.
  Move=> [p1' [Hp1 Ep1] [p2' Hp2 Dp']].
  Def Dp1: p1 := (Adds x p1'); Def Dp2: p2 := (Adds (face z) p2').
  Case/and3P: (Hj (Adds x (cat p1' (Adds z p2)))); Split.
      Rewrite: -Dp' last_cat /= in Ep; Rewrite: -Dp' -Dp2 in Hynx.
      By Rewrite: last_cat {2 p2}Dp2 /= -Ep Einng; Apply mem2_splice1.
    Move: Hpz Up; Rewrite: /p -Dp' -!cat_adds -Dp1 -Dp2 !uniq_cat mem_cat /=.
    By Move/norP=> [Hp1z Hp2z]; Rewrite: negb_orb Hp1z Hp2z.
  By Rewrite: path_cat Hp1 Dp2 /= -{1 z}Ep1 !clinkF.
Move: Hpnz Up Hpz Hpw; Rewrite: ~/p; Move/idP; Case/splitPl {p'} => [p' q Ep].
Rewrite: -cat_adds uniq_cat mem_cat path_cat last_cat; Def Dp: p := (Adds x p').
Move/and3P=> [Up Upq Uq]; Move/norP=> [Hpz Hqz].
Case Hqnz: (q (node z)).
  By Case/hasP: Upq; Exists (node z); RightBy Rewrite: Dp -Ep mem_last.
Move/andP=> [Hpw Hqw]; Rewrite: Dp in Up.
Case: {Hpw}(splice_face_clink Hpw Up).
    By Rewrite: lastI Ep -cats1 uniq_cat /= orbF in Up; Case/and3P: Up.
  Rewrite: -Dp in Up; Case Dq: {-3}q Hqw => [|fez q'].
    Move=> _ Hp; Rewrite: Dq cats0 Ep /=.
    Case: (z =P (node y)) => [Dz|_]; RightBy Move=> *; Case/eqP: Hzy; Apply Inode.
    Clear; Rewrite: {1 z}Dz (inj_eqd (Inode g)) eqd_sym Hxy.
    Move=> Hynx; Case/and3P: (Hj (Adds x (add_last p' z))); Split.
        By Rewrite: last_add_last Dz Einng -cats1 mem2_cat Hynx.
      By Rewrite: -cats1 -cat_adds -Dp uniq_cat Up /= orbF Hpz.
    By Rewrite: -cats1 path_cat Ep Hp /= clinkN.
  Rewrite: /= Ep; Move/andP=> [Dfez Hqw] Hp.
  Case Hzfez: (z =d fez); LeftBy Rewrite: Dq (eqP Hzfez) /= setU11 in Hqz.
  Case: (z =d (node y)) => [|] Eq; LeftBy Rewrite: Dq Eq mem_last in Hqnz.
  Rewrite Dq in Uq; Case: {Hqw}(splice_face_clink Hqw Uq).
      By Apply/idP=> [H]; Case/idP: Hqnz; Rewrite: Dq mem_belast.
    Move=> Hq Hynx; Rewrite: -Dq in Uq; Case Hzq: (clink z fez).
      Case/and3P: (Hj (Adds x (cat p' (Adds z q)))); Split.
          Rewrite: last_cat {2 q}Dq /= -Eq Einng.
          Case: (z =P (node x)) Hynx => [Dz|_] Hynx; RightBy Apply mem2_splice1.
          Rewrite: (mem2r_cat Hqnz) in Hynx.
          By Rewrite: -Dz mem2_cat /= setU11 (mem2l Hynx) orbC.
        By Rewrite: -cat_adds -Dp uniq_cat Up /= negb_orb Upq Hpz Hqz.
      By Rewrite: path_cat Hp Dq /= Ep clinkN Hzq.
    Case/orP: Dfez; Rewrite: /skip1.
      Case: (z =P (node fez)) => [Dz|_] Dnz; LeftBy Rewrite: Dz clinkN in Hzq.
      By Rewrite: (Inode g (eqP Dnz)) Dq /= setU11 in Hqz.
    Case: (z =d (face (node z))) => [|] Dfez.
      By Rewrite: -(eqP Dfez) clinkF in Hzq.
    Case: (z =P (node x)) Hynx => [Dz | _] Hynx.
      Case/and3P: (Hj (Adds z (Adds x (cat p' q)))); Split.
          By Rewrite: /= last_cat {2 q}Dq /= -Eq Einng mem2_adds Hxy.
        Rewrite: -cat_adds -Dp /= uniq_cat Up Upq mem_cat /setU negb_orb.
        By Rewrite: Hqz Hpz.
      Rewrite: Dq /= {1 z}Dz path_cat clinkN Hp Ep /=.
      By Rewrite: -{1 fez}(eqP Dfez) clinkF.
    Case/and3P: (Hj (Adds x (cat p' q))); Split.
        By Rewrite: last_cat {2 q}Dq /= -Eq Einng.
      By Rewrite: -cat_adds -Dp uniq_cat Up Upq.
    By Rewrite: path_cat Dq Hp Ep /= -{1 fez}(eqP Dfez) clinkF.
  Move=> [q1' [Hq1 Eq1] [q2' Hq2 Dq']].
  Rewrite: -Dq in Uq; Case: {q'}Dq' Dq Eq; Rewrite: last_cat /= -cat_adds.
  Def Dq1: q1 := (Adds fez q1'); Def Dq2: q2 := (Adds (face z) q2').
  Move=> Dq Eq2; Rewrite: Dq mem_cat in Hqz; Rewrite: Dq uniq_cat in Uq.
  Case/norP: Hqz => [Hq1z Hq2z]; Case/and3P: Uq => [Uq1 Uq12 Uq2].
  Rewrite: Dq has_cat in Upq; Case/norP: Upq => [Upq1 Upq2].
  Case/orP: Dfez; Rewrite: Dq /skip1.
    Case: (z =P (node fez)) {q Dq Hqnz} => [Dz | _] Dnz;
      RightBy Rewrite: (Inode g (eqP Dnz)) Dq1 /= setU11 in Hq1z.
    Case: (z =P (node x)) {Dnz} => [Dz' | _] Hynx.
      Case/hasP: Upq1; Exists fez; LeftBy Rewrite: Dq1 /= setU11.
      By Rewrite: Dz in Dz'; Rewrite: (Inode g Dz') Dp /= setU11.
    Case Hq1y: (q1 y).
      Case/and3P: (Hj (Adds fez (cat q1' (Adds z q2)))); Split.
          Rewrite: last_cat {2 q2}Dq2 /= -Eq2 Einng -Dz.
          Rewrite: Dq1 /= in Hq1y; Case/orP: Hq1y.
            Rewrite: -(inj_eqd (Inode g)) Eq2 -Dz; Move/eqP=> Eq2'.
            By Rewrite: Eq2' Dq2 mem_last in Hq2z.
          By Move=> Hq1'y; Rewrite: mem2_cat Hq1'y /= setU11 /= orbT.
        By Rewrite: -cat_adds -Dq1 uniq_cat Uq1 /= negb_orb Hq1z Uq12 Hq2z.
      By Rewrite: path_cat Hq1 Dq2 /= -{1 z}Eq1 !clinkF.
    Case Hq1nx: (q1 (node x)).
      Rewrite Dq1 in Hq1nx; Case/splitPl: {q1' Eq1}Hq1nx Dq1 Hq1 => [q3' q4 Eq3].
      Rewrite: -cat_adds; Def Dq3: q3 := (Adds fez q3'); Move=> Dq1.
      Move: Uq12 Upq1 {Hq1y}(negbI Hq1y) Hq1z Hynx Uq1.
      Rewrite: ~{q1}Dq1 has_sym !has_cat !mem_cat uniq_cat path_cat.
      Move/norP=> [Uq23 _]; Move/norP=> [Upq3 _]; Move/norP=> [Hq3y _].
      Move/norP=> [Hq3z _] Hynx; Move/and3P=> [Uq3 Uq34 _]; Move/andP=> [Hq3 _].
      Case Hq423: (cat q4 q2 (last fez q3')).
        Case (elimN (hasPx q3 (cat q4 q2))).
          By Rewrite: has_cat negb_orb Uq34 has_sym.
        By Exists (last fez q3'); RightBy Rewrite: Dq3 mem_last.
      Rewrite: -catA catA -Eq3 ~{q4 Hq423 Uq34}(mem2r_cat Hq423) in Hynx.
      Case/and3P: (Hj (Adds fez (cat q3' (cat p (Adds z q2))))); Split.
          Rewrite: catA last_cat {2 q2}Dq2 /= -Eq2 Einng -Dz mem2_cat /=.
          Apply/orP; Right; Move: (mem2l Hynx).
          Rewrite: !mem_cat /setU (negbE Hq3y) orbF orbC.
          By Move=> Hpy; Rewrite: Dp /= (setU1r x Hpy) setU11.
        Rewrite: -cat_adds -Dq3 !uniq_cat Uq3 Up has_cat /= !negb_orb Upq2.
        By Rewrite: !(has_sym q3) Upq3 Uq23 Hq3z Hpz Hq2z.
      By Rewrite: !path_cat Hq3 Eq3 Dp Dq2 /= Hp Ep !clinkN clinkF.
    Case/and3P: (Hj (Adds x (cat p' (Adds z q2)))); Split.
        Rewrite: catA (mem2lr_splice Hq1y Hq1nx) in Hynx.
        By Rewrite: last_cat {2 q2}Dq2 /= -Eq2 Einng; Apply mem2_splice1.
      By Rewrite: -cat_adds -Dp uniq_cat Up /= negb_orb Upq2 Hpz Hq2z.
    By Rewrite: path_cat Hp Ep Dq2 /= clinkN clinkF.
  Case: (z =P (face (node z))) => [Dz | _] Dfnz Hynx.
    Case/hasP: Upq1; Exists (node z); RightBy Rewrite: -Ep Dp mem_last.
    By Rewrite Dz in Eq1; Rewrite: -(Iface g Eq1) Dq1 mem_last.
  Case/and3P: (Hj (Adds x (cat p' (cat q1 (Adds z q2))))); Split.
      Rewrite: catA last_cat {2 q2}Dq2 /= -Eq2 Einng.
      Case: (z =P (node x)) Hynx => [Dz | _].
        Rewrite: -Dz -Dq (mem2r_cat Hqnz) mem2_cat /= setU11 orbC.
        By Move=> Hpy; Rewrite:  mem_cat /setU (mem2l Hpy).
      By Rewrite catA; Exact [H](mem2_splice1 H ?).
    Rewrite: -cat_adds -Dp !uniq_cat has_cat /= !negb_orb.
    By Rewrite: Up Upq1 Hpz Upq2 Uq1 Hq1z Uq12 Hq2z.
  By Rewrite: !path_cat Ep Dq1 Dq2 /= Hp Hq1 -{2 z}Eq1 -(eqP Dfnz) !clinkF.
Move=> [p1' [Hp1 Ep1] [p2' Hp2 Dp']]; Rewrite: -Dp in Up; Rewrite Ep in Hqw.
Case: {p'}Dp' Ep Dp; Rewrite: last_cat /= -cat_adds; Move=> Ep2.
Def Dp1: p1 := (Adds x p1'); Def Dp2: p2 := (Adds (face z) p2'); Move=> Dp.
Rewrite: Dp uniq_cat in Up; Case/and3P: Up => [Up1 Up12 Up2].
Rewrite: Dp has_sym has_cat in Upq; Case/norP: Upq => [Uqp1 Uqp2].
Rewrite: Dp mem_cat in Hpz; Case/norP: Hpz => [Hp1z Hp2z].
Case Hp2nx: (setU1 z p2 (node x)).
  Case/and3P: (Hj (Adds x (cat p1' (Adds z p2)))); Split.
      Rewrite: last_cat {2 p2}Dp2 /= Ep2 Einng mem2_cat mem2_adds set11 Hp2nx.
      By Rewrite: orbT.
    By Rewrite: -cat_adds -Dp1 uniq_cat /= negb_orb Up1 Hp1z Up12 Hp2z.
  By Rewrite: path_cat Hp1 Dp2 /= -{1 z}Ep1 !clinkF.
Case/norP: Hp2nx => [Hznx Hp2nx]; Rewrite: (negbE Hznx) Ep2.
Case Dq: {1 2}q Hqw => [|fez q'] /=.
  Rewrite: Dq cats0 /=; Case: (z =P (node y)) => [Dz | _] _;
    RightBy Move=> Dy; Case/eqP: Hzy; Apply Inode.
  Rewrite: (mem2r_cat (negbE Hp2nx)); Move=> _ Hynx.
  Case/and3P: (Hj (Adds x (add_last p1' z))); Split.
      By Rewrite: last_add_last {2 z}Dz Einng -cats1 mem2_cat Hynx.
    By Rewrite: -cats1 -cat_adds -Dp1 uniq_cat /= Up1 orbF andbT.
  By Rewrite: -cats1 path_cat Hp1 /= -Ep1 clinkF.
Case: (z =d (node y)); LeftBy Move=> _ Dnz; Rewrite: Dnz Dq mem_last in Hqnz.
Move=> H Eq Hynx; Case: {H}(andP H) => [Dfez Hqw]; Rewrite Dq in Uq.
Case: {Hqw}(splice_face_clink Hqw Uq); Rewrite: -Dq in Uq.
    By Apply/idP=> [Hnz]; Case/idP: Hqnz; Rewrite: Dq mem_belast.
  Case/orP: Dfez {Hqnz}; Rewrite: /skip1.
    Case: (z =P (node fez)) => [Dz | _] Dnz;
      RightBy Rewrite: (Inode g (eqP Dnz)) Dq /= setU11 in Hqz.
    Case Hp2y: (p2 y) {Dnz} => [|] Hq.
      Case Hp1y: (p1' y).
        By Case/hasP: Up12; Exists y; RightBy Rewrite: Dp1 /= (setU1r x Hp1y).
      Rewrite Dp2 in Hp2y.
      Case/splitPl: {p2' Hp2nx}Hp2y Ep2 Dp2 Hp2 => [p3' p4' Ep3].
      Rewrite: last_cat -cat_adds lastI path_cat ~Ep3 cat_add_last.
      Move: (belast (face z) p3') => p3; Def Dp4: p4 := (Adds y p4').
      Move=> Ep4 Dp2; Move/andP=> [_ Hp4] {p3'}; Move: Up12 Uqp2 Up2 Hp2z.
      Rewrite: Dp2 !has_cat uniq_cat mem_cat; Move/norP=> [_ Up14].
      Move/norP=> [_ Uqp4]; Move/and3P=>  [_ Up34 Up4]; Move/norP=> [_ Hp4z].
      Case Hp3y: (p3 y).
        By Case/hasP: Up34; Exists y; LeftBy Rewrite: Dp4 /= setU11.
      Rewrite: Dp2 -catA (mem2l_cat Hp1y) -catA (mem2l_cat Hp3y) in Hynx.
      Case/and3P: (Hj (Adds x (cat p1' (cat (Adds z q) p4)))); Split.
          Rewrite: !last_cat {2 p4}Dp4 /= Ep4 Einng mem2_cat mem2_adds set11.
          Rewrite: orbC /setU1 !orbA; Apply/orP; Right.
          By Move: (mem2r Hynx); Rewrite: !mem_cat /setU orbC.
        Rewrite: -cat_adds -Dp1 uniq_cat Up1 /= uniq_cat has_cat Uq mem_cat.
        By Rewrite: /setU !negb_orb Hp1z Hqz Hp4z Uqp4 Up14 has_sym Uqp1.
      By Rewrite: !path_cat Hp1 Dq Dp4 /= Hq -{1 z}Ep1 Dz -Eq !clinkN clinkF.
    Rewrite: (mem2lr_splice Hp2y (negbE Hp2nx)) in Hynx.
    Case/and3P: (Hj (Adds x (cat p1' (Adds z q)))); Split.
        By Rewrite: last_cat {2 q}Dq /= -Eq Einng; Apply mem2_splice1.
      By Rewrite: -cat_adds -Dp1 uniq_cat Up1/= negb_orb Hp1z has_sym Uqp1 Hqz.
    By Rewrite: path_cat Hp1 Dq /= -{1 z}Ep1 clinkF Dz clinkN.
  Case: (z =d (face (node z))) => [|] Dfz Hq.
    Case/hasP: Uqp2; Exists fez; RightBy Rewrite: Dq /= setU11.
    By Rewrite: -(eqP Dfz) Dp2 /= setU11.
  Case/and3P: (Hj (Adds x (cat p1' (cat (Adds z p2) q)))); Split.
      By Rewrite: !last_cat {2 q}Dq /= -Eq Einng mem2_splice1 ?catA.
    Rewrite: -cat_adds -Dp1 uniq_cat Up1 /= has_cat uniq_cat Up2 mem_cat /setU.
    By Rewrite: !negb_orb Hp1z Up12 has_sym Uqp1 Hqz Hp2z has_sym Uqp2.
  By Rewrite: !path_cat Hp1 Dp2 Dq /= Hp2 Hq -{1 z}Ep1 Ep2 -(eqP Dfz) !clinkF.
Move=> [q1 _ [q2 _ Dq']]; Case/hasP: Uqp2; Exists (face z).
  By Rewrite: Dp2 /= setU11.
By Rewrite: Dq -Dq' /= /setU1 mem_cat /setU /= setU11 !orbT.
Qed.

End Walkup.

Section WalkupAux.

Variables g : hypermap; z : g.

Definition walkupN : hypermap := (permF (walkupE z::(permN g))).
Definition walkupF : hypermap := (permN (walkupE z::(permF g))).

Lemma planar_walkupN : (planar g) -> (planar walkupN).
Proof.
Rewrite: /walkupN /planar genus_permF -(genus_permN g); Apply: planar_walkupE.
Qed.

Lemma planar_walkupF : (planar g) -> (planar walkupF).
Proof.
Rewrite: /walkupF /planar genus_permN -(genus_permF g); Apply: planar_walkupE.
Qed.

End WalkupAux.

Unset Implicit Arguments.

