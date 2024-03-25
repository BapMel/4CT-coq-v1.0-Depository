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
Require hypermap.
Require geometry.
Require color.
Require coloring.

Set Implicit Arguments.

(* Reduction to cubic maps; since this is not the inductive case, we can    *)
(* construct a larger map (indeed, we split each dart in 6!).               *)

Section Cube.

Variable g : hypermap.

Inductive cube_tag : Set :=
    CTn  : cube_tag
  | CTen : cube_tag
  | CTf  : cube_tag
  | CTnf : cube_tag
  | CTe  : cube_tag
  | CTfe : cube_tag.

Syntactic Definition tag := cube_tag.

Definition cube_tag_eq [o, o' : tag] : bool :=
  Cases o o' of
    CTn  CTn  => true
  | CTen CTen => true
  | CTf  CTf  => true
  | CTnf CTnf => true
  | CTe  CTe  => true
  | CTfe CTfe => true
  | _ _ => false
  end.

Definition cube_tagData : dataSet.
Apply (DataSet 2!cube_tag_eq); Abstract By Do 2 Case; Constructor.
Defined.

Canonical Structure cube_tagData.

Definition cube_tagSet : finSet.
Apply (FinSet 2!(Seq CTn CTen CTf CTnf CTe CTfe)); Abstract By Case.
Defined.

Canonical Structure cube_tagSet.

Definition cube_dart : finSet := (prodFin cube_tagSet g).
Syntactic Definition d := cube_dart.

Local tsI : tag -> g -> d := (!proddI cube_tagSet g).
Local tsE [u : d] : g := (proddE2 u).

Definition cube_edge [u : d] : d :=
  let (o, x) = u in Cases o of
    CTen => (tsI CTnf (edge x))
  | CTf  => (tsI CTe  (node (face x)))
  | CTnf => (tsI CTen (node (face x)))
  | CTe  => (tsI CTf  (edge x))
  | CTfe => (tsI CTn  x)
  | CTn  => (tsI CTfe x)
  end.

Definition cube_node [u : d] : d :=
  let (o, x) = u in Cases o of
    CTn  => (tsI CTen (node x))
  | CTen => (tsI CTfe x)
  | CTf  => (tsI CTnf (edge x))
  | CTnf => (tsI CTe  (node (face x)))
  | CTe  => (tsI CTf  x)
  | CTfe => (tsI CTn  (face (edge x)))
  end.

Definition cube_face [u : d] : d :=
  let (o, x) = u in Cases o of
    CTn  => (tsI CTen x)
  | CTen => (tsI CTf  x)
  | CTf  => (tsI CTnf x)
  | CTnf => (tsI CTn (face x))
  | CTe  => (tsI CTe (edge x))
  | CTfe => (tsI CTfe (node x))
  end.

Remark cube_monic3 : (monic3 cube_edge cube_node cube_face).
Proof. By Do 2 Case; Move=> x; Rewrite: /= ?Eface ?Eedge ?Enode. Qed.

Local cmap : hypermap := (Hypermap cube_monic3).

Definition cube := (locked cmap).

Lemma plain_cube : (plain cube).
Proof.
Unlock cube; Apply/plainP=> [u _].
By Case: u; Case; Split; Rewrite: //= ?Eedge ?Eface ?Enode.
Qed.

Lemma cubic_cube : (cubic cube).
Proof.
Unlock cube; Apply/cubicP=> [u _].
By Case: u; Case; Split; Rewrite: //= ?Eedge ?Eface ?Enode.
Qed.

Local ate : (set cmap) := [u] (proddE1 u) =d CTe.
Local atn : (set cmap) := [u] (proddE1 u) =d CTfe.
Local atf : (set cmap) := (setC (setU ate atn)).

Local cf : (rel cmap) := (eqdf cube_face).


Remark Hcf : (connect_sym cf). Proof. Exact (Sface cmap). Qed.

Remark Hate : (closed cf ate).
Proof.
By Apply: (intro_closed Hcf) => [[o x] v Dv]; Rewrite: -(? =P v Dv); Case o.
Qed.

Remark Hatn : (closed cf atn).
Proof.
By Apply: (intro_closed Hcf) => [[o x] v Dv]; Rewrite: -(? =P v Dv); Case o.
Qed.

Remark Hatf : (closed cf atf).
Proof. By Move=> u v Huv; Rewrite: /atf /setC /setU (Hate Huv) (Hatn Huv). Qed.

Remark Hcfe : (rel_adjunction (tsI CTe) cf (eqdf (!edge?)) ate).
Proof.
Apply: (strict_adjunction (Sedge g) Hate) => // [x y Hxy | ].
  Exact (congr tsE Hxy). 
Apply/subsetP=> [[o x]]; Rewrite: /ate /=.
Move/eqP=> Eo; Rewrite Eo; Exact (codom_f ? x).
Qed.

Remark Hcfn : (rel_adjunction (tsI CTfe) cf (eqdf (!node?)) atn).
Proof.
Apply: (strict_adjunction (Snode g) Hatn) => // [x y Hxy | ].
  Exact (congr tsE Hxy).
Apply/subsetP=> [[o x]]; Rewrite: /atn /=.
Move/eqP=> Eo; Rewrite Eo; Exact (codom_f ? x).
Qed.

Remark Hcff : (rel_adjunction (tsI CTnf) cf (eqdf (!face?)) atf).
Proof.
Apply: (intro_adjunction (Sface g) Hatf 9![x; _](tsE x)) => [[o x] Hox | x].
  Rewrite: /sumfin_subdom in x Hox *; Split.
      Case: o Hox => // [] _;
        Do 4 First [Apply: connect0 | Apply: (connect_trans (fconnect1 ? ?))].
    Move=> v _ Dv; Rewrite: -~{v Dv}(? =P v Dv) /=.
    Case: o Hox => // [] _; First [Apply: connect0 | Apply: fconnect1].
Split; LeftBy Apply: connect0.
Move=> y; Case/eqP {y}; Do 3 Apply: (connect_trans (fconnect1 ? ?)).
Apply: fconnect1.
Qed.

Lemma genus_cube : (genus cube) = (genus g).
Proof.
Move: plain_cube cubic_cube; Unlock cube; Move=> HcgE HcgN.
Step HcD: (card cmap) = (mult (6) (card g)).
  By Apply: (etrans (card_prod_dom ? ?)).
Step HcE: (fcard edge cmap) = (mult (3) (card g)).
  Apply: eqP; Rewrite: -(order_div_card (Iedge ?) HcgE) //.
  By Rewrite mult_assoc_l; Apply/eqP.
Step HcN: (fcard node cmap) = (mult (2) (card g)).
  Apply: eqP; Rewrite: -(order_div_card (Inode ?) HcgN) //.
  By Rewrite mult_assoc_l; Apply/eqP.
Step HcFE: (fcard edge g) = (n_comp cf ate).
  By Apply: etrans (esym (adjunction_n_comp Hcf (Sedge g) Hate Hcfe)).
Step HcFN: (fcard node g) = (n_comp cf atn).
  By Apply: etrans (esym (adjunction_n_comp Hcf (Snode g) Hatn Hcfn)).
Step HcFF: (fcard face g) = (n_comp cf atf).
  By Apply: etrans (esym (adjunction_n_comp Hcf (Sface g) Hatf Hcff)).
Step HcF: (fcard face cmap) = (genus_rhs g).
  Rewrite: /n_comp /genus_rhs HcFE -(cardIC ate); Congr addn.
    By Apply: eq_card => [u]; Rewrite: /setI -andbA.
  Rewrite: -(cardIC atn) HcFN HcFF; Congr addn.
    By Apply: eq_card => [u]; Rewrite: /setI -!andbA; Case: u; Case.
  By Apply: eq_card => [u]; Rewrite: /setI /atf /setU /setC negb_orb -!andbA.
Step HcG: (n_comp glink cmap) = (n_comp glink g).
  Move: (Sclink g) (Sclink cmap) => Sg Scg.
  Rewrite: -![g'](eq_n_comp (!clink_glink g')).
  Def: g0 := [g'](connect0 (!glink g')).
  Def: g1e := [g'; u](connect1 2!(!glink g') (glinkE u)).
  Def: g1n := [g'; u](connect1 2!(!glink g') (glinkN u)).
  Def: g1f := [g'; u](connect1 2!(!glink g') (glinkF u)).
  Step Ha: (closed (!clink cmap) cmap) By Done.
  Apply: (adjunction_n_comp 3!(tsI CTnf) Scg Sg Ha).
  Apply: (intro_adjunction Sg Ha 9![x;_](tsE x)) => [u _ | x _].
    Split.
      Case: u => [o x] /=.
      Pose cgx := [o'](connect (!glink cmap) (tsI o' x) (tsI CTnf x)).
      Step Hxe: (cgx CTe) By Exact (connect_trans (g1n ? ?) (g1f ? ?)).
      Step Hxnf: (cgx CTfe).
        Apply: (connect_trans (g1e ? ?)).
        Do 3 Apply: (connect_trans (g1f ? ?)); Apply: connect0.
      Rewrite (!clink_glink cmap); Case: o => //;
        Do 4 First [Apply: g0 | Apply: (connect_trans (g1f ? ?))].
    Move=> v _; Rewrite clink_glink; Case/clinkP=> [Du | Dv].
      Rewrite: ~{u}Du Sglink; Case: v; Case => //= [] x.
        Exact (connect_trans (g1f ? ?) (g1n ? ?)).
      Exact (connect_trans (g1e ? ?) (g1f ? ?)).
    By Rewrite: -~{v}Dv; Case: u; Case => [] x /=.
  Split; LeftBy Apply: connect0.
  Move=> y; Rewrite (!clink_glink cmap); Case/clinkP=> [Dx | Dy].
    Apply connect_trans with (tsI CTn y).
      Rewrite: Sglink Dx; Apply: (connect_trans (g1n cmap ?)) => /=.
      Exact (connect_trans (g1f cmap ?) (g1f cmap ?)).
    Do 3 Apply: (connect_trans (g1f cmap ?)); Apply: g0.
  By Rewrite: -Dy; Do 4 Apply: (connect_trans (g1f cmap ?)).
Rewrite: {1}/genus /genus_lhs /genus_rhs HcD HcE HcN HcF HcG /= addnI addn0.
By Rewrite: addnC -!addnA !subn_add2l addnC.
Qed.

Lemma planar_cube : (planar cube) == (planar g).
Proof. PropCongr; Exact (congr [n](n =d (0)) genus_cube). Qed.

Lemma cube_colorable : (four_colorable cube) -> (four_colorable g).
Proof.
Unlock cube; Move=> [k [HkE HkF]]; Exists [x](k (tsI CTnf x)); Split.
  Move=> x; Apply/eqcP=> [Hkx]; Case/eqcP: (HkE (tsI CTnf (edge x))) => /=.
  By Symmetry; Do 2 Apply: (etrans ? (eqcP (HkF ?))) => /=; Rewrite Eedge.
By Move=> x; Apply/eqcP; Do 4 Apply: (etrans ? (eqcP (HkF ?))) => /=.
Qed.

Lemma bridgeless_cube : (bridgeless cube) == (bridgeless g).
Proof.
Case: (Hcff) => [_ Ecff].
Unlock cube; PropCongr; Apply/set0P/set0P=> [Htg x | Hg u].
  Apply/idP=> [Hgx]; Case/idP: {Htg}(Htg (tsI CTen x)) => /=.
  By Do 2 Apply: (connect_trans (fconnect1 ? ?)) => /=; Rewrite Ecff in Hgx.
Apply/idP=> [Hgu]; Case: u Hgu (closed_connect Hatf Hgu); Case => //= [] x.
  Move=> Hgu; Case/idP: {Hg}(Hg x); Rewrite: Ecff //.
  Apply: (connect_trans ? Hgu); Rewrite (Sface cmap).
  Exact (connect_trans (fconnect1 ? ?) (fconnect1 ? ?)).
Move=> Hgu; Case/idP: {Hg}(Hg (node (face x))).
Rewrite: Sface Eface Ecff //; Apply: (connect_trans Hgu ?).
Exact (connect_trans (fconnect1 ? ?) (fconnect1 ? ?)).
Qed.

End Cube.

Unset Implicit Arguments.


