(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require tacticext.
Require boolprop.
Require funs.
Require dataset.
Require natprop.
Require znat.
Require frac.
Require Setoid.
Require real.

Set Implicit Arguments.

(* Construcion of R = complete totally ordered field.         *)
(* We use the standard Dedekind cut construction.             *)
(* We actually make R into a setoid, taking non-comparability *)
(* as equality. This allows the construction of an internal   *)
(* model in the calculus of constructions, assuming only the  *)
(* classical excluded middle.                                 *)

Section DedekindReals.

Hypothesis Hclassical : excluded_middle.

(* patch for v7.3.1 Setoid Prop rewrite at root bug *)
Local xProp [P : Prop] : Prop := P.
Remark xPropE : (P : Prop) (xProp P) -> P. Proof. Done. Qed.
Add Morphism xProp : dedekind_xProp_morphism. Proof. Tauto. Qed.
Tactic Definition IP := Apply xPropE.

(* We use nontrivial open upper order ideals of frac to represent the reals. *)

Syntactic Definition ddseg := frac -> Prop.

Definition ideals [x : ddseg] : Prop :=
  (f1, f2 : frac) (leqf f1 f2) -> (x f1) -> (x f2).

Definition opens [x : ddseg] : Prop :=
  (f : frac) (x f) -> (EX f' | (ltf f' f) & (x f')).

Definition hass [x : ddseg] : Prop := (EX f | (x f)).

Definition hasNs [x : ddseg] : Prop := (EX f | ~(x f)).

Record dreal : Type := Dreal {
  dd_seg : ddseg;
  dd_ideal : (ideals dd_seg);
  dd_open : (opens dd_seg);
  dd_ub : (hass dd_seg);
  dd_lb : (hasNs dd_seg)
  }.

Coercion dd_seg : dreal >-> FUNCLASS.

Definition leqdr [x1, x2 : dreal] : Prop := (f : frac) (x2 f) -> (x1 f).

Definition eqdr [x1, x2 : dreal] : Prop := (leqdr x1 x2) /\ (leqdr x2 x1).

Lemma leqdrr : (x : dreal) (leqdr x x). Proof. By Move=> x f. Qed.
Implicits leqdrr [].
Hints Resolve leqdrr.

Lemma eqdr_refl : (x : dreal) (eqdr x x). Proof. By Split. Qed.
Hints Resolve eqdr_refl.

Lemma eqdr_sym : (x1, x2 : dreal) (eqdr x1 x2) -> (eqdr x2 x1).
Proof. By Move=> x1 x2 [Hx12 Hx21]; Split. Qed.
Hints Immediate eqdr_sym.

Lemma leqdr_trans : (x1, x2, x3 : dreal)
  (leqdr x1 x2) -> (leqdr x2 x3) -> (leqdr x1 x3).
Proof. By Rewrite: /leqdr; Auto. Qed.

Lemma eqdr_trans : (x1, x2, x3 : dreal)
  (eqdr x1 x2) -> (eqdr x2 x3) -> (eqdr x1 x3).
Proof.
By Move=> x1 x2 x3 [Hx12 Hx21] [Hx23 Hx32]; Split; Apply leqdr_trans with x2.
Qed.

Lemma eqdr_theory : (Setoid_Theory dreal eqdr).
Proof. Split; Auto; Exact eqdr_trans. Qed.

Add Setoid dreal eqdr eqdr_theory.

Add Morphism dd_seg : dd_seg_morphism.
Proof. By Move=> x y f [_ Hyx]; Auto. Qed.

Add Morphism leqdr : leqdr_morphism.
Proof.
By Move=> x1 y1 x2 y2 Dx1 Dx2 H f; Move: (H f); Rewrite: Dx1 Dx2.
Qed.

Lemma eqf_dr : (x : dreal; f1, f2 : frac) (eqf f1 f2) -> (x f1) <-> (x f2).
Proof. By Move=> x f1 f2; Case/andP; Split; Apply: dd_ideal. Qed.

Section RealFrac.

Variable f : frac.

Definition fracs : ddseg := [f'](ltf f f').

Lemma ideals_frac : (ideals fracs).
Proof. Rewrite: /fracs; Move=> f1 f2 *; EApply ltf_leq_trans; EAuto. Qed.

Lemma opens_frac : (opens fracs).
Proof. By Move=> f3; Case/frac_dense=> [f2]; Exists f2. Qed.

Lemma hass_frac : (hass fracs).
Proof.
By Exists (addf F1 f); Rewrite: addfC /fracs /ltf -{2 f}addF0 leqf_add2l.
Qed.

Lemma hasNs_frac : (hasNs fracs).
Proof. By Exists f; Rewrite: /fracs ltff. Qed.

Definition fracdr : dreal := (Dreal ideals_frac opens_frac hass_frac hasNs_frac).

End RealFrac.

Coercion fracdr : frac >-> dreal.

Section RealSup.

Variable E : dreal -> Prop.

Definition supds0 : ddseg :=
  [f](EX f' | (ltf f' f) & (x : dreal) (E x) -> (x f')).
Definition has_supdr0 : Prop := (hass supds0) /\ (hasNs supds0).
Definition supds : ddseg := [f]IF has_supdr0 then (supds0 f) else (ltf F0 f).

Lemma ideals_sup : (ideals supds).
Proof.
Move=> f1 f2 Hf12; Case=> [[HE Hf1]]; [Left | Right]; Split; Auto.
  By Case: Hf1 => [f Hf HfE]; Exists f; LeftBy Apply: ltf_leq_trans Hf12.
By Apply: ltf_leq_trans Hf12.
Qed.

Lemma opens_sup : (opens supds).
Proof.
Move=> f; Case=> [[HE Hf]].
  Case: Hf => [f2 Hff2 Hf2]; Case: (frac_dense Hff2) => [f1 Hff1 Hf12].
  By Exists f1; LeftDone; Left; Split; LeftDone; Exists f2.
By Case: (frac_dense Hf) => [f1 Hff1 Hf1]; Exists f1; LeftDone; Right; Split.
Qed.

Lemma hass_sup : (hass supds).
Proof.
Case: (Hclassical has_supdr0) => [HE]; RightBy Exists F1; Right; Split.
By Case: {}HE =>  [[f Hf] _]; Exists f; Left; Split.
Qed.

Lemma hasNs_sup : (hasNs supds).
Proof.
Case: (Hclassical has_supdr0) => [HE]; RightBy Exists F0; Do 2 Case; Auto.
By Case: {}HE =>  [_ [f Hf]]; Exists f; Do 2 Case; Auto.
Qed.

Definition supdr : dreal := (Dreal ideals_sup opens_sup hass_sup hasNs_sup).

End RealSup.

Lemma eqdr_sup : (E, E' : dreal -> Prop)
  ((x, x' : dreal) (eqdr x x') -> (E x) <-> (E' x'))
     -> (eqdr (supdr E) (supdr E')).
Proof.
Move=> E E' DE; Step Esup: (f : frac) (supds0 E f) <-> (supds0 E' f).
  Move=> f; Rewrite: /supds0; Split; 
    By Move=> [f' Hff' Hf']; Exists f'; RightBy Move=> x; Case (DE x x); Auto.
Step Ehas: (hass (supds0 E)) <-> (hass (supds0 E')).
  By Split; Move=> [f Hf]; Exists f; Move: Hf; Rewrite: (Esup f).
Step EhasN: (hasNs (supds0 E)) <-> (hasNs (supds0 E')).
  By Split; Move=> [f Hf]; Exists f; Move: Hf; Rewrite: (Esup f).
By Split; Move=> f; Rewrite: /leqdr /= /supds /has_supdr0 /IF Ehas EhasN (Esup f).
Qed.

Local hasdr [E : dreal -> Prop] : Prop :=
  (EXT x | (E x)).

Local ubdr [E : dreal -> Prop; z : dreal] : Prop :=
  (y : dreal) (E y) -> (leqdr y z).

Local has_supdr [E : dreal -> Prop] : Prop :=
  (hasdr E) /\ (hasdr (ubdr E)).

Local boundeddr [x : dreal; E : dreal -> Prop] : Prop :=
  (EXT y | (E y) & (leqdr x y)).

Remark has_supdr0I : (E : dreal -> Prop)
  (has_supdr E) -> (has_supdr0 E).
Proof.
Move=> E [[x Hx] [z Hz]]; Split.
  Move: (dd_ub z) {x Hx} => [f Hf]; Case: (dd_ub f) => [f1].
  Move/dd_open=> [f2 Hf12 Hff2]; Exists f1; Exists f2; LeftDone.
  By Move=> x Hx; Apply Hz; RightBy Apply: dd_ideal Hf; Apply ltfW.
Move: (dd_lb x) {z Hz} => [f Hf]; Exists f; Case=> [f1 Hff1 Hf1]; Case: Hf.
By Apply: dd_ideal (Hf1 ? Hx); Apply ltfW.
Qed.
Hints Resolve has_supdr0I.

Lemma ubdr_sup : (E : dreal -> Prop) (has_supdr E) -> (ubdr E (supdr E)).
Proof.
Move=> E HE x Hx f [[_ [f' Hff' Hf']] | [[]]]; Auto.
Apply: (dd_ideal (ltfW Hff')); Auto.
Qed.

Lemma leqdr_sup_ub : (E : dreal -> Prop) (has_supdr E) ->
  (x : dreal) (ubdr E x) -> (leqdr (supdr E) x).
Proof.
Move=> E HE x Hx f; Move/dd_open=> [f1 Hff1 Hf1].
By Left; Split; Auto; Exists f1; RightBy Move=> y Hy; Apply Hx.
Qed.

Lemma supdr_total : (x : dreal; E : dreal -> Prop) (has_supdr E) -> 
  (boundeddr x E) \/ (leqdr (supdr E) x).
Proof.
Move=> x E HE; Case: (Hclassical (boundeddr x E)); LeftBy Left.
Move=> HxE; Right; Apply leqdr_sup_ub; Auto; Move=> y Hy f Hxf.
Case: (Hclassical (EX f' | (ltf f' f) & (y f'))) => [[f' Hf'f] | Hxy].
  By Apply: dd_ideal; Apply ltfW.
Case: HxE; Exists y; Move=> // f' Hyf'.
By Case: (leqf_cases f f') => *; [Apply: dd_ideal Hxf | Case Hxy; Exists f'].
Qed.

Section RealSelect.

(* definition by cases *)

Variables P : Prop; x1, x2 : dreal.

Definition selectdr_set [x : dreal] : Prop :=
  IF P then (eqdr x x1) else (eqdr x x2).
Definition selectdr : dreal := (supdr selectdr_set).

Lemma selectdr_cases :
  IF P then (eqdr selectdr x1) else (eqdr selectdr x2).
Proof.
Case: (Hclassical P) => [HP]; [Left | Right]; (Split; LeftDone).
  Step Hsup: (has_supdr0 selectdr_set).
    Case: (dd_lb x1) (dd_ub x1) => [f1 Hf1] [f2 Hf2]; Split.
      Case/dd_open: Hf2 => [f3 Hf23 Hf3]; Exists f2; Exists f3; LeftDone.
      By Move=> x [[_ Dx] | [[]]] //; Rewrite Dx.
    Exists f1; Move=> [f3 Hf13 Hf3]; Case: Hf1; Apply: (dd_ideal (ltfW Hf13)).
    By Apply Hf3; Left; Split.
  Split; Move=> f.
    Case/dd_open=> [f1 Hff1 Hf1]; Left; Split; LeftDone; Exists f1; LeftDone.
    By Move=> x  [[_ Dx] | [[]]] //; Rewrite Dx.
  Case=> [[_ [f1 Hf1f Hf1]] | [[]]] //; Apply: (dd_ideal (ltfW Hf1f)).
  By Apply Hf1; Left; Split.
Step Hsup: (has_supdr0 selectdr_set).
  Case: (dd_lb x2) (dd_ub x2) => [f1 Hf1] [f2 Hf2]; Split.
    Case/dd_open: Hf2 => [f3 Hf23 Hf3]; Exists f2; Exists f3; LeftDone.
    Move=> x [[H _] | [_ Dx]]; Rewrite: ?Dx; Tauto.
  Exists f1; Move=> [f3 Hf13 Hf3]; Case: Hf1; Apply: (dd_ideal (ltfW Hf13)).
  By Apply Hf3; Right; Split.
Split; Move=> f.
  Case/dd_open=> [f1 Hff1 Hf1]; Left; Split; LeftDone; Exists f1; LeftDone.
  Move=> x [[H' _] | [_ Dx]]; Rewrite: ?Dx; Tauto.
Case=> [[_ [f1 Hf1f Hf1]] | [[]]] //; Apply: (dd_ideal (ltfW Hf1f)).
By Apply Hf1; Right; Split.
Qed.

End RealSelect.

Add Morphism selectdr : selectdr_morphism.
Proof.
Move=> P Q x1 y1 x2 y2 DP Dx1 Dx2; Apply: eqdr_sup=> [x3 y3 Dx3].
Rewrite: /selectdr_set /IF DP Dx1 Dx2 Dx3; Tauto.
Qed.

Section RealSign.

(* opposite and absolute value. *)

Variable x : dreal.

(* opposite *)

Definition oppds : ddseg := [f](EX f' | (ltf f' f) & ~(x (oppf f'))).

Lemma ideals_opp : (ideals oppds).
Proof.
By Move=> f1 f2 Hf12 [f3 Hf23 Hf3]; Exists f3; LeftBy Apply: ltf_leq_trans Hf12.
Qed.

Lemma opens_opp : (opens oppds).
Proof.
Move=> f1 [f3 Hf13 Hf3]; Case/frac_dense: Hf13 => [f2 Hf12 Hf23].
By Exists f2; RightBy Exists f3.
Qed.

Lemma hass_opp : (hass oppds).
Proof.
Move: (dd_lb x) => [f1]; Exists (oppf (addf (oppf F1) f1)).
Exists (oppf f1); RightBy Rewrite: /= oppf_opp.
By Rewrite: /ltf leqf_opp2 -{1 f1}addF0 addfC leqf_add2r.
Qed.

Lemma hasNs_opp : (hasNs oppds).
Proof.
Move: (dd_ub x) => [f Hxf]; Exists (oppf f); Move=> [f1 Hff1 []].
By Apply: dd_ideal Hxf; Rewrite: -leqf_opp2 oppf_opp ltfW.
Qed.

Definition oppdr : dreal := (Dreal ideals_opp opens_opp hass_opp hasNs_opp).

(* absolute value *)

Definition absds : ddseg := [f](x f) /\ (oppdr f).

Lemma ideals_abs  : (ideals absds).
Proof.
Move=> f1 f2 Hf12 [Hf1 Hf1'].
By Split; [Apply: dd_ideal Hf1 | Apply: ideals_opp Hf1'].
Qed.

Lemma opens_abs  : (opens absds).
Proof.
Move=> f; Case; Move/dd_open=> [f1 Hff1 Hf1]; Move/opens_opp=> [f2 Hff2 Hf2]. 
Case: (leqf_cases f1 f2) => [Hf12].
  By Exists f2; RightBy Split; LeftBy Apply: dd_ideal Hf1.
By Exists f1; RightBy Split; RightBy Apply: ideals_opp Hf2; Apply ltfW.
Qed.

Lemma hass_abs : (hass absds).
Proof.
Move: (dd_ub x) hass_opp => [f1 Hf1] [f2 Hf2].
Case: (leqf_cases f1 f2) => [Hf12].
  By Exists f2; Split; LeftBy Apply: dd_ideal Hf1.
By Exists f1; Split; RightBy Apply: ideals_opp Hf2; Apply ltfW.
Qed.

Lemma posf_absdr : (f : frac) (absds f) -> (posf f).
Proof.
Move=> f [Hf [f1 Hff1 Hf1]]; Rewrite: -posfI; Apply/idP=> [Hf0]; Case: Hf1.
Apply: dd_ideal Hf; Apply: (leqf_trans Hf0); Rewrite: -oppF0 leqf_opp2.
By Apply: leqf_trans Hf0; Apply ltfW.
Qed.

Lemma hasNs_abs : (hasNs absds).
Proof. By Exists F0; Move; Move/posf_absdr. Qed.

Definition absdr : dreal := (Dreal ideals_abs opens_abs hass_abs hasNs_abs).

End RealSign.

Add Morphism oppdr : oppdr_morphism.
Proof.
Move=> x y Dx; Split; Move=> f [f' Hff' Hf']; 
  By Exists f'; RightBy Move: Hf'; Rewrite: Dx.
Qed.

Add Morphism absdr : absdr_moprphism.
Proof.
Move=> x y Dx; Split; Move=> f; Rewrite: /= /absds Dx; Tauto.
Qed.

Lemma oppdr_opp : (x : dreal) (eqdr (oppdr (oppdr x)) x).
Proof.
Move=> x; Split; Move=> f.
  Move/dd_open=> [f1 Hff1 Hf1]; Exists f1; LeftDone.
  By Move=> [f2 Hf12 []]; Apply: dd_ideal Hf1; Rewrite: -leqf_opp2 oppf_opp ltfW.
Case: (Hclassical (x f)) => [Hf]; LeftDone; Move=> [f1 Hff1 []].
By Exists (oppf f); Rewrite: /ltf ?leqf_opp2 ?oppf_opp.
Qed.

Lemma absdr_opp : (x : dreal) (eqdr (absdr (oppdr x)) (absdr x)).
Proof. Move=> x; Split; Move=> f; Rewrite: /= /absds (oppdr_opp x); Tauto. Qed.

Section RealArith.

Variable x1, x2 : dreal.

Definition addds : ddseg := [f](EX f1 | (x1 f1) & (x2 (addf (oppf f1) f))).

Lemma ideals_add : (ideals addds).
Proof.
Move=> f1 f2 Hf12 [f11 Hf11 Hf1']; Exists f11; LeftDone.
By Apply: dd_ideal Hf1'; Rewrite: leqf_add2l.
Qed.

Lemma opens_add : (opens addds).
Proof.
Move=> f2 [f1 Hf1]; Move/dd_open=> [f3 Hf23 Hf3]; Exists (addf f1 f3).
  By Rewrite: /ltf -(leqf_eql (addf_inv f1 f2)) addfCA leqf_add2l.
By Exists f1; IP; Rewrite: // (eqf_dr x2 (addf_inv f1 f3)).
Qed.

Lemma hass_add : (hass addds).
Proof.
Move: (dd_ub x1) (dd_ub x2) => [f1 Hf1] [f2 Hf2].
Exists (addf f1 f2); Exists f1; Auto; Apply: dd_ideal Hf2.
By Case/andP: (addf_inv f1 f2).
Qed.

Lemma hasNs_add : (hasNs addds).
Proof.
Move: (dd_lb x1) (dd_lb x2) => [f1 Hf1] [f2 Hf2].
Exists (addf f1 f2); Case=> [f3 Hf3 Hf312]; Case: Hf2; Apply: dd_ideal Hf312.
Rewrite: -(leqf_eqr (addf_inv f3 f2)) leqf_add2l leqf_add2r.
By Apply ltfW; Apply/idP=> [Hf13]; Case Hf1; Apply: dd_ideal Hf3.
Qed.

Definition adddr : dreal := (Dreal ideals_add opens_add hass_add hasNs_add).

Definition amulds : ddseg :=
  [f](EX f1 | (absdr x1 f1) & (absdr x2 (mulf (invf f1) f))).

Lemma ideals_amul : (ideals amulds).
Proof.
Move=> f1 f2 Hf12 [f Hx1f Hx2f]; Exists f; LeftDone; Apply: ideals_abs Hx2f.
Rewrite: leqf_pmul2l // posf_inv; Exact (posf_absdr Hx1f).
Qed.

Lemma opens_amul : (opens amulds).
Proof.
Move=> f2 [f1 Hxf1]; Move/dd_open=> [f3 Hf23 Hf3]; Def: Hf1 := (posf_absdr Hxf1).
Exists (mulf f1 f3).
  By Rewrite: /ltf -(leqf_eql (pmulf_inv f2 Hf1)) mulfCA leqf_pmul2l.
By Exists f1; IP; Rewrite: // (eqf_dr (absdr x2) (pmulf_inv f3 Hf1)).
Qed.
 
Lemma hass_amul : (hass amulds).
Proof.
Move: (hass_abs x1) (hass_abs x2) => [f1 Hxf1] [f2 Hxf2].
Def: Hf1 := (posf_absdr Hxf1); Exists (mulf f1 f2); Exists f1; LeftDone.
By Apply: ideals_abs Hxf2; Case/andP: (pmulf_inv f2 Hf1).
Qed.

Lemma hasNs_amul : (hasNs amulds).
Proof.
Exists F0; Case=> [f _]; Move/posf_absdr.
By Rewrite: -posfI /ltf [f'](leqf_eql (mulF0 f')).
Qed.

Definition amuldr : dreal := (Dreal ideals_amul opens_amul hass_amul hasNs_amul).

Definition pos_muldr : Prop := (x1 F0) <-> (x2 F0).

Definition muldr : dreal := (selectdr pos_muldr amuldr (oppdr amuldr)).

End RealArith.

Definition ainvdr [x1 : dreal] : dreal :=
  (supdr [x](amuldr x x1 F1)).

Definition invdr [x1 : dreal] : dreal :=
  (selectdr (x1 F0)  (oppdr (ainvdr x1)) (ainvdr x1)).

Add Morphism adddr : adddr_morphism.
Proof.
Move=> x1 y1 x2 y2 Dx1 Dx2.
By Split; Move=> f [f' Hf1 Hf2]; Exists f'; Move: Hf1 Hf2; Rewrite: ?Dx1 ?Dx2.
Qed.

Add Morphism amuldr : amuldr_morphism.
Proof.
Move=> x1 y1 x2 y2 Dx1 Dx2.
By Split; Move=> f [f' Hf1 Hf2]; Exists f'; Move: Hf1 Hf2; Rewrite: ?Dx1 ?Dx2.
Qed.

Add Morphism pos_muldr : pos_muldr_morphism.
Proof. By Move=> x1 y1 x2 y2 Dx1 Dx2; Rewrite: /pos_muldr Dx1 Dx2. Qed.

Add Morphism muldr : muldr_morphism.
Proof.
Move=> x1 y1 x2 y2 Dx1 Dx2; Split; Move=> f; Rewrite: /muldr Dx1 Dx2; Tauto.
Qed.

Lemma adddrC : (x1, x2 : dreal) (eqdr (adddr x1 x2) (adddr x2 x1)).
Proof.
Cut (x1, x2 : dreal) (leqdr (adddr x2 x1) (adddr x1 x2)); LeftBy Split.
Move=> x1 x2 f [f' Hf' Hf]; Exists (addf (oppf f') f); LeftDone.
Apply: dd_ideal Hf'; Rewrite: oppf_add oppf_opp -addfA addfC -addfA.
By Case/andP: (addf_inv f f').
Qed.

Lemma adddrA : (x1, x2, x3 : dreal)
  (eqdr (adddr x1 (adddr x2 x3)) (adddr (adddr x1 x2) x3)).
Proof.
Cut (x1, x2, x3 : dreal)(leqdr (adddr (adddr x1 x2) x3) (adddr x1 (adddr x2 x3))).
  Split; Auto; Rewrite: (adddrC x1 (adddr x2 x3)) (adddrC (adddr x1 x2) x3).
  Rewrite: (adddrC x1 x2) (adddrC x2 x3); Auto.
Move=> x1 x2 x3 f3 [f1 Hf1 [f2 Hf2 Hf3]].
Exists (addf f1 f2); RightBy Rewrite: oppf_add -addfA addfCA.
By Exists f1; LeftDone; Apply: dd_ideal Hf2; Case/andP: (addf_inv f1 f2).
Qed.

Lemma adddrI : (x : dreal) (eqdr (adddr x (oppdr x)) F0).
Proof.
Move=> x; Apply eqdr_sym; Split; Move=> f.
  Move=> [f1 Hf1 [f2 Hf12 Hf2]]; Apply/idP=> [Hf]; Case: Hf2; Apply: dd_ideal Hf1.
  Rewrite: -leqf_opp2 oppf_opp; Apply: (leqf_trans (ltfW Hf12)).
  By Rewrite: -{2 (oppf f1)}addF0 leqf_add2l.
Rewrite: /= /fracs posfI; Move=> Hf; Pose fn := [n](Frac (0) (Zpos n)).
Step [n Hn]: (EX n | (absdr x (mulf f (fn n)))).
  Case: (hass_abs x) => [f1 Hxf1].
  Case Dn: (mulf (invf f) f1) => [d [n|n]].
    Exists n; Apply: ideals_abs Hxf1.
    Rewrite: -(leqf_eql (pmulf_inv f1 Hf)) mulfCA leqf_pmul2l // ~Dn /fn /=.
    By Rewrite: scalez_pos leqz_nat -{3 n}addn0 iter_f /= leq_addr.
  By Move: (posf_absdr Hxf1); Rewrite: -(!posf_pmull (invf f) f1) ?posf_inv ?Dn.
Elim: n Hn => [|n].
  By Move/posf_absdr; Rewrite: /fn -/F0 -posfI /ltf (leqf_eql (mulF0 f)).
Pose f' := (mulf f (fn n)); Move=> Hrec Hn.
Step Hff': (absdr x (addf f f')).
  By Apply: dd_ideal Hn; Rewrite: -{2 f}mulf1; Case/andP: (mulf_addr f F1 (fn n)).
Case/dd_open: Hff' => [f1 Hff1 [Hf1 Hf1']]; Pose f2 := (addf (oppf f) f1).
Case: (Hclassical (x f')) {Hn Hf} => [Hf'].
  Case: (Hclassical (x (oppf f2))) => [Hf2].
    Exists (oppf f2); LeftDone.
    By IP; Rewrite: oppf_opp addfC /f2 addfCA (eqf_dr (oppdr x) (addf_inv f f1)).
  Apply Hrec; Split; LeftDone.
  By Exists f2; Rewrite: // /ltf -(leqf_eql (addf_inv f f')) /f2 leqf_add2l.
Exists f1; LeftDone; Exists (oppf f'); RightBy Rewrite: oppf_opp.
Rewrite: /ltf -{f}oppf_opp -oppf_add leqf_opp2 addfC.
By Rewrite: -(leqf_eql (addf_inv f f')) leqf_add2l.
Qed.

Lemma add0dr : (x : dreal) (eqdr (adddr F0 x) x).
Proof.
Move=> x; Split; Move=> f.
  Move/dd_open=> [f1 Hf1 Hxf1]; Exists (addf (oppf f1) f).
    By Rewrite: /= /fracs /ltf -(leqf_eqr (addf_inv f1 F0)) addF0 leqf_add2l.
  By IP; Rewrite: oppf_add oppf_opp -addfA addfC -addfA (eqf_dr x (addf_inv f f1)).
Move=> [f1 Hf1]; Apply: dd_ideal; Rewrite: -{2 f}addF0 addfC leqf_add2l.
By Rewrite: -oppF0 leqf_opp2 ltfW.
Qed.

Lemma oppdr_add : (x1, x2 : dreal)
  (eqdr (oppdr (adddr x1 x2)) (adddr (oppdr x1) (oppdr x2))).
Proof.
Move=> x1 x2; Pose y1 := (oppdr x1); Pose y2 := (oppdr x2).
Pose y := (oppdr (adddr x1 x2)); Rewrite: -(add0dr (adddr y1 y2)) -(adddrI y).
Rewrite: -(adddrA y (oppdr y) (adddr y1 y2)) (adddrA (oppdr y) y1 y2).
Rewrite: {3}/y (oppdr_opp (adddr x1 x2)) (adddrC x1 x2) -(adddrA x2 x1 y1).
Rewrite: /y1 (adddrI x1) (adddrC x2 F0) (add0dr x2) /y2 (adddrI x2).
By Rewrite: (adddrC y F0) (add0dr y).
Qed.

Lemma adddr_monotony : (x1, x2, x3 : dreal)
  (leqdr x2 x3) -> (leqdr (adddr x1 x2) (adddr x1 x3)).
Proof. Move=> x1 x2 x3 Hx12 f2 [f1 Hf1 Hf2]; Exists f1; Auto. Qed.

Lemma amuldrC : (x1, x2 : dreal) (eqdr (amuldr x1 x2) (amuldr x2 x1)).
Proof.
Cut (x1, x2 : dreal) (leqdr (amuldr x2 x1) (amuldr x1 x2)); LeftBy Split.
Move=> x1 x2 f [f' Hf' Hf]; Exists (mulf (invf f') f); LeftDone.
Apply: dd_ideal {}Hf'; Move/posf_absdr: Hf => Hf.
Rewrite: -(leqf_pmul2l Hf) mulfCA (leqf_eqr (pmulf_inv f Hf)).
By Rewrite: mulfC mulfCA; Case/andP: (pmulf_inv f (posf_absdr Hf')).
Qed.

Lemma pos_muldrC : (x1, x2 : dreal) (pos_muldr x1 x2) <-> (pos_muldr x2 x1).
Proof. By Split; Case; Split. Qed.

Lemma muldrC : (x1, x2 : dreal) (eqdr (muldr x1 x2) (muldr x2 x1)).
Proof.
By Move=> x1 x2; Rewrite: /muldr (pos_muldrC x1 x2) (amuldrC x1 x2).
Qed.

Lemma amuldr_opp : (x1, x2 : dreal) (eqdr (amuldr (oppdr x1) x2) (amuldr x1 x2)).
Proof.
Cut (x1, x2 : dreal) (leqdr (amuldr x1 x2) (amuldr (oppdr x1) x2)). 
  Move=> Hrec x1 x2; Split; RightDone; Move=> f Hf.
  By Apply Hrec; Rewrite: (oppdr_opp x1).
By Move=> x1 x2 f [f' Hf' Hf]; Exists f'; Rewrite: // -(absdr_opp x1).
Qed.

Lemma pos_absdr : (x : dreal) ~(x F0) -> (eqdr (absdr x) x).
Proof.
Move=> x Hx; Split; Move=> f Hf; RightBy Case Hf.
Split; LeftDone; Exists F0; RightDone.
By Apply/idP=> [Hf0]; Case: Hx; Apply: dd_ideal Hf.
Qed.

Lemma oppdr0 : (eqdr (oppdr F0) F0).
Proof. By Pose f0 := (oppdr F0); Rewrite: -(adddrI F0) -/f0 (add0dr f0). Qed.

Lemma leqdr_opp2 : (x1, x2 : dreal)
 (leqdr x1 x2) -> (leqdr (oppdr x2) (oppdr x1)).
Proof. Move=> x1 x2 Hx12 f1 [f2 Hf12 Hf2]; Exists f2; Auto. Qed.

Lemma pos_leqdr : (x : dreal) ~(x F0) -> (leqdr F0 x).
Proof. By Move=> x Hx f Hxf; Apply/idP=> [Hf]; Case: Hx; Apply: dd_ideal Hxf. Qed.

Lemma pos_oppdr1 : (x : dreal) (x F0) -> ~(oppdr x F0).
Proof.
By Move=> x Hx [f Hf []]; Apply: dd_ideal Hx; Rewrite: -oppF0 leqf_opp2 ltfW.
Qed.

Lemma pos_oppdr2 : (x : dreal) ~(x F0) -> ~(oppdr x F0) -> (eqdr x F0).
Proof.
Move: {}pos_leqdr; Split; Auto.
Rewrite: -(oppdr_opp x) -oppdr0; Apply leqdr_opp2; Auto.
Qed.

Lemma pos_amuldr : (x1, x2 : dreal) ~(amuldr x1 x2 F0).
Proof.
Move=> x1 x2; Case=> [f _]; Move/posf_absdr; Rewrite: -posfI; Case/idP.
By Case/andP: (mulF0 (invf f)).
Qed.

Lemma oppdr_cases : (P : dreal -> Prop)
  ((x : dreal) (P (oppdr x)) -> (P x)) ->
  ((x : dreal) ~(x F0) -> (P x)) ->
  (x : dreal) (P x).
Proof. Move=> P Hopp H0 x; Case: (Hclassical (x F0)) {}pos_oppdr1; Auto. Qed.

Lemma amul0dr : (x : dreal) (eqdr (amuldr F0 x) F0).
Proof.
Move=> x; Split; Move=> f; RightBy Apply pos_leqdr; Apply pos_amuldr.
Case: (dd_ub (absdr x)) => [f1 Hxf1] Hf; Def: Hf1 := (posf_absdr Hxf1).
Pose f2 := (mulf (invf f1) f).
Step Hf2: (posf f2) By Rewrite: /f2 posf_pmull ?posf_inv // -posfI.
Exists f2; LeftBy Rewrite: /= /absds oppdr0; Rewrite: -posfI in Hf2; Split.
Apply: dd_ideal Hxf1; Rewrite: -(leqf_eql (pmulf_inv f1 Hf2)).
Rewrite: leqf_pmul2l ?posf_inv // /f2 mulfC mulfCA.
By Case/andP: (pmulf_inv f Hf1).
Qed.

Lemma muldr_oppl : (x1, x2 : dreal)
  (eqdr (muldr (oppdr x1) x2) (oppdr (muldr x1 x2))).
Proof.
Move=> x1 x2; Elim/oppdr_cases: x1 => [x1 Hx1].
  By Rewrite: -(oppdr_opp (muldr (oppdr x1) x2)) -Hx1 (oppdr_opp x1).
Rewrite: /muldr (amuldr_opp x1 x2); Pose y := (amuldr x1 x2).
Case: (selectdr_cases (pos_muldr x1 x2) y (oppdr y)) => [[Hx12 Dy]];
  Case: (selectdr_cases (pos_muldr (oppdr x1) x2) y (oppdr y)) => [[Hx21 Dy']];
  Rewrite: Dy Dy' ?(oppdr_opp y) //; Rewrite: /pos_muldr /= -/F0 in Hx12 Hx21.
  Step Dx1: (eqdr x1 F0) By Apply: pos_oppdr2; Rewrite: //= Hx21 -Hx12.
  By Rewrite: /y Dx1 (amul0dr x2) oppdr0.
Step Dx1: (eqdr x1 F0) By Apply: pos_oppdr2 => // [Hx1']; Case: Hx12; Tauto.
By Rewrite: /y Dx1 (amul0dr x2) oppdr0.
Qed.

Lemma muldr_oppr : (x1, x2 : dreal)
  (eqdr (muldr x1 (oppdr x2)) (oppdr (muldr x1 x2))).
Proof.
By Move=> x1 x2; Rewrite: (muldrC x1 (oppdr x2)) (muldr_oppl x2 x1) (muldrC x2 x1).
Qed.

Lemma absdr_amul : (x1, x2 : dreal) (eqdr (absdr (amuldr x1 x2)) (amuldr x1 x2)).
Proof.
Move=> x1 x2; Split; Move=> f Hf; RightBy Case Hf.
Split; LeftDone; Case/dd_open: Hf=> [f' Hff' Hf']; Exists f'; LeftDone.
Move=> [f1]; Move/posf_absdr=> Hf1; Move/posf_absdr.
Rewrite: posf_pmull ?posf_inv // posf_opp nnegf_0Vpos; Case/orP; Right.
Case: Hf' => [f2]; Move/posf_absdr=> Hf2; Move/posf_absdr.
By Rewrite: posf_pmull ?posf_inv.
Qed.

Lemma amuldrA : (x1, x2, x3 : dreal)
  (eqdr (amuldr x1 (amuldr x2 x3)) (amuldr (amuldr x1 x2) x3)).
Proof.
Cut (x1, x2, x3 : ?) (leqdr (amuldr (amuldr x1 x2) x3) (amuldr x1 (amuldr x2 x3))).
  Move=> Hrec x1 x2 x3; Split; RightDone.
  Rewrite: (amuldrC (amuldr x1 x2) x3) (amuldrC x1 (amuldr x2 x3)).
  By Rewrite: (amuldrC x2 x3) (amuldrC x1 x2).
Move=> x1 x2 x3 f3 [f1 Hf1 [[f2 Hf2 Hf3] _]]; Exists (mulf f1 f2).
  IP; Rewrite: (absdr_amul x1 x2); Exists f1; LeftDone.
  By Apply: ideals_abs Hf2; Case/andP: (pmulf_inv f2 (posf_absdr Hf1)).
Move/posf_absdr: Hf1 => Hf1; Move/posf_absdr: Hf2 => Hf2.
Apply: ideals_abs Hf3; Rewrite: -(leqf_pmul2l Hf2) mulfCA.
Rewrite: [f'](leqf_eql (pmulf_inv f' Hf2)) -(leqf_pmul2l Hf1) mulfCA.
Rewrite: (leqf_eql (pmulf_inv f3 Hf1)) mulfA mulfCA.
By Rewrite: -(posf_pmull f2 Hf1) in Hf2; Case/andP: (pmulf_inv f3 Hf2).
Qed.

Lemma eqdr_opp2 : (x1, x2 : dreal) (eqdr (oppdr x1) (oppdr x2)) -> (eqdr x1 x2).
Proof. Move=> x1 x2 Hx12; Rewrite: -(oppdr_opp x1) Hx12; Apply oppdr_opp. Qed.

Lemma pos_muldr2 : (x1, x2 : dreal) ~(x1 F0) -> ~(x2 F0) ->
  (eqdr (muldr x1 x2) (amuldr x1 x2)).
Proof.
Move=> x1 x2 Hx1 Hx2; Rewrite: /muldr; Move: (amuldr x1 x2) => y.
Case: (selectdr_cases (pos_muldr x1 x2) y (oppdr y)) => [[_ Dy] | [[]]] //.
Split; Tauto.
Qed.

Lemma muldrA : (x1, x2, x3 : dreal)
  (eqdr (muldr x1 (muldr x2 x3)) (muldr (muldr x1 x2) x3)).
Proof.
Elim/oppdr_cases=> [x1 Hx1] x2 x3.
  Apply eqdr_opp2; Rewrite: -(muldr_oppl x1 (muldr x2 x3)).
  By Rewrite: -(muldr_oppl (muldr x1 x2) x3) -(muldr_oppl x1 x2).
Elim/oppdr_cases: x2 => [x2 Hx2].
  Apply eqdr_opp2; Rewrite: -(muldr_oppr x1 (muldr x2 x3)).
  Rewrite: -(muldr_oppl (muldr x1 x2) x3) -(muldr_oppr x1 x2).
  By Rewrite: -(muldr_oppl x2 x3).
Elim/oppdr_cases: x3 => [x3 Hx3].
  Apply eqdr_opp2;  Rewrite: -(muldr_oppr x1 (muldr x2 x3)).
  By Rewrite: -(muldr_oppr (muldr x1 x2) x3) -(muldr_oppr x2 x3).
Rewrite: (pos_muldr2 Hx2 Hx3) (pos_muldr2 Hx1 (!pos_amuldr x2 x3)).
Rewrite: (pos_muldr2 Hx1 Hx2) (pos_muldr2 (!pos_amuldr x1 x2) Hx3); Apply amuldrA.
Qed.

Lemma muldr_addr : (x1, x2, x3 : dreal)
  (eqdr (muldr x1 (adddr x2 x3)) (adddr (muldr x1 x2) (muldr x1 x3))).
Proof.
Move=> x1 x2 x3; Pose x := (adddr x2 x3); Elim/oppdr_cases: x1 => [x1 Hx1].
  Rewrite: -(oppdr_opp x1); Pose y1 := (oppdr x1).
  Rewrite: (muldr_oppl y1 x) (muldr_oppl y1 x2) (muldr_oppl y1 x3).
  Rewrite: /y1 ~Hx1; Apply oppdr_add.
Step Dx: (eqdr x (adddr x2 x3)) By Done.
ClearBody x; Elim/oppdr_cases: x x2 x3 Dx => [x Hx] x2 x3 Dx.
  Step Dnx: (eqdr (oppdr x) (adddr (oppdr x2) (oppdr x3))).
    Rewrite Dx; Apply oppdr_add.
  Rewrite: -(oppdr_opp x) (muldr_oppr x1 (oppdr x)) (Hx ? ? Dnx).
  Rewrite: (muldr_oppr x1 x2) (muldr_oppr x1 x3).
  Rewrite: -(oppdr_add (muldr x1 x2) (muldr x1 x3)); Apply oppdr_opp.
Move: Hx; Rewrite: ~{x}Dx; Move: x2 x3.
Cut (x2, x3 : dreal) ~(x2 F0) -> ~(x3 F0) ->
  (eqdr (muldr x1 (adddr x2 x3)) (adddr (muldr x1 x2) (muldr x1 x3))).
  Move=> Hrec; Cut (x2, x3 : dreal) (x2 F0) -> ~(adddr x2 x3 F0) ->
      (eqdr (muldr x1 (adddr x2 x3)) (adddr (muldr x1 x2) (muldr x1 x3))).
    Move=> Hneg x2 x3; Case (Hclassical (x3 F0)); Case (Hclassical (x2 F0)); EAuto.
    Move=> Hx2 Hx3; Rewrite: (adddrC (muldr x1 x2) (muldr x1 x3)) (adddrC x2 x3).
    EAuto.
  Move=> x2 x3; Pose x := (adddr x2 x3); Move/pos_oppdr1=> Hx2 Hx.
  Rewrite: -(add0dr x3) -(adddrI x2) (adddrC x2 (oppdr x2)).
  Rewrite: -(adddrA (oppdr x2) x2 x3) -/x (Hrec ? ? Hx2 Hx) (muldr_oppr x1 x2).
  Move: (muldr x1 x2) (muldr x1 x) => y2 y.
  By Rewrite: (adddrA y2 (oppdr y2) y) (adddrI y2) (add0dr y).
Move=> x2 x3 Hx2 Hx3; Step Hx23: ~(adddr x2 x3 F0).
  Move=> [f1 Hx2f1 Hx3f1]; Case: Hx3; Apply: dd_ideal Hx3f1.
  Rewrite: addF0 -oppF0 leqf_opp2; Apply ltfW; Apply/idP=> [Hf1].
  By Case: Hx2; Apply: dd_ideal Hx2f1.
Rewrite: (pos_muldr2 Hx1 Hx23) (pos_muldr2 Hx1 Hx2) (pos_muldr2 Hx1 Hx3).
Apply eqdr_sym; Split; Move=> f.
  Case=> [f1]; Rewrite: (pos_absdr Hx23); Move=> Hxf1 [f2 Hf2 Hf3].
  Def: Hf1 := (posf_absdr Hxf1); Exists (mulf f1 f2).
    By Exists f1; IP; Rewrite: // (pos_absdr Hx2) (eqf_dr x2 (pmulf_inv f2 Hf1)).
  Exists f1; Rewrite: // (pos_absdr Hx3); Apply: dd_ideal Hf3.
  Rewrite: (leqf_eqr (mulf_addr (invf f1) (oppf (mulf f1 f2)) f)) leqf_add2r.
  By Rewrite: -mulf_oppr; Case/andP: (pmulf_inv (oppf f2) Hf1).
Case=> [f2]; Case=> [f12]; Rewrite: (pos_absdr Hx2); Move=> Hxf12 Hxf2.
Case=> [f13]; Rewrite: (pos_absdr Hx3); Move=> Hxf13 Hxf3.
Step [f1 Hxf1 [Hf12 Hf13]]:
   (EX f1 | (absdr x1 f1) & (leqf f1 f12) /\ (leqf f1 f13)).
  Case: (leqf_cases f12 f13) => [Hf123].
    By Exists f12; RightBy Split; LeftBy Apply leqff.
  By Exists f13; RightBy Split; [Apply ltfW | Apply leqff].
Exists f1; LeftDone; Rewrite: (pos_absdr Hx23); Def: Hf1 := (posf_absdr Hxf1).
Exists (mulf (invf f1) f2).
  Def: Hf120 := (posf_absdr Hxf12); Step Hf2: (posf f2).
    Move: Hxf2; Rewrite: -(pos_absdr Hx2); Move/posf_absdr.
    By Rewrite: posf_pmull ?posf_inv. 
  Apply: dd_ideal Hxf2; Rewrite: -(leqf_pmul2l Hf120) mulfCA.
  Rewrite: (leqf_eql (pmulf_inv f2 Hf120)) -(leqf_pmul2l Hf1) !mulfA -!(mulfC f2).
  By Rewrite: (leqf_pmul2l Hf2) mulfC (leqf_eqr (pmulf_inv f12 Hf1)).
Apply: dd_ideal {}Hxf3; Move: Hxf3; Rewrite: -(pos_absdr Hx3); Move/posf_absdr.
Rewrite: -mulf_oppr -(leqf_eqr (mulf_addr (invf f1) (oppf f2) f)).
Move: (addf (oppf f2) f) => f3 Hf3'; Def: Hf130 := (posf_absdr Hxf13).
Step Hf3: (posf f3) By Move: Hf3'; Rewrite: posf_pmull ?posf_inv.
Rewrite: -(leqf_pmul2l Hf130) mulfCA.
Rewrite: (leqf_eql (pmulf_inv f3 Hf130)) -(leqf_pmul2l Hf1) !mulfA -!(mulfC f3).
By Rewrite: (leqf_pmul2l Hf3) mulfC (leqf_eqr (pmulf_inv f13 Hf1)).
Qed.

Lemma mul1dr : (x : dreal) (eqdr (muldr F1 x) x).
Proof.
Elim/oppdr_cases=> [x Hx]; LeftBy Apply eqdr_opp2; Rewrite: -Hx (muldr_oppr F1 x).
Step HpF1: ~(fracdr F1 F0) By Done.
Rewrite: (pos_muldr2 HpF1 Hx); Split; Move=> f.
  Move/dd_open=> [f1 Hff1 Hx1]; Rewrite: (amuldrC F1 x).
  Exists f1; LeftBy Rewrite: (pos_absdr Hx).
  Step Hf1: (posf f1) By Move: Hx1; Rewrite: -(pos_absdr Hx); Apply: (!posf_absdr).
  Rewrite: (pos_absdr HpF1) /= /fracs /ltf -(leqf_eqr (pmulf_inv F1 Hf1)).
  By Rewrite: mulf1 leqf_pmul2l ?posf_inv.
Case=> [f1 Hxf1 Hxf]; Move: {}Hxf; Rewrite: (pos_absdr Hx); Apply: dd_ideal.
Rewrite: -(leqf_eqr (pmulf_inv f (posf_absdr Hxf1))) mulfCA.
Move: (mulf (invf f1) f) (posf_absdr Hxf) Hxf1 => y Hy.
Rewrite: (pos_absdr HpF1) mulfC -{1 y}mulf1 leqf_pmul2l //; Apply: (!ltfW).
Qed.

Lemma muldr_monotony : (x, x1, x2 : dreal)
  (leqdr F0 x) -> (leqdr x1 x2) -> (leqdr (muldr x x1) (muldr x x2)).
Proof.
Move=> /= x x1 x2 Hx Hx12; Pose y1 := (muldr x x1); Pose y2 := (muldr x x2).
Rewrite: -(add0dr y2) -(adddrI y1) -(adddrA y1 (oppdr y1) y2) {-1}/y1 -(add0dr y1).
Rewrite: -(muldr_oppr x x1) -/y1 (adddrC F0 y1); Apply adddr_monotony.
Move: (adddr_monotony 1!(oppdr x1) Hx12) {y1 Hx12}.
Rewrite: ~/y2 -(muldr_addr x (oppdr x1) x2) (adddrC (oppdr x1) x1) (adddrI x1).
Move: {x1 x2}(adddr (oppdr x1) x2) => y Hy.
Step Hp0: (z : dreal) (leqdr F0 z) -> ~(z F0).
  By Move=> z Hz Hz0; Move: (Hz ? Hz0); Rewrite: /= /fracs ltff.
Rewrite: (pos_muldr2 (Hp0 ? Hx) (Hp0 ? Hy)); Apply pos_leqdr; Apply pos_amuldr.
Qed.

Lemma invdr_opp : (x : dreal) (eqdr (invdr (oppdr x)) (oppdr (invdr x))).
Proof.
Move=> x; Rewrite: /invdr; Pose y := (ainvdr x).
Step Dy': (eqdr (ainvdr (oppdr x)) y).
  Apply: eqdr_sup {y} => [y z Dy].
  Rewrite: (amuldrC y (oppdr x)) (amuldr_opp x y) (amuldrC x y) Dy; Tauto.
Rewrite: ~Dy'; Case: (selectdr_cases (x F0) (oppdr y) y) => [[Hx Ey]];
             Case: (selectdr_cases (oppdr x F0) (oppdr y) y) => [[Hx' Ey']];
  Rewrite: ~Ey ~Ey' ?(oppdr_opp y) //; Try By Case/pos_oppdr1: Hx.
Cut (eqdr y F0); LeftBy Move=> Dy; Rewrite: Dy oppdr0.
Cut ~(has_supdr0 [z](amuldr z x F1)).
  Move{Hx Hx'}=> Hx; Split; Move=> f; Rewrite: /y /ainvdr /= /supds /IF; Tauto.
Move=> [[f [f' Hff' Hf']] _]; Case/idP: Hff'; Apply ltfW; Apply (Hf' f).
By Rewrite: (amuldrC f x) (pos_oppdr2 Hx Hx') (amul0dr f).
Qed.

Lemma muldrI : (x : dreal) ~(eqdr x F0) -> (eqdr (muldr x (invdr x)) F1).
Proof.
Rewrite: /eqr /=; Elim/oppdr_cases=> [x Hx] Hx0;
  Rewrite: -/(eqdr (muldr x (invdr x)) F1).
  Rewrite:  -(oppdr_opp (invdr x)) -(invdr_opp x) (muldr_oppr x (invdr (oppdr x))).
  Rewrite: -(muldr_oppl x (invdr (oppdr x))); Apply: Hx {Hx} => [Hx'].
  By Case: Hx0; Apply: eqdr_opp2; Rewrite: oppdr0.
Rewrite: /invdr; Pose y := (ainvdr x).
Case: (selectdr_cases (x F0) (oppdr y) y) => [[Hx' _] | [_ Dy]]; LeftBy Case Hx.
Rewrite: Dy; Case: (Hclassical (EX f | (posf f) & ~(x f)));
  RightBy Move=> Hx'; Case: Hx0; Apply: (pos_oppdr2 Hx)=> [[f Hf Hxf]];
  Case: Hx'; Exists (oppf f); LeftBy Rewrite: posf_opp -nnegfI.
Move=> [f0 Hf0 Hxf0]; Pose aix := [z](amuldr z x F1).
Step Haix0: (aix F0) By Rewrite: /aix (amul0dr x).
Step Haix: (has_supdr aix).
  Split; LeftBy Exists (F0 :: dreal).
  Exists ((invf f0) :: dreal); Move=> x'; Rewrite: /aix (amuldrC x' x).
  Move=> [f Hxf]; Def: Hf := (posf_absdr Hxf).
  Move=> [H _] f' Hf'; Apply: dd_ideal H; Move/ltfW: Hf'; Apply: leqf_trans.
  Rewrite: mulf1 -(leqf_pmul2l Hf) -(leqf_pmul2l Hf0) mulfC -mulfA mulfCA.
  Rewrite: (leqf_eql (pmulf_inv f0 Hf)) (mulfC f) mulfCA.
  Rewrite: (leqf_eqr (pmulf_inv f Hf0)); Apply ltfW; Apply/idP=> [Hff0].
  By Case: Hxf0; Case: Hxf => [H _]; Apply: dd_ideal H.
Step Hyub: (ubdr aix y) By Apply: ubdr_sup.
Step Hysup: (z : dreal) (ubdr aix z) -> (leqdr y z).
  By Move=> z Hz; Apply: leqdr_sup_ub.
Step Hy0: ~(y F0).
  By Move/dd_open=> [f' Hf'0 Hyf']; Case/idP: (Hyub ? Haix0 ? Hyf'); Apply ltfW.
Rewrite: (pos_muldr2 Hx Hy0); Split; Move=> f.
  Move=> Hf; Step Hpf: (posf f) By Rewrite: -posfI; Apply: leqf_lt_trans Hf.
  Pose e := (addf F1 (oppf (invf f))); Step He: (posf e).
    Rewrite: -posfI /ltf /e addfC -(leqf_eqr (addf_inv (invf f) F0)) leqf_add2l.
    Rewrite: addF0 -{(invf f)}mulf1 -(leqf_pmul2l Hpf) mulf1 mulfCA.
    By Rewrite: (leqf_eqr (pmulf_inv F1 Hpf)).
  Pose e0 := (mulf e f0).
  Cut (fracdr F0 e0); RightBy Rewrite: /= /fracs posfI /e0 posf_pmull.  
  Rewrite: -(adddrI x); Move=> [f1 Hxf1 [f2 Hf12 Hxf2]].
  Step Hf10: (ltf f0 f1) By Apply/idP=> [Hf10]; Case: Hxf0; Apply: dd_ideal Hxf1.
  Exists f1; LeftBy IP; Rewrite: (pos_absdr Hx).
  Step Hf1: (posf f1).
    By Move: Hf0 (ltfW Hf10); Rewrite: -!posfI; Apply: (!ltf_leq_trans).
  Step Hf2: (posf (oppf f2)).
    Rewrite: posf_opp -nnegfI; Apply: (ltf_leq_trans Hf12).
    Rewrite: -(leqf_eqr (addf_inv f1 F0)) addF0 leqf_add2l.
    Apply: leqf_trans (ltfW Hf10); Rewrite: -{f0}addF0 /e0 mulfC.
    Rewrite: /e (leqf_eql (mulf_addr f0 F1 (oppf (invf f)))) mulf1 leqf_add2l.
    Rewrite: mulf_oppr -oppF0 leqf_opp2; Apply ltfW.
    By Rewrite: posfI posf_pmull ?posf_inv.
  Cut (ubdr aix (invf (oppf f2))).
    Rewrite: (pos_absdr Hy0); Move/(Hysup ?)=> H; Apply: H {H}.
    Rewrite: /= /fracs /ltf -(leqf_pmul2l Hf1) mulfCA (leqf_eql (pmulf_inv f Hf1)).
    Rewrite: mulfC -(leqf_eql (pmulf_inv f Hf2)) leqf_pmul2l ?posf_inv //.
    Rewrite: mulfC -(leqf_eqr (pmulf_inv f1 Hpf)) mulfCA leqf_pmul2l ?posf_inv //.
    Rewrite: -leqf_opp2 oppf_opp -mulf_oppl mulfC; Apply: (ltf_leq_trans Hf12).
    Rewrite: -(leqf_add2l f1) addfCA (leqf_eql (addf_inv f1 e0)).
    Rewrite: -{1 f1}mulf1 -(leqf_eqr (mulf_addr f1 F1 (oppf (invf f)))) -/e.
    By Rewrite: mulfC /e0 leqf_pmul2l // ltfW.
  Move=> z; Rewrite: /aix (amuldrC z x); Move=> [f3 Hxf3 [Hf3 _]] f4 Hf4.
  Apply: dd_ideal Hf3; Move/ltfW: Hf4; Apply: leqf_trans {f4}.
  Def: Hf3 := (posf_absdr Hxf3); Rewrite: -(leqf_pmul2l Hf3) mulfCA.
  Rewrite: (leqf_eql (pmulf_inv F1 Hf3)) mulfC -(leqf_eql (pmulf_inv F1 Hf2)).
  Rewrite: mulf1 leqf_pmul2l ?posf_inv //; Apply ltfW; Apply/idP=> [Hf23].
  By Case: Hxf2; Apply: (dd_ideal Hf23); Case: Hxf3.
Move=> [f1 Hxf1]; Pose f2 := (mulf (invf f1) f); Move=> Hyf2; Apply/idP=> [Hf].
Def: Hf1 := (posf_absdr Hxf1); Cut (aix f2).
  Case: Hyf2 => [Hyf2 _] Hxf2; Case/idP: (Hyub ? Hxf2 ? Hyf2); Apply leqff.
Rewrite: /aix (amuldrC f2 x); Move/dd_open: Hxf1 => [f3 Hf13 Hxf3].
Def: Hf2 := (posf_absdr Hyf2); Def: Hf3 := (posf_absdr Hxf3).
Step Hf20: ~(f2 F0) By Case/idP; Apply ltfW; Rewrite posfI. 
Exists f3; LeftDone; Rewrite: (pos_absdr Hf20) /= /fracs /ltf.
Rewrite: -(leqf_pmul2l Hf3) mulfCA (leqf_eql (pmulf_inv F1 Hf3)).
Apply: ltf_leq_trans Hf; Rewrite: /ltf -(leqf_eql (pmulf_inv f Hf1)) mulfCA -/f2.
By Rewrite: -!(mulfC f2) leqf_pmul2l.
Qed.

Theorem dedekind_reals : real_model.
Proof.
Apply: (RealModel (!RealAxioms (RealStructure ? ? ? ? ? ? ? ?)
         leqdrr leqdr_trans ubdr_sup supdr_total
         adddr_monotony adddrC adddrA add0dr adddrI
         muldr_monotony muldrC muldrA muldr_addr mul1dr muldrI ?)) => /=.
By Case=> [H _]; Move: (H (invf F2) (erefl ?)).
Qed.

End DedekindReals.
          
Unset Implicit Arguments.


 
