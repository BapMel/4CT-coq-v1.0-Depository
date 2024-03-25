(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require tacticext.
Require boolprop.
Require funs.
Require dataset.
Require natprop.
Require znat.
Require frac.
Require real.
Require realsyntax.
Require Setoid.

Set Implicit Arguments.

Section RealOperations.

(**********************************************************) 
(**  Derived real operations:                             *)
(*     definition by nondeterministic/deterministiccases, *)
(*     min, max                                           *)
(*     injections from Z, and Q into R                    *)
(*     floor, range1r (unit interval)                     *)
(**********************************************************)

Variable R : real_structure.

Definition pickr_set [P1, P2 : Prop; x1, x2, y : R] : Prop :=
  P1 /\ `y = x1` \/ P2 /\ `y = x2`.

Definition pickr [P1, P2 : Prop; x1, x2 : R] : R := (supr (pickr_set P1 P2 x1 x2)).

Definition selr [P : Prop] : R -> R -> R := (pickr P ~P).

Definition minr [x1, x2 : R] : R := (pickr `x1 <= x2` `x2 <= x1` x1 x2).

Definition maxr [x1, x2 : R] : R := (pickr `x1 <= x2` `x2 <= x1` x2 x1).

Coercion Local natR := (natr R).

Definition znatr [m : znat] : R :=
  Cases m of (Zpos n) => (n :: R) | (Zneg n) => `-(S n)` end.

Coercion Local znatr : znat >-> real_carrier.

Definition fracr [f : frac] : R := let (d, m) = f in `m / (S d)`.

Inductive floor_set [x : R] : R -> Prop :=
  FloorSet : (m : znat) `m <= x` -> (floor_set x m).

Definition floor [x : R] : R := (supr (floor_set x)).

Definition range1r [x, y : R] : Prop := `x <= y` /\ `y < x + 1`.

End RealOperations.

Section RealLemmas.

(* Basic arithmetic/order/setoid lemmas for real numbers.    *)
(* The local definitions below need to be included verbatim  *)
(* by clients of this module, along with all the setoid      *)
(* declaration, in order to make setoid rewriting usable.    *)
(* Note that the sup and inverse operators are not morphisms *)
(* because of the undefined cases.                           *)
(*   Most of the lemmas here do not depend explicitly on     *)
(* classical reasoning; to underscore this we only prove the *)
(* excluded middle at the very end of this section, when it  *)
(* is needed to prove, e.g., the archimedean property.       *)

Variable R : real_model.

(* patch for v7.3.1 Setoid Prop rewrite at root bug *)
Local xProp [P : Prop] : Prop := P.
Remark xPropE : (P : Prop) (xProp P) -> P. Proof. Done. Qed.
Add Morphism xProp : dedekind_xProp_morphism. Proof. Tauto. Qed.
Tactic Definition IP := Apply xPropE.

Local RR : Type := R.
Local isR [x : RR] : RR := x.
Local eqR : RR -> RR -> Prop := (!eqr ?).
Local leqR : RR -> RR -> Prop := (locked (!leqr ?)).
Local addR : RR -> RR -> RR := (locked (!addr ?)).
Local oppR : RR -> RR := (locked (!oppr ?)).
Local mulR : RR -> RR -> RR := (locked (!mulr ?)).
Local selR : Prop -> RR -> RR -> RR := (locked (!selr ?)).
Local minR : RR -> RR -> RR := (locked (!minr ?)).
Local maxR : RR -> RR -> RR := (locked (!maxr ?)).
Local floorR : RR -> RR := (locked (!floor ?)).
Local range1R : RR -> RR -> Prop := (!range1r ?).
Coercion Local natR := (natr R).
Coercion Local znatR := (znatr R).
Coercion Local fracR := (fracr R).

Remark rwR : (x1, x2 : R) `x1 = x2` -> (eqR (isR x1) (isR x2)).
Proof. Done. Qed. 

Remark leqRI : (x1, x2 : R) `x1 <= x2` == (leqR (isR x1) (isR x2)).
Proof. By Unlock leqR. Qed.

Remark eqRI : (x1, x2 : R) `x1 = x2` == (eqR (isR x1) (isR x2)).
Proof. By Unlock eqR. Qed.

Remark addRI : (x1, x2 : R) `x1 + x2` == (addR (isR x1) (isR x2)).
Proof. By Unlock addR. Qed.

Remark oppRI : (x : R) `-x` == (oppR (isR x)).
Proof. By Unlock oppR. Qed.

Remark mulRI : (x1, x2 : R) `x1 * x2` == (mulR (isR x1) (isR x2)).
Proof. By Unlock mulR. Qed.

Remark selRI : (P : Prop; x1, x2 : R) (selr P x1 x2) == (selR P (isR x1) (isR x2)).
Proof. By Unlock selR. Qed.

Remark minRI : (x1, x2 : R) (minr x1 x2) == (minR (isR x1) (isR x2)).
Proof. By Unlock minR. Qed.

Remark maxRI : (x1, x2 : R) (maxr x1 x2) == (maxR (isR x1) (isR x2)).
Proof. By Unlock maxR. Qed.

Remark floorRI : (x : R) (floor x) == (floorR (isR x)).
Proof. By Unlock floorR. Qed.

Remark range1RI : (x : R) (range1r x) == (range1R (isR x)).
Proof. By Unlock range1R. Qed.

(*********************************************************)
(**     Comparisons and the least upper bound axioms     *)
(*********************************************************)

Lemma eqr_leq2 : (x1, x2 : R) `x1 = x2` <-> `x1 <= x2` /\ `x2 <= x1`.
Proof. By Split. Qed.

Lemma eqr_leq : (x1, x2 : R) `x1 = x2` -> `x1 <= x2`.
Proof. By Move=> x1 x2 [Hx12 _]. Qed.

Lemma ltr_neq : (x1, x2 : R) `x1 < x2` -> `x1 <> x2`.
Proof. Rewrite: /eqr; Tauto. Qed.

Lemma gtr_neq : (x1, x2 : R) `x1 > x2` -> `x1 <> x2`.
Proof. Rewrite: /eqr; Tauto. Qed.

Lemma leqrr : (x : R) `x <= x`.
Proof. Exact (leqr_reflexivity R). Qed.
Hints Resolve leqrr.

Lemma leqr_trans : (x1, x2, x3 : R) `x1 <= x2` -> `x2 <= x3` -> `x1 <= x3`.
Proof. Exact (leqr_transitivity R). Qed.

Lemma ubr_sup : (E : R -> Prop) (hasr (ubr E)) -> (ubr E `sup E`).
Proof.
By Move=> E HhiE x Hx; Apply: (supr_upper_bound R) {}Hx; Split; LeftBy Exists x.
Qed.

Lemma ubr_geq_sup : (E : R -> Prop; x : R) (hasr (ubr E)) ->
  `sup E <= x` -> (ubr E x).
Proof. Move=> E x; Move/ubr_sup=> HhiE Hx y Hy; Apply: leqr_trans Hx; Auto. Qed.

Lemma supr_total : (x : R; E : R -> Prop) (has_supr E) -> 
  (boundedr x E) \/ `sup E <= x`.
Proof. Exact (supr_totality R). Qed.

Lemma leqr_total : (x1, x2 : R) `x1 <= x2` \/ `x2 <= x1`.
Proof.
Move=> x1 x2; Pose E := [y](x2 == y).
Step HE: (has_supr E) By Split; Exists x2; RightBy Move=> x [].
Case: (supr_total x1 HE) => [[y []] | HEx1]; LeftBy Left.
By Right; Apply: leqr_trans HEx1; Apply: ubr_sup => //; Exists x2; Move=> x [].
Qed.

Lemma ltr_total : (x1, x2 : R) `x1 <> x2` -> `x1 < x2` \/ `x2 < x1`.
Proof. Move=> x1 x2; Rewrite: /eqr; Move: (leqr_total x1 x2); Tauto. Qed.

Lemma ltrW : (x1, x2 : R) `x1 < x2` -> `x1 <= x2`.
Proof. By Move=> x1 x2 Hx12; Case: (leqr_total x1 x2) => // *; Case: Hx12. Qed.
Hints Resolve ltrW.

Lemma leqr_lt_trans : (x1, x2, x3 : R) `x1 <= x2` -> `x2 < x3` -> `x1 < x3`.
Proof. By Move=> x1 x2 x3 Hx12 Hx23 Hx31; Case: Hx23; Apply: leqr_trans Hx12. Qed.

Lemma ltr_leq_trans : (x1, x2, x3 : R) `x1 < x2` -> `x2 <= x3` -> `x1 < x3`.
Proof. By Move=> x1 x2 x3 Hx12 Hx23 Hx31; Case: Hx12; Apply: leqr_trans Hx31. Qed.

Lemma ltr_trans : (x1, x2, x3 : R) `x1 < x2` -> `x2 < x3` -> `x1 < x3`.
Proof. By Move=> x1 x2 x3 Hx12 Hx23; Apply: ltr_leq_trans (ltrW Hx23). Qed.

(**********************************************************) 
(**      The setoid structure                             *)
(**********************************************************)

Lemma eqr_refl : (x : R) `x = x`.
Proof. Split; Apply: leqrr. Qed.
Hints Resolve eqr_refl.
Hints Unfold eqR.

Remark eqR_refl : (x : R) (eqR x x). Proof. Auto. Qed.
Hints Resolve eqR_refl.

Lemma eqr_sym : (x1, x2 : R) `x1 = x2` -> `x2 = x1`.
Proof. Rewrite: /eqr; Tauto. Qed.
Hints Immediate eqr_sym.

Lemma eqr_trans : (x1, x2, x3 : R) `x1 = x2` -> `x2 = x3` -> `x1 = x3`.
Proof.
Move=> x1 x2 x3 [Hx12 Hx21] [Hx23 Hx32]; Split; EApply leqr_trans; EAuto.
Qed.

Lemma eqr_theory : (Setoid_Theory RR eqR).
Proof. Split; Auto; Exact eqr_trans. Qed.

Add Setoid RR eqR eqr_theory.

Add Morphism isR : isr_morphism. Proof. Done. Qed.

Add Morphism ((!leqr?) :: RR -> RR -> Prop) : leqr_morphism.
Proof. Move: {}leqr_trans => Htr x1 y1 x2 y2 [_ Hyx1] [Hxy2 _]; EAuto. Qed.

Add Morphism leqR : leqR_morphism.
Proof. Unlock leqR; Exact leqr_morphism. Qed.

(**********************************************************) 
(**       Addition                                        *)
(**********************************************************)

Lemma addrC : (x1, x2 : R) `x1 + x2 = x2 + x1`.
Proof. Exact (addr_commutativity R). Qed.

Add Morphism ((!addr ?) :: RR -> RR -> RR) : addr_morphism.
Proof.
Move=> x1 y1 x2 y2 Dx1 Dx2; Apply eqr_trans with `x1 + y2`.
  By Case Dx2; Split; Apply: (addr_monotony R).
Rewrite: eqRI (rwR (addrC x1 y2)) (rwR (addrC y1 y2)).
By Case Dx1; Split; Apply: (addr_monotony R).
Qed.

Add Morphism addR : addR_morphism.
Proof. Unlock addR; Exact addr_morphism. Qed.

Lemma addrA : (x1, x2, x3 : R) `x1 + (x2 + x3) = x1 + x2 + x3`.
Proof. Exact (addr_associativity R). Qed.

Lemma addrCA : (x1, x2, x3 : R) `x1 + (x2 + x3) = x2 + (x1 + x3)`.
Proof.
Move=> x1 x2 x3; Rewrite: eqRI (rwR (addrA x1 x2 x3)) (rwR (addrA x2 x1 x3)).
By Rewrite: addRI (rwR (addrC x1 x2)) -addRI.
Qed.

Lemma add0r : (x : R) `0 + x = x`.
Proof. Exact (addr_neutral_left R). Qed.

Lemma addr0 : (x : R) `x + 0 = x`.
Proof. By Move=> x; Rewrite: eqRI (rwR (addrC x `0`)); Apply: add0r. Qed.

Lemma subrr : (x : R) `x - x = 0`.
Proof. Exact (addr_inverse_right R). Qed.

Lemma addr_inv : (x1, x2 : R) `(-x1) + (x1 + x2) = x2`.
Proof.
Move=> x1 x2; Rewrite: eqRI (rwR (addrCA `-x1` x1 x2)).
Rewrite: (rwR (addrA x1 `-x1` x2)) addRI (rwR (subrr x1)) -addRI; Apply: add0r.
Qed.

Lemma addr_injl : (x, x1, x2 : R) `x + x1 = x + x2` -> `x1 = x2`.
Proof.
Move=> x x1 x2 Ex12; Rewrite: eqRI -(rwR (addr_inv x x1)) addRI (rwR Ex12) -addRI.
Apply: addr_inv.
Qed.

Lemma addr_injr : (x, x1, x2 : R) `x1 + x = x2 + x` -> `x1 = x2`.
Proof.
Move=> x x1 x2; Rewrite: eqRI (rwR (addrC x1 x)) (rwR (addrC x2 x)).
Apply: (!addr_injl).
Qed.

Lemma oppr_opp : (x : R) `-(-x) = x`.
Proof.
Move=> x; Apply addr_injr with `-x`; Rewrite: eqRI (rwR (subrr x)).
Rewrite: (rwR (addrC `-(-x)` `-x`)); Apply: subrr.
Qed.

Lemma oppr_add : (x1, x2 : R) `-(x1 + x2) = -x1 - x2`.
Proof.
Move=> x1 x2; Apply addr_injl with `x1 + x2`; Rewrite: eqRI.
Rewrite: (rwR (addrCA `x1 + x2` `-x1` `-x2`)) (rwR (subrr `x1 + x2`)).
Rewrite: addRI -(rwR (addrA  x1 x2 `-x2`)) -addRI.
By Rewrite: (rwR (addr_inv x1 `x2 - x2`)) (rwR (subrr x2)).
Qed.

Lemma oppr_sub : (x1, x2 : R) `-(x1 - x2) = x2 - x1`.
Proof.
Move=> x1 x2; Rewrite: eqRI (rwR (oppr_add x1 `-x2`)) addRI (rwR (oppr_opp x2)).
Rewrite: -addRI; Apply: addrC.
Qed.

Lemma leqr_add2l : (x, x1, x2 : R) `x + x1 <= x + x2` <-> `x1 <= x2`.
Proof.
Move=> x x1 x2; Split; RightBy Apply (addr_monotony R).
Move=> Hx12; Rewrite: leqRI -(rwR (addr_inv x x1)) -(rwR (addr_inv x x2)) -leqRI.
By Apply (addr_monotony R).
Qed.

Lemma leqr_add2r : (x, x1, x2 : R) `x1 + x <= x2 + x` <-> `x1 <= x2`.
Proof.
Move=> x x1 x2; Rewrite: leqRI (rwR (addrC x1 x)) (rwR (addrC x2 x)) -leqRI.
Apply leqr_add2l.
Qed.

Lemma leqr_0sub : (x1, x2 : R) `x1 <= x2` <-> `0 <= x2 - x1`.
Proof.
Move=> x1 x2; Rewrite: -(leqr_add2r `-x1` x1 x2) leqRI (rwR (subrr x1)) -leqRI.
By Split.
Qed.

Lemma leqr_sub0 : (x1, x2 : R) `x1 <= x2` <-> `x1 - x2 <= 0`.
Proof.
Move=> x1 x2; Rewrite: -(leqr_add2r `-x2` x1 x2) leqRI (rwR (subrr x2)) -leqRI.
By Split.
Qed.

Lemma leqr_opp2 : (x1, x2 : R) `-x1 <= -x2` <-> `x2 <= x1`.
Proof.
Move=> x1 x2; Rewrite: (leqr_0sub `-x1` `-x2`) (leqr_0sub x2 x1).
Rewrite: leqRI addRI (rwR (oppr_opp x1)) -addRI (rwR (addrC `-x2` x1)) -leqRI.
By Split.
Qed.

Lemma oppr_inj : (x1, x2 : R) `-x1 = -x2` -> `x1 = x2`.
Proof.
Move=> x y; Rewrite: /eqR /eqr (leqr_opp2 x y) (leqr_opp2 y x); Tauto.
Qed.

Add Morphism ((!oppr ?) :: RR -> RR) : oppr_morphism.
Proof.
Move=> x y; Rewrite: /eqR /eqr (leqr_opp2 x y) (leqr_opp2 y x); Tauto.
Qed.

Add Morphism oppR : oppR_morphism.
Proof. Unlock oppR; Exact oppr_morphism. Qed.

Lemma oppr0 : `-0 = 0%R`.
Proof. By Rewrite: eqRI -(rwR (subrr `0`)) (rwR (add0r `-0`)). Qed.

(**********************************************************) 
(**       Multiplication                                  *)
(**********************************************************)

Lemma mulrC : (x1, x2 : R) `x1 * x2 = x2 * x1`.
Proof. Exact (mulr_commutativity R). Qed.

Lemma mulr_addr : (x, x1, x2 : R) `x * (x1 + x2) = x * x1 + x * x2`.
Proof. Exact (mulr_addr_distributivity_right R). Qed.

Lemma mulr_addl : (x, x1, x2 : R) `(x1 + x2) * x = x1 * x + x2 * x`.
Proof.
Move=> x x1 x2; Rewrite: eqRI (rwR (mulrC `x1+x2` x)) (rwR (mulr_addr x x1 x2)).
By Rewrite: addRI (rwR (mulrC x x1)) (rwR (mulrC x x2)) -addRI.
Qed.

Add Morphism ((!mulr ?) :: RR -> RR -> RR) : mulr_morphism.
Proof.
Step Hpos: (x, x1, x2 : R) `x >= 0` -> `x1 = x2` -> `x * x1 = x * x2`.
  By Move=> x x1 x2 Hx [Hx12 Hx21]; Split; Apply (mulr_monotony R).
Step Hmull: (x, x1, x2 : R) `x1 = x2` -> `x * x1 = x * x2`.
  Move=> x x1 x2 Dx1; Case: (leqr_total `0` x) => [Hx]; Auto.
  Step Hx': `-x >= 0`.
    By Move: Hx; Rewrite: -(leqr_opp2 `0` x) !leqRI (rwR oppr0).
  Apply addr_injr with `(-x) * x1`.
  Rewrite: eqRI -(rwR (mulr_addl x1 x `-x`)) 2!addRI -addRI.
  Rewrite: (rwR (Hpos ? ? ? Hx' Dx1)) -addRI -(rwR (mulr_addl x2 x `-x`)).
  Apply: Hpos; RightDone; Apply eqr_leq; Apply eqr_sym; Apply subrr.
Rewrite: /eqR; Move=> x1 y1 x2 y2 Dx1 Dx2.
Apply eqr_trans with `x1 * y2`; Auto.
Rewrite: eqRI (rwR (mulrC x1 y2)) (rwR (mulrC y1 y2)) -eqRI; Auto.
Qed.

Add Morphism mulR : mulR_morphism. Proof. Unlock mulR; Exact mulr_morphism. Qed.

Lemma mulrA : (x1, x2, x3 : R) `x1 * (x2 * x3) = x1 * x2 * x3`.
Proof. Exact (mulr_associativity R). Qed.

Lemma mulrCA : (x1, x2, x3 : R) `x1 * (x2 * x3) = x2 * (x1 * x3)`.
Proof.
Move=> x1 x2 x3; Rewrite: eqRI (rwR (mulrA x1 x2 x3)) (rwR (mulrA x2 x1 x3)).
By Rewrite: mulRI (rwR (mulrC x1 x2)) -mulRI.
Qed.

Lemma mul1r : (x : R) `1 * x = x`.
Proof. Exact (mulr_neutral_left R). Qed.

Lemma mulr1 : (x : R) `x * 1 = x`.
Proof. By Move=> x; Rewrite: eqRI (rwR (mulrC x `1`)); Apply: mul1r. Qed.

Lemma mul2r: (x : R) `2 * x = x + x`.
Proof.
By Move=> x; Rewrite: eqRI (rwR `(mulr_addl x 1 1)`) !addRI (rwR (mul1r x)).
Qed.

Lemma mul0r : (x : R) `0 * x = 0`.
Proof.
Move=> x; Apply addr_injl with `1 * x`.
Rewrite: eqRI -(rwR `(mulr_addl x 1 0)`) (rwR (addr0 `1 * x`)).
By Rewrite: !mulRI (rwR `(addr0 1)`).
Qed.

Lemma mulr0 : (x : R) `x * 0 = 0`.
Proof. By Move=> x; Rewrite: eqRI (rwR (mulrC x `0`)); Apply: mul0r. Qed.

Lemma mulr_oppr : (x1, x2 : R) `x1 * -x2 = -(x1 * x2)`.
Proof.
Move=> x1 x2; Apply addr_injl with `x1 * x2`.
Rewrite: eqRI -(rwR (mulr_addr x1 x2 `-x2`))  (rwR (subrr `x1 * x2`)).
Rewrite: mulRI (rwR (subrr x2)) -mulRI; Apply: mulr0.
Qed.

Lemma mulr_oppl : (x1, x2 : R) `-x1 * x2 = -(x1 * x2)`.
Proof.
Move=> x1 x2; Rewrite: eqRI (rwR (mulrC `-x1` x2)) (rwR (mulr_oppr x2 x1)).
By Rewrite: !oppRI (rwR (mulrC x2 x1)).
Qed.

Lemma mulr_opp : (x : R) `-1 * x = -x`.
Proof. 
By Move=> x; Rewrite: eqRI (rwR (mulr_oppl `1` x)) !oppRI (rwR (mul1r x)).
Qed.

Lemma mulr_opp1 : (x : R) `x * -1 = -x`.
Proof. Move=> x; Rewrite: eqRI (rwR (mulrC x `-1`)); Apply: mulr_opp. Qed.

(* Properties of 1 (finally!) *)

Lemma neqr10 : `1 <> 0%R`.
Proof. Exact (mulr_neutral_nonzero R). Qed.

Lemma ltr01 : `0 < 1%R`.
Proof.
Case/ltr_total: {}neqr10 => // [H] H10; Case: H; Move: {}H10.
Rewrite: -`(leqr_opp2 0 1%R)` -`(leqr_opp2 1 0%R)` !leqRI (rwR oppr0) -leqRI.
Move=> Hn1; Rewrite: -(rwR (mulr1 `-1`)) -(rwR (mulr0 `-1`)) -leqRI.
By Apply (mulr_monotony R).
Qed.
Hints Resolve ltr01.

Lemma ltrSr : (x : R) `x < x + 1`.
Proof.
By Move=> x; Rewrite: leqRI -(rwR (addr0 x)) -leqRI `(leqr_add2l x 1 0)`.
Qed.
Implicits ltrSr [].

Lemma ltPrr : (x : R) `x - 1 < x`.
Proof.
Move=> x; Rewrite: -(leqr_opp2 `x - 1` x) leqRI (rwR (oppr_add x `-1`)).
Rewrite: addRI (rwR (oppr_opp `1`)) -addRI -leqRI; Apply ltrSr.
Qed.
Implicits ltPrr [].

Lemma ltr02 : `0 < 2%R`.
Proof. Exact (ltr_trans ltr01 (ltrSr ?)). Qed.
Hints Resolve ltr02.

(* Division (well, mostly inverse) *)

Lemma divrr : (x : R) `x <> 0` -> `x/x = 1`.
Proof. Exact (mulr_inverse_right R). Qed.

Lemma leqr_pmul2l : (x, x1, x2 : R) `0 < x` ->
  (`x * x1 <= x * x2` <-> `x1 <= x2`).
Proof.
Move=> x x1 x2 Hx; Split; RightBy Apply (mulr_monotony R); Apply ltrW.
Move=> Hx12; Rewrite: leqRI -(rwR (mul1r x1)) -(rwR (mul1r x2)).
Rewrite: !mulRI -(rwR (divrr (gtr_neq Hx))) (rwR (mulrC x `1/x`)) -!mulRI.
Rewrite: -(rwR (mulrA `1/x` x x1)) -(rwR (mulrA `1/x` x x2)) -leqRI.
Apply: (mulr_monotony R) Hx12; Apply ltrW; Move=> Hix.
Case ltr01; Rewrite: leqRI -(rwR (divrr (gtr_neq Hx))) -(rwR (mulr0 x)) -leqRI.
By Apply: (mulr_monotony R) Hix; Apply ltrW.
Qed.

Lemma leqr_pmul2r : (x, x1, x2 : R) `0 < x` ->
  (`x1 * x <= x2 * x` <-> `x1 <= x2`).
Proof.
Move=> x x1 x2 Hx; Rewrite: leqRI (rwR (mulrC x1 x)) (rwR (mulrC x2 x)) -leqRI.
Apply: leqr_pmul2l Hx.
Qed.

Lemma pmulr_inv : (x, x1 : R) `0 < x` -> `1/x * (x * x1) = x1`.
Proof.
Move=> x x1 Hx; Rewrite: eqRI (rwR (mulrCA `1/x` x x1)) (rwR (mulrA x `1/x` x1)).
Rewrite: mulRI (rwR (divrr (gtr_neq Hx))) -mulRI; Apply: mul1r.
Qed.

Lemma posr_pmull : (x1, x2 : R) `x1 > 0` -> (`x1 * x2 <= 0` <-> `x2 <= 0`).
Proof.
Move=> x1 x2 Hx1.
Rewrite: -(leqr_pmul2l x2 `0` Hx1) 2!leqRI (rwR (mulr0 x1)); Tauto.
Qed.

Lemma pmulr_injl : (x, x1, x2 : R) `0 < x` -> `x * x1 = x * x2` -> `x1 = x2`.
Proof.
Move=> x x1 x2 Hx Ex12; Rewrite: eqRI -(rwR (pmulr_inv x1 Hx)) mulRI (rwR Ex12).
Rewrite: -mulRI; Exact (pmulr_inv x2 Hx).
Qed.

Lemma pmulr_injr : (x, x1, x2 : R) `0 < x` -> `x1 * x = x2 * x` -> `x1 = x2`.
Proof.
Move=> x x1 x2 Hx; Rewrite: eqRI (rwR (mulrC x1 x)) (rwR (mulrC x2 x)).
By Apply: pmulr_injl.
Qed.

Lemma mulr_injl : (x, x1, x2 : R) `x <> 0` -> `x * x1 = x * x2` -> `x1 = x2`.
Proof.
Move=> x x1 x2 Hx; Case: (leqr_total `0` x) => [Hx0].
  By Apply: pmulr_injl => [H0x]; Case Hx; Split.
Move/oppr_morphism; Rewrite: eqRI -(rwR (mulr_oppl x x1)) -(rwR (mulr_oppl x x2)).
Apply: pmulr_injl; Rewrite: leqRI -(rwR oppr0) -leqRI (leqr_opp2 x `0`).
By Move=> H0x; Case Hx; Split.
Qed.

Lemma mulr_injr : (x, x1, x2 : R) `x <> 0` -> `x1 * x = x2 * x` -> `x1 = x2`.
Proof.
Move=> x x1 x2 Hx; Rewrite: eqRI (rwR (mulrC x1 x)) (rwR (mulrC x2 x)).
By Apply: mulr_injl.
Qed.

(* The inverse is only a partial morphism. It might be worth fixing, say,  *)
(* 1/0 = 0 in order to make setoid rewriting work better.                  *)

Lemma invr_morphism : (x, y : R) `x <> 0` -> `x = y` -> `1/x = 1/y`.
Proof.
Move=> x y Hx Dx; Step Hy: `y <> 0` By Rewrite: eqRI -(rwR Dx).
Apply: (mulr_injl Hx); Rewrite: eqRI (rwR (divrr Hx)) -(rwR (divrr Hy)).
By Rewrite: !mulRI (rwR Dx).
Qed.

Lemma invr1 : `1/1 = 1%R`.
Proof. By Rewrite: eqRI -(rwR (divrr neqr10)) (rwR (mul1r `1/1`)). Qed.

Lemma invr_pmul : (x1, x2 : R) `0 < x1` -> `0 < x2` ->
  `1 / (x1 * x2) = (1/x1) / x2`.
Proof.
Move=> x1 x2 Hx1 Hx2; Pose y := `1 / (x1 * x2)`; Apply: (pmulr_injl Hx1).
Rewrite: eqRI (rwR (mulrCA x1 `1/x1` `1/x2`)) (rwR (pmulr_inv `1/x2` Hx1)) /isR.
Apply: (pmulr_injl Hx2); Rewrite: eqRI (rwR (divrr (gtr_neq Hx2))).
Rewrite: (rwR (mulrCA x2 x1 y)) (rwR (mulrA x1 x2 y)).
Apply: divrr; Apply: gtr_neq; Rewrite: leqRI -(rwR (mulr0 x1)) -leqRI.
By Rewrite: (leqr_pmul2l x2 `0` Hx1).
Qed.

Lemma invr_opp : (x : R) `x <> 0` -> `1/-x = -(1/x)`.
Proof.
Move=> x Hx; Apply: (mulr_injl Hx); Apply oppr_inj.
Rewrite: eqRI -(rwR (mulr_oppl x `1/-x`)) -(rwR (mulr_oppr x `-(1/x)`)).
Rewrite: !mulRI (rwR (oppr_opp `1/x`)) -!mulRI (rwR (divrr Hx)); Apply: divrr.
By Rewrite: eqRI -(rwR oppr0) -eqRI; Move/oppr_inj.
Qed.

Lemma posr_inv : (x : R) `0 < x` -> `0 < 1/x`.
Proof.
Move=> x Hx; Rewrite: -(leqr_pmul2l `1/x` `0` Hx).
By Rewrite: leqRI (rwR (mulr0 x)) (rwR (divrr (gtr_neq Hx))) -leqRI.
Qed.

Lemma leqr_pinv2 : (x1, x2 : R) `0 < x1` -> `0 < x2` ->
  (`1/x1 <= 1/x2` <-> `x2 <= x1`).
Proof.
Move=> x1 x2 Hx1 Hx2; Rewrite: -(leqr_pmul2r `1/x1` `1/x2` Hx1).
Rewrite: -(leqr_pmul2l `1/x1 * x1` `1/x2 * x1` Hx2).
Rewrite: !leqRI (rwR (mulrC x2 `1/x1 * x1`)) -(rwR (mulrA `1/x1` x1 x2)).
Rewrite: (rwR (mulrCA x2 `1/x2` x1)) (rwR (pmulr_inv x1 Hx2)).
Rewrite: (rwR (pmulr_inv x2 Hx1)); Tauto.
Qed.

(**********************************************************) 
(**      The least upper bound and derived operations.    *)
(**********************************************************) 

Lemma leqr_sup_ub : (E : R -> Prop; x : R)
  (hasr E) -> (ubr E x) -> `sup E <= x`.
Proof.
Move=> E x HloE Hx; Pose y := (supr E); Pose z := `(x + y) / 2`.
Step Dz: `2 * z = x + y`.
  Apply: (eqr_trans (mulrA ? ? ?)); Apply: (eqr_trans (mulrC ? ?)).
  By Apply: pmulr_inv; Exact ltr02.
Step HE: (has_supr E) By Split; RightBy Exists x.
Case: (supr_total z HE) => [[t Ht Hzt] | Hyz]; IP.
  Rewrite: -(leqr_add2l x y x) leqRI -(rwR Dz) -(rwR (mul2r x)) -leqRI.
  Rewrite: (leqr_pmul2l z x ltr02); Apply: (leqr_trans Hzt); Auto.
Rewrite: -(leqr_add2r y y x) leqRI -(rwR Dz) -(rwR (mul2r y)) -leqRI.
By Rewrite: (leqr_pmul2l y z ltr02).
Qed.

Lemma supr_sup : (E : R -> Prop) (has_supr E) ->
  (x : R) (ubr E x) <-> `sup E <= x`.
Proof.
By Move=> E [HloE HhiE] x; Split; [Apply leqr_sup_ub | Apply ubr_geq_sup].
Qed.

(* Partial morphism property of the sup function; similarly to 1/0,   *)
(* it might be helpful to define (supr [_]True) and (supr [_]False).  *)

Lemma supr_morphism : (E : R -> Prop) (has_supr E) ->
  (E' : R -> Prop) ((x : R) (E x) <-> (E' x)) -> `sup E = sup E'`.
Proof.
Step Hleq: (E, E' : R -> Prop) (hasr E) -> (hasr (ubr E')) ->
           ((x : R) (E x) -> (E' x)) -> `sup E <= sup E'`.
  By Move=> *; Apply: leqr_sup_ub => // [x Hx]; Apply ubr_sup; Auto.
Move=> E [HloE HhiE] E' DE'.
Split; (Apply Hleq; Auto; RightBy Move=> x; Case (DE' x); Auto).
  By Move: HhiE => [y Hy]; Exists y; Move=> x; Case (DE' x); Auto.
By Move: HloE => [x Hx]; Case (DE' x); Exists x; Auto.
Qed.

(* Definition by nondeterministic cases.                        *)

Section PickrCases.

Variables P1, P2 : Prop; x1, x2 : R.
Hypotheses HP : P1 \/ P2; HPx : P1 /\ P2 -> `x1 = x2`.

Inductive pickr_spec : R -> Prop :=
  PickrSpec : (y : R) (pickr_set P1 P2 x1 x2 y) -> (pickr_spec y).

Lemma pickr_cases : (pickr_spec (pickr P1 P2 x1 x2)).
Proof.
Pose ps := (pickr_set P1 P2 x1 x2); Pose x := (pickr P1 P2 x1 x2).
Step [x3 Hx3lo Ex3] : (EXT x3 | (ps x3) & (y : R)(ps y) <-> `y = x3`).
  Case: HP => [HPi]; [Exists x1; Try Split; Try By Left; Split
                    | Exists x2; Try Split; Try By Right; Split];
  Case=> [[Hpj Dy]] //; Apply: (eqr_trans Dy); Auto; Apply eqr_sym; Auto.
Step Hx3hi: (ubr ps x3).
  By Move=> x4; Rewrite: (Ex3 x4); Move=> Dx4; Rewrite: leqRI (rwR Dx4) -leqRI.
Split; IP; Rewrite: -/ps (Ex3 x); Split; RightBy Apply: ubr_sup; LeftBy Exists x3.
By Apply: leqr_sup_ub; LeftBy Exists x3.
Qed.

End PickrCases.

Section PickrMorphism.

Variables P1, P2 : Prop; x1, x2 : R.
Hypotheses HP : P1 \/ P2; HPx : P1 /\ P2 -> `x1 = x2`.

Lemma pickr_morphism : (Q1, Q2 : Prop; y1, y2 : R)
  (P1 <-> Q1) -> (P2 <-> Q2) -> `x1 = y1` -> `x2 = y2` ->
  `(pickr P1 P2 x1 x2) = (pickr Q1 Q2 y1 y2)`.
Proof.
Move=> Q1 Q2 y1 y2 DP1 DP2 Dx1 Dx2; Rewrite: -/eqR.
Step HQ: Q1 \/ Q2 By Rewrite: -DP1 -DP2.
Step HQy: Q1 /\ Q2 -> `y1 = y2` By Rewrite: -DP1 -DP2 eqRI -(rwR Dx1) -(rwR Dx2).
Case: (pickr_cases HQ HQy) => [y]; Case: (pickr_cases HP HPx) => [x].
Rewrite: /pickr_set -DP1 -DP2 (eqRI y y1) -(rwR Dx1) (eqRI y y2) -(rwR Dx2) -!eqRI.
Case=> [[HPi Dx]]; Case=> [[HPj Dy]];
   Rewrite: /eqR eqRI (rwR Dx) (rwR Dy) -eqRI; Auto; Apply eqr_sym; Auto.
Qed.

End PickrMorphism.

(* min and max.                                                         *)

Section MinMaxReal.

Variables x1, x2 : R.

Local Hx12 : `x1 <= x2` \/ `x2 <= x1` := (leqr_total x1 x2).
Local Ex12 [H : `x1 <= x2` /\ `x2 <= x1`] : `x1 = x2` := H.
Local Ex21 [H : `x1 <= x2` /\ `x2 <= x1`] : `x2 = x1` := (eqr_sym H).

Lemma leqr_minl : `(minr x1 x2) <= x1`.
Proof.
Rewrite: /minr; Case: (pickr_cases Hx12 Ex12) => [x3].
By Case=> [[Hx Dx3]]; Rewrite: leqRI (rwR Dx3) -leqRI.
Qed.

Lemma leqr_minr : `(minr x1 x2) <= x2`.
Proof.
Rewrite: /minr; Case: (pickr_cases Hx12 Ex12) => [x3].
By Case=> [[Hx Dx3]]; Rewrite: leqRI (rwR Dx3) -leqRI.
Qed.
Hints Resolve leqr_minl leqr_minr.

Lemma ltr_min : (x : R) `x < (minr x1 x2)` <-> `x < x1` /\ `x < x2`.
Proof.
Rewrite: /minr; Case: (pickr_cases Hx12 Ex12) => [x3].
Case=> [[Hx Dx3]] x; Rewrite: leqRI (rwR Dx3) -leqRI;
  By Split; [Split; Try By Apply: ltr_leq_trans Hx | Case].
Qed.

Lemma leqr_min : (x : R) `x <= (minr x1 x2)` <-> `x <= x1` /\ `x <= x2`.
Proof.
Move=> x; Split; LeftBy Split; EApply leqr_trans; EAuto.
Move=> [Hxx1 Hxx2]; Rewrite: /minr; Case: (pickr_cases Hx12 Ex12) => [x3].
By Case=> [[Hx Dx3]]; Rewrite: leqRI (rwR Dx3) -leqRI.
Qed.

Lemma leqr_maxl : `x1 <= (maxr x1 x2)`.
Proof.
Rewrite: /maxr; Case: (pickr_cases Hx12 Ex21) => [x3].
By Case=> [[Hx Dx3]]; Rewrite: leqRI (rwR Dx3) -leqRI.
Qed.

Lemma leqr_maxr : `x2 <= (maxr x1 x2)`.
Proof.
Rewrite: /maxr; Case: (pickr_cases Hx12 Ex21) => [x3].
By Case=> [[Hx Dx3]]; Rewrite: leqRI (rwR Dx3) -leqRI.
Qed.
Hints Resolve leqr_maxl leqr_maxr.

Lemma ltr_max : (x : R) `(maxr x1 x2) < x` <-> `x1 < x` /\ `x2 < x`.
Proof.
Rewrite: /maxr; Case: (pickr_cases Hx12 Ex21) => [x3].
Case=> [[Hx Dx3]] x; Rewrite: leqRI (rwR Dx3) -leqRI;
  By Split; [Split; Try By Apply: (leqr_lt_trans Hx) | Case].
Qed.

Lemma leqr_max : (x : R) `(maxr x1 x2) <= x` <-> `x1 <= x` /\ `x2 <= x`.
Proof.
Move=> x; Split; LeftBy Split; EApply leqr_trans; EAuto.
Move=> [Hxx1 Hxx2]; Rewrite: /maxr; Case: (pickr_cases Hx12 Ex21) => [x3].
By Case=> [[Hx Dx3]]; Rewrite: leqRI (rwR Dx3) -leqRI.
Qed.

End MinMaxReal.

Add Morphism ((!minr ?) :: RR -> RR -> RR) : minr_morphism.
Proof.
Move=> x1 y1 x2 y2 Dx1 Dx2; Apply: (pickr_morphism ? ? ?) => //;
  Try Apply leqr_total; By Rewrite: !leqRI Dx1 Dx2; Split.
Qed.

Add Morphism minR : minR_morphism. Proof. Unlock minR; Exact minr_morphism. Qed.

Add Morphism ((!maxr ?) :: RR -> RR -> RR) : maxr_morphism.
Proof.
Move=> x1 y1 x2 y2 Dx1 Dx2; Apply: (pickr_morphism ? ? ?) => //;
  Try Apply leqr_total; Try By Rewrite: !leqRI Dx1 Dx2; Split.
By Move/eqr_sym.
Qed.

Add Morphism maxR : maxR_morphism. Proof. Unlock maxR; Exact maxr_morphism. Qed.

(**********************************************************) 
(** Properties of the injections from N, Z, and Q into R  *)
(**********************************************************)

Lemma natr_S : (n : nat) `(S n) = n + 1`.
Proof.
Case=> [|n] /=; LeftBy Rewrite: eqRI (rwR (add0r `1`)).
Elim: n {2 3}`1%R` => //= [] x; Apply addrC.
Qed.

Lemma ltr0Sn : (n : nat) `0 < (S n)`.
Proof.
Elim=> [|n Hrec]; LeftBy Exact ltr01.
Apply: (ltr_trans Hrec) {Hrec}.
Rewrite: leqRI -(rwR (addr0 (S n))) (rwR (natr_S (S n))) -leqRI.
By Rewrite: `(leqr_add2l (S n) 1 0)`.
Qed.
Implicits ltr0Sn [].

Lemma leqr0n : (n : nat) `0 <= n`.
Proof. By Move=> [|n]; [Apply leqrr | Apply ltrW; Apply ltr0Sn]. Qed.

Lemma znatr_inc : (m : znat) `(incz m) = m + 1`.
Proof.
Move=> [n|n]; Rewrite: eqRI; LeftBy Rewrite: /= -/natR -(rwR (natr_S n)).
Case: n => [|n]; LeftBy Rewrite: /= (rwR (addrC `-1` `1`)) (rwR (subrr `1`)).
Rewrite: {2}/znatR /znatr -/natR addRI oppRI (rwR (natr_S (S n))) -oppRI.
Rewrite: (rwR (oppr_add (S n) `1`)) -addRI.
Rewrite: -(rwR (addrA `-(S n)` `-1` `1`)) addRI (rwR (addrC `-1` `1`)).
By Rewrite: (rwR (subrr `1`)) -addRI (rwR (addr0 `-(S n)`)).
Qed.

Lemma znatr_dec : (m : znat) `(decz m) = m - 1`.
Proof.
Move=> m; Rewrite: -{2 m}incz_dec; Move/decz: m => m.
Rewrite: eqRI addRI (rwR (znatr_inc m)) -addRI -(rwR (addrA m `1` `-1`)).
By Rewrite: addRI (rwR (subrr `1`)) -addRI (rwR (addr0 m)).
Qed.

Lemma znatr_opp : (m : znat) `(oppz m) = -m`.
Proof.
Move=> [[|[|n]]|[|m]] //=; Apply eqr_sym; First [Apply oppr0 | Apply: oppr_opp].
Qed.

Lemma znatr_add : (m1, m2 : znat) `(addz m1 m2) = m1 + m2`.
Proof.
Step znatr_addpos : (n : nat; m : znat) `(addz (Zpos n) m) = n + m`.
  Move=> n m; Elim: n => [|n Hrec]; LeftBy Rewrite: add0z /= eqRI (rwR (add0r m)).
  Rewrite: eqRI addRI (rwR (natr_S n)) -addRI -add1n zpos_addn -addzA addzC.
  Rewrite: -incz_def (rwR (znatr_inc (addz (Zpos n) m))) addRI (rwR Hrec) -addRI.
  Rewrite: -(rwR (addrA n m `1`)) -(rwR (addrA n `1` m)).
  By Rewrite: addRI (rwR (addrC m `1`)) -addRI.
Move=> [n1|m1] m2; LeftBy Apply: znatr_addpos.
Pose m12 := (addz (Zneg m1) m2); Rewrite: -(oppz_opp m12) eqRI.
Rewrite: (rwR (znatr_opp (oppz m12))) ~/m12 oppz_add {addz}lock /= -lock.
Rewrite: oppRI (rwR (znatr_addpos (S m1) (oppz m2))) -oppRI.
Rewrite: (rwR (oppr_add (S m1) (oppz m2))) addRI.
By Rewrite: -(rwR (znatr_opp (oppz m2))) oppz_opp -addRI.
Qed.

Lemma znatr_subz : (m1, m2 : znat) `(subz m1 m2) = m1 - m2`.
Proof.
Move=> m1 m2; Rewrite: eqRI /subz (rwR (znatr_add m1 (oppz m2))).
By Rewrite: !addRI (rwR (znatr_opp m2)).
Qed.

Lemma znatr_mul : (m1, m2 : znat) `(mulz m1 m2) = m1 * m2`.
Proof.
Move=> m1 m2; Elim/oppz_cases: m1 => [m1 Dm12| n1].
  Rewrite: mulz_oppl eqRI (rwR (znatr_opp (mulz m1 m2))) oppRI~{Dm12}(rwR Dm12).
  By Rewrite: -oppRI -(rwR (mulr_oppl m1 m2)) !mulRI (rwR (znatr_opp m1)).
Elim: n1 => [|n1 Hrec]; LeftBy Rewrite: mul0z eqRI /= (rwR (mul0r m2)).
Rewrite: -add1n zpos_addn mulzC mulz_addr !(mulzC m2) eqRI {1}/mulz {1}/iter mulRI.
Rewrite: (rwR (znatr_add (Znat 1) (Zpos n1))).
Rewrite: (rwR (znatr_add m2 (mulz (Zpos n1) m2))).
Rewrite: -mulRI (rwR (mulr_addl m2 (Znat 1) (Zpos n1))) !addRI.
By Rewrite: (rwR Hrec) /= (rwR (mul1r m2)).
Qed.

Lemma znatr_scale : (d : nat; m : znat) `(scalez d m) = (S d) * m`.
Proof. Move=> d m; Exact (znatr_mul (Zpos (S d)) m). Qed.

Lemma znatr_addbit : (m : znat) `m = (oddz m) + 2 * (halfz m)`.
Proof.
Move=> m; Rewrite: -{1 m}odd_double_halfz; Move/halfz: m (oddz m) => m b.
Rewrite: eqRI (rwR (znatr_add (Zpos b) (addz m m))) 2!addRI -{`2%R`}/((Znat 2)::R).
By Rewrite: -(rwR (znatr_mul (Znat 2) m)) /=.
Qed.

Lemma znatr_leqPx : (m1, m2 : znat) (reflect `m1 <= m2` (leqz m1 m2)).
Proof.
Move=> m1 m2;  Rewrite: /leqz; Apply: (iffP idP);
  Rewrite: (leqr_sub0 m1 m2) leqRI -(rwR (znatr_subz m1 m2)) -leqRI;
  Case: (subz m1 m2) => [[|n]|m] //; RightBy Case/(ltr0Sn ?).
Rewrite: leqRI -(rwR oppr0) -leqRI /znatR /znatr -/natR (leqr_opp2 (S m) `0`).
Clear; Apply leqr0n.
Qed.

Syntactic Definition znatr_leqP := znatr_leqPx | 2.

Lemma znatr_ltPx :  (m1, m2 : znat) (reflect `m1 < m2` (leqz (incz m1) m2)).
Proof.
Move=> m1 m2; Rewrite: -negb_leqz.
By Apply: (iffP idP) => [Hm12]; [Move/znatr_leqP: Hm12 | Apply/znatr_leqP].
Qed.

Syntactic Definition znatr_ltP := znatr_ltPx | 2.

(* Embedding the rationals.                                                     *)

Lemma fracr_eq : (d : nat; m : znat; f : frac)
  f = (Frac d m) -> `m = (S d) * f`.
Proof.
Move=> d m f Df; Rewrite: Df /fracR /fracr -/natR -/znatR eqRI.
Rewrite:  (rwR (mulrA (S d) m `1 / (S d)`)) (rwR (mulrC `(S d) * m` `1 / (S d)`)).
By Rewrite: (rwR (pmulr_inv m (ltr0Sn d))).
Qed.

Lemma fracr_leqPx : (f1, f2 : frac) (reflect `f1 <= f2` (leqf f1 f2)).
Proof.
Move=> f1 f2; Case Df1: {2}f1 => [d1 m1]; Case Df2: {2}f2 => [d2 m2] /=.
Step [Hzr Hrz]: `(scalez d2 m1) <= (scalez d1 m2)` <-> `f1 <= f2`.
  Rewrite: leqRI (rwR (znatr_scale d2 m1)) (rwR (znatr_scale d1 m2)).
  Rewrite: !mulRI (rwR (fracr_eq Df1)) (rwR (fracr_eq Df2)) -!mulRI.
  Rewrite: (rwR (mulrCA (S d2) (S d1) f1)) -leqRI.
  Rewrite: (leqr_pmul2l `(S d2) * f1` `(S d2) * f2` (ltr0Sn d1)).
  Apply: leqr_pmul2l; Apply: ltr0Sn.
By Apply: (iffP znatr_leqP).
Qed.

Syntactic Definition fracr_leqP := fracr_leqPx | 2.

Lemma fracr_ltPx : (f1, f2 : frac) (reflect `f1 < f2` (ltf f1 f2)).
Proof.
Move=> f1 f2; Rewrite: /ltf; Case (fracr_leqPx f2 f1); Constructor; Tauto.
Qed.

Syntactic Definition fracr_ltP := fracr_ltPx | 2.

Lemma fracrz : (m : znat) [f := (Frac (0) m)] `m = f`.
Proof. By Move=> m f; Rewrite: eqRI -(rwR (mul1r f)); Apply: (!fracr_eq (0)). Qed.

Lemma fracr0 : `F0 = 0%R`.
Proof. Apply eqr_sym; Exact (fracrz (Znat 0)). Qed.

Lemma fracr1 : `F1 = 1%R`.
Proof. Apply eqr_sym; Exact (fracrz (Znat 1)). Qed.

Lemma fracr_posPx : (f : frac) (reflect `f <= 0` (negb (posf f))).
Proof.
Move=> f; Rewrite: -nposfI.
By Apply: (iffP fracr_leqP); Rewrite: !leqRI (rwR fracr0).
Qed.

Syntactic Definition fracr_posP := fracr_posPx | 1.

Lemma fracr_opp : (f : frac) `(oppf f) = -f`.
Proof.
Move=> [d m]; Rewrite: /oppf /fracR /fracr -/znatR -/natR eqRI.
Rewrite: !mulRI (rwR (znatr_opp m)) -!mulRI; Apply: mulr_oppl.
Qed.

Lemma natr_muld : (d1, d2 : nat) `(S (muld d1 d2)) = (S d1) * (S d2)`.
Proof.
Move=> d1 d2; Pose m := (Znat 1); Apply: (pmulr_injr ltr01::`m > 0`).
Rewrite: eqRI -(rwR (znatr_scale (muld d1 d2) m)) -scalez_scale.
Rewrite: -(rwR (mulrA (S d1) (S d2) m)) (rwR (znatr_scale d1 (scalez d2 m))).
By Rewrite: 2!mulRI (rwR (znatr_scale d2 m)).
Qed.

Lemma fracr_add : (f1, f2 : frac) `(addf f1 f2) = f1 + f2`.
Proof.
Move=> f1 f2; Def Df: f := (addf f1 f2).
Case Df1: {1}f1 Df => [d1 m1]; Case Df2: {1}f2 => [d2 m2] /=.
Pose d := (muld d1 d2); Move=> Df; Apply: (pmulr_injl (ltr0Sn d)).
Rewrite: eqRI (rwR (mulr_addr (S d) f1 f2)) -~{Df}(rwR (fracr_eq Df)).
Rewrite: (rwR (znatr_add (scalez d2 m1) (scalez d1 m2))) !addRI.
Rewrite: (rwR (znatr_scale d2 m1)) (rwR (znatr_scale d1 m2)) !mulRI ~/d.
Rewrite: (rwR (fracr_eq Df1)) (rwR (fracr_eq Df2)) (rwR (natr_muld d1 d2)) -!mulRI.
Rewrite: (rwR (mulrCA (S d2) (S d1) f1)).
By Rewrite: (rwR (mulrA (S d1) (S d2) f1)) (rwR (mulrA (S d1) (S d2) f2)).
Qed.

Lemma fracr_mul : (f1, f2 : frac) `(mulf f1 f2) = f1 * f2`.
Proof.
Move=> f1 f2; Def Df: f := (mulf f1 f2).
Case Df1: {1}f1 Df => [d1 m1]; Case Df2: {1}f2 => [d2 m2] /=.
Pose d := (muld d1 d2); Move=> Df; Apply: (pmulr_injl (ltr0Sn d)).
Rewrite: eqRI -(rwR (fracr_eq Df)) (rwR (znatr_mul m1 m2)).
Rewrite: mulRI (rwR (fracr_eq Df1)) (rwR (fracr_eq Df2)) -mulRI.
Rewrite: -(rwR (mulrA (S d1) f1 `(S d2) * f2`)).
Rewrite: mulRI (rwR (mulrCA f1 (S d2) f2)) -mulRI.
Rewrite: (rwR (mulrA (S d1) (S d2) `f1 * f2`)).
By Rewrite: mulRI -(rwR (natr_muld d1 d2)) -/d -mulRI.
Qed.

Lemma fracr_pinv : (f : frac) (posf f) -> `(invf f) = 1/f`.
Proof.
Move=> f Hff; Step Hf: `f > 0`.
  Move: Hff; Rewrite: -posfI; Move/fracr_leqP.
  By Rewrite: leqRI /F0 -(rwR (fracrz (Znat 0))) -leqRI.
Apply: (pmulr_injl Hf); Rewrite: eqRI (rwR (divrr (gtr_neq Hf))).
Case Df: {1 3}f Hff => [d [[|m]|m]] // _; Rewrite: /invf {2}/fracR /fracr /znatr.
Rewrite: -/natR (rwR (mulrA f (S d) `1 / (S m)`)) mulRI (rwR (mulrC f (S d))).
Rewrite: -(rwR (fracr_eq Df)) -mulRI; Apply: divrr; Apply gtr_neq; Apply: ltr0Sn.
Qed.

(* The floor function                                                   *)

Remark ubr_floor_set : (x : R) (ubr (floor_set x) x).
Proof. By Move=> x y [m]. Qed.
Hints Resolve ubr_floor_set.

Remark hasr_ub_floor_set : (x : R) (hasr (ubr (floor_set x))).
Proof. By Move=> x; Exists x. Qed.
Hints Resolve hasr_ub_floor_set.

Remark hasr_floor_max : (x : R) (hasr (floor_set x)) -> `x < (floor x) + 1`.
Proof.
Move=> x Hxlo Hx; Step Hinc: (m : znat) `m <= x` -> `(incz m) <= x`.
  Move=> m Hm; Apply: leqr_trans Hx; Rewrite: leqRI (rwR (znatr_inc m)) -leqRI.
  IP; Rewrite: (leqr_add2r `1` m (floor x)); Apply: ubr_sup; Auto.
  By Rewrite: /znatR; Split.
Step Hsup: (has_supr (floor_set x)) By Split.
Case: (supr_total `(floor x) - 1` Hsup); RightBy Apply: ltPrr.
Move=> [y [m]] {y}; Do 2 Move/(Hinc ?).
Rewrite: -/znatR -{2 m}decz_inc; Move/incz: m => m Hm.
Rewrite: leqRI (rwR (znatr_dec m)) -!leqRI (leqr_add2r `-1` (floor x) m).
Move=> H; Case: {H}(leqr_lt_trans H (ltrSr ?)).
By Rewrite: leqRI -(rwR (znatr_inc m)) -leqRI /znatR; Apply: ubr_sup; Auto; Split.
Qed.

Remark hasr_lb_floor_set : (x : R) (hasr (floor_set x)).
Proof.
Move=> x; Case: (leqr_total `0` x); LeftBy Exists (znatr R (Znat 0)); Split.
Move=> Hx; Step Hnx: (has_supr (floor_set `-x`)).
  Split; Auto; Exists (znatr R (Znat 0)); Split.
  By IP; Rewrite: leqRI /= -(rwR oppr0) -leqRI (leqr_opp2 `0` x).
Case: (supr_total `(floor (-x)) - 1` Hnx); RightBy Case/(ltPrr ?).
Case; Auto; Move=> y [m _] Hm {y}; Pose m1 := (incz m); Pose m2 := (incz m1).
Exists (znatr R (oppz m2)); Split; Move: Hm.
Rewrite: -/znatR !leqRI -{m}decz_inc -/m1 (rwR (znatr_dec m1)).
Rewrite: (rwR (znatr_opp m2)) -(rwR (oppr_opp x)) -!leqRI.
Rewrite: (leqr_add2r `-1` (floor `-x`) m1) (leqr_opp2 m2 `-x`).
Rewrite: -(leqr_add2r `1` (floor `-x`) m1) leqRI -(rwR (znatr_inc m1)) -leqRI.
By Apply: leqr_trans; Apply ltrW; Apply hasr_floor_max; Case Hnx.
Qed.
Hints Resolve hasr_lb_floor_set.

Lemma has_supr_floor_set : (x : R) (has_supr (floor_set x)). Proof. By Split. Qed.
Hints Resolve has_supr_floor_set.

Add Morphism ((!floor ?) :: RR -> RR) : floor_morphism.
Proof.
Move=> x x' Dx; Apply: supr_morphism; LeftBy Split.
By Move=> y; Split; Case=> [m Hm] {y}; Split; Apply: (leqr_trans Hm); Case Dx.
Qed.

Add Morphism floorR : floorR_morphism.
Proof. Unlock floorR; Exact floor_morphism. Qed.

Add Morphism range1R : range1r_morphism.
Proof.
Move=> x1 y1 x2 y2 Dx1 Dx2.
By Rewrite: /range1R /range1r !leqRI !addRI (rwR Dx1) (rwR Dx2).
Qed.

Lemma range1r_floor : (x : R) (range1r (floor x) x).
Proof. By Move=> x; Split; [Apply: leqr_sup_ub | Apply hasr_floor_max]. Qed.

Lemma znat_floor : (x : R) (EX m : znat | `(floor x) = m`).
Proof.
Move=> x; Case: (range1r_floor x); Pose y := (floor x); Move=> Hyx Hxy.
Pose h2 := `1/2%R`; Step Hh2: `0 < h2` By Apply: posr_inv.
Step Hyh2: `y - h2 < y`.
  Rewrite: (leqr_0sub y `y - h2`) leqRI (rwR `(addrC y - h2 (-y))`).
  By Rewrite: (rwR (addr_inv y `-h2`)) -(rwR oppr0) -leqRI (leqr_opp2 `0` h2).
Case: (supr_total `y - h2` (has_supr_floor_set x)) => [Hy2]; RightBy Case: Hyh2.
Case: Hy2 => [z [m Hmx] Hym] {z}; Rewrite: -/znatR in Hmx Hym; Exists m.
Split; RightBy Apply: ubr_sup; Auto; Rewrite: /znatR; Split.
Apply: leqr_sup_ub; Auto; Move=> z' [m' Hm'] {z'}.
Apply: znatr_leqP; Rewrite: -leqz_inc2; Apply/znatr_ltP.
Pose m1 := `m + h2`; Step Hym1: `y <= m1`.
  IP; Rewrite: -(leqr_add2r `-h2` y m1); Apply: (leqr_trans Hym); Apply eqr_leq.
  Rewrite: eqRI /m1 addRI (rwR (addrC m `h2`)) -addRI.
  By Rewrite: (rwR (addrC `h2 + m` `-h2`)) (rwR (addr_inv h2 m)).
Move: {}Hh2; Rewrite: -(leqr_add2l m1 h2 `0`) leqRI (rwR (addr0 m1)).
Rewrite: {1}/m1 -(rwR (addrA m h2 h2)) addRI -(rwR (mul2r h2)) /h2.
Rewrite: (rwR (divrr (gtr_neq ltr02))) -addRI -(rwR (znatr_inc m)) -leqRI.
By Apply: leqr_lt_trans; Apply: (ubr_geq_sup ? Hym1) => //; Rewrite: /znatR; Split.
Qed.

Lemma range1z_inj : (x : R; m1, m2 : znat)
  (range1r m1 x) -> (range1r m2 x) -> m1 = m2.
Proof.
Move=> x; Cut (m1, m2 : znat) (range1r m1 x) -> (range1r m2 x) -> (leqz m1 m2).
  By Move=> Hle m1 m2 Hm1 Hm2; Apply: eqP; Rewrite: eqz_leq !Hle.
Move=> m1 m2 [Hm1 _] [_ Hm2]; Rewrite: -leqz_inc2; Apply/znatr_ltP.
Rewrite: leqRI (rwR (znatr_inc m2)) -leqRI; EApply leqr_lt_trans; EAuto.
Qed.

Lemma range1zz : (m : znat) (range1r m m).
Proof.
Move=> m; Split; Auto; Rewrite: leqRI -(rwR (znatr_inc m)) -leqRI.
Apply: znatr_ltP; Apply leqzz.
Qed.

Lemma range1z_floor : (m : znat; x : R) (range1r m x) <-> `(floor x) = m`.
Proof.
Step Hlr: (m : znat; x : R) `(floor x) = m` -> (range1r m x).
  By Move=> m x Dm; Rewrite: range1RI -(rwR Dm); Apply: range1r_floor.
Move=> m x; Split; Auto; Case: (znat_floor x) => [m' Dm'] Hm.
By Case: (range1z_inj (Hlr ? ? Dm') Hm).
Qed.

Lemma floor_znat : (m : znat) `(floor m) = m`.
Proof. By Move=> m; IP; Rewrite: -(range1z_floor m m); Apply: range1zz. Qed.

Lemma find_range1z : (x : R) (EX m : znat | (range1r m x)).
Proof.
Move=> x; Case: (znat_floor x) => [m Hm]; Exists m; Case (range1z_floor m x); Auto.
Qed.

Lemma fracr_dense : (x, y : R) `x < y` -> (EX f : frac | `x < f` & `f < y`).
Proof.
Move=> x y Hxy; Pose z := `y - x`.
Step Hz: `z > 0`.
  By Rewrite: leqRI -(rwR (subrr x)) -leqRI /z (leqr_add2r `-x` y x).
Case: (find_range1z `1/z`) => [[d|m] [Hdz Hzd]].
  Pose dd := ((S d)::R); Step Hdd: `dd > 0` By Apply: ltr0Sn.
  Case: (find_range1z `dd * x`) => [m [Hmx Hxm]].
  Def Df': f' := (Frac d (incz m)); Exists f'.
    Rewrite: -(leqr_pmul2l f' x Hdd) {1}/dd leqRI -(rwR (fracr_eq Df')).
    By Rewrite: (rwR (znatr_inc m)) -leqRI.
  Rewrite: -(leqr_pmul2l y f' Hdd) {2}/dd leqRI -(rwR (fracr_eq Df')).
  Rewrite: mulRI -(rwR (addr_inv x y)) (rwR (addrC `-x` `x + y`)).
  Rewrite: -(rwR (addrA x y `-x`)) -/z -mulRI (rwR (znatr_inc m)).
  Rewrite: (rwR (mulr_addr dd x z)) -leqRI; Move: Hmx.
  Rewrite: -(leqr_add2r `dd * z` m `dd * x`); Apply: ltr_leq_trans.
  Rewrite: (leqr_add2l  m `dd * z` `1`).
  Rewrite: leqRI -(rwR (divrr (gtr_neq Hz))) (rwR (mulrC dd z)) -leqRI.
  By Rewrite: (leqr_pmul2l dd::RR `1/z` Hz) leqRI /dd (rwR (natr_S d)) -leqRI.
Case Hzd; Apply ltrW; Apply: leqr_lt_trans (posr_inv Hz).
Rewrite: leqRI -(rwR (znatr_inc (Zneg m))) -leqRI.
By Apply: (znatr_leqPx ? (Znat 0)); Case m.
Qed.

(**********************************************************)
(*   The excluded middle, and lemmas that depend on       *)
(* explicit classical reasoning.                          *)
(**********************************************************)

Lemma reals_classic : excluded_middle.
Proof.
Move=> P; Pose E := [x : R](`0` == x \/ P /\ `2` == x).
Step HhiE: (hasr (ubr E)) By Exists `2%R`; Move=> x [[] | [_ []]] //; Apply ltrW.
Step HE: (has_supr E) By Split; LeftBy Exists `0%R`; Left.
Case: (supr_total `1` HE) => [HE1].
  By Left; Case: HE1 => [x [[] | [HP _]]] // *; Case ltr01.
Right; Move=> HP; Case: (ltrSr `1`); Apply: leqr_trans HE1.
By Apply ubr_sup; RightBy Right; Split.
Qed.

(* Deciding comparisons. *)

Lemma leqr_eqVlt : (x1, x2 : R) `x1 <= x2` <-> `x1 = x2` \/ `x1 < x2`.
Proof.
Move=> x1 x2; Rewrite: /eqr.
Case: (reals_classic `x1 >= x2`) (leqr_total x1 x2); Tauto.
Qed.

Lemma ltr_neqAle : (x1, x2 : R) `x1 < x2` <-> `x1 <> x2` /\ `x1 <= x2`.
Proof. Move=> x1 x2; Rewrite: (leqr_eqVlt x1 x2) /eqr; Tauto. Qed.

(* Deciding definition by cases. *)

Lemma selr_cases : (P : Prop; x1, x2 : R) (pickr_spec P ~P x1 x2 (selr P x1 x2)).
Proof. Move=> P x1 x2; Apply: pickr_cases; Try Tauto; Apply reals_classic. Qed.

Add Morphism ((!selr ?) :: Prop -> RR -> RR -> RR) : selr_morphism.
Proof.
Move=> P Q x1 y1 x2 y2 DP Dx1 Dx2; Apply: (pickr_morphism ? ? ?); Try Tauto.
Apply: reals_classic.
Qed.

Add Morphism selR : selR_morphism. Proof. Unlock selR; Exact selr_morphism. Qed.

End RealLemmas.

Implicits neqr10 [].
Implicits ltr01 [].
Implicits ltr02 [].
Implicits ltrSr [1].
Implicits ltPrr [1].
Implicits ltr0Sn [].

Unset Implicit Arguments.


