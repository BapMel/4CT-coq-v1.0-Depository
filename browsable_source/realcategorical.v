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
Require realprop.

Set Implicit Arguments.

(* A proof that the real axiomatisation is categorical -- i.e., *)
(* that the result dedekind construction is essentially unique. *)

Section RealsCategorical.

(* patch for v7.3.1 Setoid Prop rewrite at root bug *)
Local xProp [P : Prop] : Prop := P.
Remark xPropE : (P : Prop) (xProp P) -> P. Proof. Done. Qed.
Add Morphism xProp : dedekind_xProp_morphism. Proof. Tauto. Qed.
Tactic Definition IP := Apply xPropE.

Hints Resolve eqr_refl leqrr.
Syntactic Definition fracr_leqP := fracr_leqPx | 3.
Syntactic Definition fracr_posP := fracr_posPx | 2.

Section RealMorphismLiftsAxioms.

(* A monomorphism lifts back the real axioms, and preserves the rationals *)

Variables R : real_structure; R' : real_model; phi : R -> R'.
Hypothesis Hphi : (real_structure_morphism phi).

Remark phi_leq : (x1, x2 : R) `(phi x1) <= (phi x2)` <-> `x1 <= x2`.
Proof. By Case Hphi. Qed.

Remark phi_leq_inj : (x1, x2 : R) `(phi x1) <= (phi x2)` -> `x1 <= x2`.
Proof. By Move=> x1 x2; Rewrite: (phi_leq x1 x2). Qed.

Lemma morphr_eq : (x1, x2 : R) `(phi x1) = (phi x2)` <-> `x1 = x2`.
Proof. Move=> x1 x2; Rewrite: /eqr (phi_leq x1 x2) (phi_leq x2 x1); Tauto. Qed.

Syntactic Definition phi_eq := morphr_eq.

Remark phi_eq_inj : (x1, x2 : R) `(phi x1) = (phi x2)` -> `x1 = x2`.
Proof. By Move=> x1 x2; Rewrite: (phi_eq x1 x2). Qed.

Remark phi_add : (x1, x2 : R) `(phi x1 + x2) = (phi x1) + (phi x2)`.
Proof. By Case Hphi. Qed.

Remark phi_opp : (x : R) `(phi (-x)) = -(phi x)`.
Proof. By Case Hphi. Qed.

Remark phi_mul : (x1, x2 : R) `(phi x1 * x2) = (phi x1) * (phi x2)`.
Proof. By Case Hphi. Qed.

Remark phi0 : `(phi 0) = 0`.
Proof. By Case Hphi. Qed.

Remark phi1 : `(phi 1) = 1`.
Proof. By Case Hphi. Qed.

Remark phi_leqrr : (x : R) `x <= x`.
Proof. Move=> x; Apply phi_leq_inj; Apply leqrr. Qed.

Remark phi_leqr_trans : (x1, x2, x3 : R)
  `x1 <= x2` -> `x2 <= x3` -> `x1 <= x3`.
Proof.
Move=> x1 x2 x3; Rewrite: -(phi_leq x1 x2) -(phi_leq x2 x3) -(phi_leq x1 x3).
Apply: (!leqr_trans).
Qed.

Lemma morphr_has_sup : (E : R -> Prop) (has_supr E) -> (has_supr (imager phi E)).
Proof.
Move=> E [[x Hx] [z Hz]]; Split; LeftBy Exists (phi x); Exists x.
By Exists (phi z); Move=> y' [y [] Hy] {y'}; IP; Rewrite: (phi_leq y z); Apply: Hz.
Qed.
Hints Resolve morphr_has_sup.

Remark phi_ubr_sup : (E : R -> Prop) (has_supr E) -> (ubr E `sup E`).
Proof.
Move=> E HE x Hx.
Step [_ HE'E]: `(phi (supr E)) = (supr (imager phi E))` By Case Hphi; Auto.
Apply phi_leq_inj; Apply: leqr_trans HE'E; Apply (supr_upper_bound R'); Auto.
By Exists x.
Qed.

Remark phi_leqr_total : (x1, x2 : R) `x1 <= x2` \/ `x2 <= x1`.
Proof.
Move=> x1 x2; Rewrite: -(phi_leq x1 x2) -(phi_leq x2 x1); Apply leqr_total.
Qed.

Remark phi_supr_total : (x : R; E : R -> Prop) (has_supr E) ->
  (boundedr x E) \/ `sup E <= x`.
Proof.
Move=> x E HE.
Step [HEE' _]: `(phi (supr E)) = (supr (imager phi E))` By Case Hphi; Auto.
Case: (supr_total (phi x) (morphr_has_sup HE)).
  By Move=> [y' [y [] Hy]]; Rewrite: (phi_leq x y); Move=> Hxy; Left; Exists y.
By Move/(leqr_trans HEE'); Rewrite: (phi_leq (supr E) x); Right.
Qed.

Remark phi_addr_monotony : (x1, x2, x3 : R)
  `x2 <= x3` -> `x1 + x2 <= x1 + x3`.
Proof.
Move=> x1 x2 x3 Hx23; Apply phi_leq_inj.
Case: (phi_add x1 x3) => [_]; Apply: leqr_trans.
Case: (phi_add x1 x2) => [H _]; Apply: (leqr_trans H) {H}.
By Apply (addr_monotony R'); IP; Rewrite (phi_leq x2 x3).
Qed.

Remark phi_mulr_monotony : (x1, x2, x3 : R)
  `0 <= x1` -> `x2 <= x3` -> `x1 * x2 <= x1 * x3`.
Proof.
Move=> x1 x2 x3 Hx1 Hx23; Apply phi_leq_inj.
Case: (phi_mul x1 x3) => [_]; Apply: leqr_trans.
Case: (phi_mul x1 x2) => [H _]; Apply: (leqr_trans H) {H}.
Apply (mulr_monotony R'); RightBy IP; Rewrite (phi_leq x2 x3).
Case: {}phi0 => [_ H]; Apply: (leqr_trans H) {H}.
By IP; Rewrite: `(phi_leq 0 x1)`.
Qed.

Remark phi_add0r : (x : R) `0 + x = x`.
Proof.
Move=> x; Apply phi_eq_inj; Apply: eqr_trans (add0r (phi x)).
Apply: (eqr_trans `(phi_add 0 x)`).
Apply addr_morphism; [Exact phi0 | Apply eqr_refl].
Qed.

Remark phi_addrC : (x1, x2 : R) `x1 + x2 = x2 + x1`.
Proof.
Move=> x1 x2; Apply phi_eq_inj; Apply: (eqr_trans (phi_add x1 x2)).
Apply: (eqr_trans (addrC ? ?)); Apply eqr_sym; Apply phi_add.
Qed.

Remark phi_addrA : (x1, x2, x3 : R) `x1 + (x2 + x3) = x1 + x2 + x3`.
Proof.
Move=> x1 x2 x3; Apply phi_eq_inj; Apply: (eqr_trans (phi_add ? ?)).
Apply: (eqr_trans ? (eqr_sym (phi_add ? ?))).
Apply: (eqr_trans (addr_morphism (eqr_refl ?) (phi_add ? ?))).
Apply: (eqr_trans ? (eqr_sym (addr_morphism (phi_add ? ?)  (eqr_refl ?)))).
Apply addrA.
Qed.

Remark phi_subrr : (x : R) `x - x = 0`.
Proof.
Move=> x; Apply phi_eq_inj; Apply: (eqr_trans (phi_add ? ?)).
Apply: (eqr_trans ? (eqr_sym phi0)); Apply: eqr_trans (subrr (phi x)).
By Apply addr_morphism; [Apply eqr_refl | Apply phi_opp].
Qed.

Remark phi_mulrC : (x1, x2 : R) `x1 * x2 = x2 * x1`.
Proof.
Move=> x1 x2; Apply phi_eq_inj; Apply: (eqr_trans (phi_mul x1 x2)).
Apply: (eqr_trans (mulrC ? ?)); Apply eqr_sym; Apply phi_mul.
Qed.

Remark phi_mulrA : (x1, x2, x3 : R) `x1 * (x2 * x3) = x1 * x2 * x3`.
Proof.
Move=> x1 x2 x3; Apply phi_eq_inj; Apply: (eqr_trans (phi_mul ? ?)).
Apply: (eqr_trans ? (eqr_sym (phi_mul ? ?))).
Apply: (eqr_trans (mulr_morphism (eqr_refl ?) (phi_mul ? ?))).
Apply: (eqr_trans ? (eqr_sym (mulr_morphism (phi_mul ? ?)  (eqr_refl ?)))).
Apply mulrA.
Qed.

Remark phi_mulr_addr : (x1, x2, x3 : R) `x1 * (x2 + x3) = x1 * x2 + x1 * x3`.
Proof.
Move=> x1 x2 x3; Apply phi_eq_inj; Apply: (eqr_trans (phi_mul ? ?)).
Apply: (eqr_trans ? (eqr_sym (phi_add ? ?))).
Apply: (eqr_trans (mulr_morphism (eqr_refl ?) (phi_add ? ?))).
Apply: (eqr_trans ? (eqr_sym (addr_morphism (phi_mul ? ?) (phi_mul ? ?)))).
Apply mulr_addr.
Qed.

Remark phi_mul1r : (x : R) `1 * x = x`.
Proof.
Move=> x; Apply phi_eq_inj; Apply: (eqr_trans (phi_mul ? ?)).
Apply: eqr_trans (mul1r (phi x)).
Apply mulr_morphism; [Exact phi1 | Apply eqr_refl].
Qed.

Lemma morphr_neq0 : (x : R) `x <> 0` -> `(phi x) <> 0`.
Proof.
By Move=> x H H'; Case: H; Apply phi_eq_inj; Apply: eqr_trans (eqr_sym phi0).
Qed.

Remark phi_divrr : (x : R) `x <> 0` -> `x / x = 1`.
Proof.
Move=> x Hx; Apply phi_eq_inj; Apply: (eqr_trans (phi_mul ? ?)).
Apply: (eqr_trans ? (eqr_sym phi1)); Apply: (eqr_trans ? (divrr (morphr_neq0 Hx))).
Apply mulr_morphism; [Apply eqr_refl | Case Hphi; Auto].
Qed.

Remark phi_neqr10 : `1 <> 0%R`.
Proof.
Rewrite: /= -`(phi_eq 1 0)`; Move=> H10; Case (neqr10 R').
Apply: eqr_trans {}phi0; Apply: eqr_trans H10; Apply eqr_sym; Exact phi1.
Qed.

Theorem real_morphism_lifts_axioms : (real_axioms R).
Proof.
Exact (RealAxioms phi_leqrr phi_leqr_trans phi_ubr_sup phi_supr_total
  phi_addr_monotony  phi_addrC phi_addrA phi_add0r phi_subrr
  phi_mulr_monotony phi_mulrC phi_mulrA phi_mulr_addr
  phi_mul1r phi_divrr phi_neqr10).
Qed.

Lemma morphr_nat : (n : nat) `(phi (natr R n)) = (natr R' n)`.
Proof.
Move=> [|n] /=; LeftBy Exact phi0.
Elim: n (`1`::R) (`1`::R') {}phi1 => [|n Hrec] x x' Dx' //=; Apply: Hrec.
By Apply: (eqr_trans (phi_add ? ?)); Apply addr_morphism; LeftBy Exact phi1.
Qed.

Lemma morphr_znat : (m : znat) `(phi (znatr R m)) = (znatr R' m)`.
Proof.
Move=> [n|n]; Rewrite: /znatr; LeftBy Apply morphr_nat.
Apply: (eqr_trans (phi_opp ?)); Apply oppr_morphism; Apply morphr_nat.
Qed.

Lemma morphr_frac : (f : frac) `(phi (fracr R f)) = (fracr R' f)`.
Proof.
Move=> [d m]; Apply: (eqr_trans (phi_mul ? ?)).
Apply: mulr_morphism; LeftBy Apply morphr_znat.
Pose dd := (natr R (S d)); Pose dd' := (natr R' (S d)).
Step Hdd': `dd' > 0` By Apply: ltr0Sn.
Step Edd': `(phi dd) = dd'` By Apply: morphr_nat.
Step Hdd: `(phi dd) > 0` By Apply: (ltr_leq_trans Hdd'); Case Edd'.
Apply: (pmulr_injl Hdd'); Apply eqr_sym.
Apply: (eqr_trans (divrr (gtr_neq Hdd'))).
Apply: (eqr_trans (eqr_sym (divrr (gtr_neq Hdd)))); Apply: (mulr_morphism Edd').
Step Hdd0: `dd <> 0`.
  Rewrite: -(phi_eq dd `0`); Move=> Hdd0; Case/gtr_neq: Hdd.
  By Apply: eqr_trans {}phi0.
Apply eqr_sym; Case Hphi; Auto.
Qed.

End RealMorphismLiftsAxioms.

(* The categorical structure of the models of the reals. *)

Theorem real_morphism_comp : (R, R' : real_structure; R'' : real_model)
  (phi1 : R -> R'; phi2 : R' -> R'')
  (real_structure_morphism phi1) -> (real_structure_morphism phi2) ->
  (real_structure_morphism [x](phi2 (phi1 x))).
Proof.
Move=> R R' R'' phi1 phi2 Hphi1 Hphi2; Move: phi1 {}phi2 Hphi1 {}Hphi2.
Pose R'S := (RealModel (real_morphism_lifts_axioms Hphi2)).
Rewrite: -{R'}/R'S; Move: {R' phi2 Hphi2}R'S => R' phi1 phi2 Hphi1 Hphi2.
Pose phi := [x](phi2 (phi1 x)).
Step Ephi: (x1 : R; x2 : R'; x3 : R'')
 `(phi1 x1) = x2` -> `(phi2 x2) = x3` -> `(phi x1) = x3`.
  Move=> x1 x2 x3 Dx1; Apply: eqr_trans; Case (morphr_eq Hphi2 (phi1 x1) x2); Auto.
Step Hsup: (E : ?) (has_supr E) -> `(phi (supr E)) = (supr (imager phi E))`.
  Move=> E HE; Apply: (Ephi ? ? ? (morphr_sup Hphi1 HE)).
  Pose E' := (imager phi1 E); Step HE': (has_supr E') By Apply: morphr_has_sup.
  Apply: (eqr_trans (morphr_sup Hphi2 HE')).
  Apply supr_morphism; LeftBy Apply morphr_has_sup.
  Move=> x''; Split; LeftBy Move=> [x' [] [x [] Hx]] {x' x''}; Exists x.
  By Move=> [x [] Hx]; Exists (phi1 x); RightBy Exists x.
Split; Auto.
  By Move=> x1 x2; Rewrite: -(morphr_leq Hphi1 x1 x2); Apply: (morphr_leq Hphi2).
  Exact [x1, x2](Ephi ? ? ? (morphr_add Hphi1 ? ?) (morphr_add Hphi2 ? ?)).
  Exact (Ephi ? ? ? (morphr_0 Hphi1) (morphr_0 Hphi2)).
  Exact [x](Ephi ? ? ? (morphr_opp Hphi1 ?) (morphr_opp Hphi2 ?)).
  Exact [x1, x2](Ephi ? ? ? (morphr_mul Hphi1 ? ?) (morphr_mul Hphi2 ? ?)).
  Exact (Ephi ? ? ? (morphr_1 Hphi1) (morphr_1 Hphi2)).
Move=> x Hx; Apply: (Ephi ? ? ? (morphr_inv Hphi1 Hx) (morphr_inv Hphi2 ?)).
By Apply: (morphr_neq0 Hphi1).
Qed.

Theorem real_morphism_id : (R : real_model) (real_structure_morphism [x : R]x).
Proof.
Move=> R; Split; Try Tauto; Auto; Move=> E HE; Apply supr_morphism; Auto.
By Move=> x; Split; [Exists x | Move=> [x' []]].
Qed.

Section CanonicalRealMorphism.

(* There is a (canonical) monomorphism between two real structures. *)

Variables R, R' : real_model.

Inductive morphr_segment [x : R] : R' -> Prop :=
  Morphr_segment : (f : frac) `(fracr R f) < x` -> 
    (morphr_segment x (fracr R' f)).

Local psi [x : R] : R' := `sup (morphr_segment x)`.

Remark psi_has_sup : (x : R) (has_supr (morphr_segment x)).
Proof.
Move=> x; Split.
  By Case: (fracr_dense (ltPrr x)) => [f _ Hfx]; Exists (fracr R' f); Split.
Case: (fracr_dense (ltrSr x)) => [f Hxf _].
Exists (fracr R' f); Move=> y [f' Hf'] {y}; Apply: fracr_leqP.
By Apply/(fracr_leqPx R ? ?); Apply ltrW; Apply: ltr_trans Hxf.
Qed.

Remark psi_is_ub : (x : R; f : frac)
  `(fracr R f) < x`  -> `(fracr R' f) < (psi x)`.
Proof.
Move=> x f; Move/fracr_dense=> [f' Hff' Hf'x].
Apply: (ltr_leq_trans (elimN fracr_leqP (introN fracr_leqP Hff'))).
By Case: (psi_has_sup x) => [_ Hhi]; Apply: (ubr_sup Hhi); Split.
Qed.

Remark psi_leq_ub : (x : R; y' : R')
  (ubr (morphr_segment x) y') -> `(psi x) <= y'`.
Proof. By Move=> x y'; Apply: leqr_sup_ub; Case: (psi_has_sup x). Qed.

Remark psi_frac : (f : frac) `(psi (fracr R f)) = (fracr R' f)`.
Proof.
Move=> f; Step Hf: `(psi (fracr R f)) <= (fracr R' f)`.
  Apply: psi_leq_ub => [y [f' Hf']] {y}; Apply: fracr_leqP.
  By Apply/(fracr_leqPx R ? ?); Apply ltrW.
Move: Hf; Rewrite: (leqr_eqVlt (psi (fracr R f)) (fracr R' f)).
Case; LeftDone; Case/fracr_dense=> [f' Hf'f Hff'].
Case: Hf'f; Apply ltrW; Apply psi_is_ub.
By Move/(fracr_leqPx R ? ?): (introN fracr_leqP Hff').
Qed.

Remark psi_leq : (x1, x2 : R) `(psi x1) <= (psi x2)` <-> `x1 <= x2`.
Proof.
Move=> x1 x2; Split; Move=> Hx12.
  Case: (reals_classic R `x1 <= x2`); LeftDone.
  Move/fracr_dense=> [f Hx2f Hfx1].
  Case/psi_is_ub: Hfx1; Apply: (leqr_trans Hx12).
  Apply: psi_leq_ub => [y [f' Hf']] {y}.
  Apply: fracr_leqP; Apply/(fracr_leqPx R ? ?).
  By Apply ltrW; Apply: ltr_trans Hx2f.
Apply: psi_leq_ub => [y [f Hf]] {y}.
By Apply ltrW; Apply psi_is_ub; Apply: ltr_leq_trans Hx12.
Qed.

Remark psi_eq : (x1, x2 : R) `(psi x1) = (psi x2)` <-> `x1 = x2`.
Proof.
Move=> x1 x2; Rewrite: /eqr (psi_leq x1 x2) (psi_leq x2 x1); Tauto.
Qed.

Remark psi_0 : `(psi 0) = 0`.
Proof.
Apply: eqr_trans (fracr0 R'); Apply: eqr_trans (psi_frac F0).
IP; Rewrite: (psi_eq `0` (fracr R F0)); Apply: eqr_sym; Apply: fracr0.
Qed.

Remark psi_pos : (x : R) `(psi x) <= 0` <-> `x <= 0`.
Proof.
Move=> x; Rewrite: -(psi_leq x `0`); Case: {}psi_0 {}leqr_trans.
Split; EAuto.
Qed.

Remark psi_opp : (x : R) `(psi (-x)) = -(psi x)`.
Proof.
Move=> x; Split.
  Apply: psi_leq_ub => [y [f Hf]] {y}.
  Case: (fracr_opp R' (oppf f)); Rewrite: oppf_opp.
  Move=> H _; Apply: (leqr_trans H) {H}.
  IP; Rewrite: (leqr_opp2 (fracr R' (oppf f)) (psi x)).
  Case: (psi_frac (oppf f)) => [H _]; Apply: leqr_trans H.
  IP; Rewrite: (psi_leq x (fracr R (oppf f))).
  Rewrite: -(leqr_opp2 (fracr R (oppf f)) x); Apply: leqr_trans (ltrW Hf).
  By Case (fracr_opp R (oppf f)); Rewrite oppf_opp.
Case: (reals_classic R `(psi (-x)) >= -(psi x)`); LeftDone.
Move/fracr_dense=> [f Hxf []]; Rewrite: -{f}oppf_opp.
Case: (fracr_opp R' (oppf f)) => [_]; Apply: leqr_trans.
IP; Rewrite: (leqr_opp2 (psi x) (fracr R' (oppf f))).
Apply: ltrW; Apply psi_is_ub; Rewrite: -(leqr_opp2 (fracr R (oppf f)) x).
Case: (fracr_opp R (oppf f)) => [H _]; Apply: ltr_leq_trans H.
Rewrite: oppf_opp -(psi_leq (fracr R f) `-x`).
By Apply: (ltr_leq_trans Hxf); Case: (psi_frac f).
Qed.

Remark psi_add : (x1, x2 : R) `(psi x1 + x2) = (psi x1) + (psi x2)`.
Proof.
Cut (x1, x2 : R) `(psi x1 + x2) <= (psi x1) + (psi x2)`.
  Move=> Hrec x1 x2; Split; Auto.
  IP; Rewrite: -`(leqr_add2r (psi (-x2)) (psi x1) + (psi x2) (psi x1 + x2))`.
  Apply: (leqr_trans ? (Hrec ? ?)); Apply leqr_trans with (psi x1).
    Apply: eqr_leq; Apply: (eqr_trans (eqr_sym (addrA ? ? ?))).
    Apply: (eqr_trans ? (eqr_trans (addrC ? ?) (add0r ?))).
    Apply addr_morphism; Auto; Apply: (eqr_trans ? (subrr (psi x2))).
    By Apply addr_morphism; RightBy Apply psi_opp.
  IP; Rewrite: (psi_leq x1 `x1 + x2 - x2`).
  Apply: eqr_leq; Apply: (eqr_trans ? (addrA ? ? ?)).
  Apply: (eqr_sym (eqr_trans ? (eqr_trans (addrC ? ?) (add0r ?)))).
  By Apply addr_morphism; RightBy Apply subrr.
Move=> x1 x2; Apply: psi_leq_ub => [y [f Hf]] {y}; Pose y1 := `(fracr R f) - x2`.
Step Hy : `y1 < x1`.
  Rewrite: -(leqr_add2r x2 x1 y1); Apply: leqr_lt_trans Hf; Apply eqr_leq.
  Apply: (eqr_trans (eqr_sym (addrA ? ? ?))); Apply: (eqr_trans (addrC ? ?)).
  Apply: (eqr_trans (eqr_sym (addrA ? ? ?))); Apply: addr_inv.
Case: (fracr_dense Hy) => [f1 Hy1f1 Hf1x1].
Pose f2 := (addf f (oppf f1)); Step Hf2: `(fracr R f2) < x2`.
  Case: (fracr_add R f (oppf f1)) => [H _]; Apply: (leqr_lt_trans H) {H}.
  Rewrite: -(leqr_add2l (fracr R f1) x2 `(fracr R f) + (fracr R (oppf f1))`).
  Apply leqr_lt_trans with (fracr R f).
    Apply eqr_leq; Apply: (eqr_trans (addrA ? ? ?)).
    Apply: (eqr_trans ? (addr_inv (fracr R f1) ?)).
    By Apply: (eqr_trans (addrC ? ?)); Apply addr_morphism; LeftBy Apply fracr_opp.
  Rewrite: -(leqr_add2r `-x2` `(fracr R f1) + x2` (fracr R f)).
  Apply: (ltr_leq_trans Hy1f1); Apply eqr_leq; Apply eqr_sym.
  Apply: (eqr_trans (eqr_sym (addrA ? ? ?)));  Apply: (eqr_trans (addrC ? ?)).
  Apply: (eqr_trans (eqr_sym (addrA ? ? ?)));  Apply: (eqr_trans (addrCA ? ? ?)).
  Apply addr_inv.
Apply leqr_trans with `(fracr R' f1) + (fracr R' f2)`.
  Case: (fracr_add R' f1 f2) => [H _]; Apply: leqr_trans H; Apply: fracr_leqP.
  By Rewrite: /f2 addfA addfC; Case/andP: (addf_inv f1 f).
Apply leqr_trans with `(psi x1) + (fracr R' f2)`; IP.
  Rewrite: (leqr_add2r (fracr R' f2) (fracr R' f1) (psi x1)).
  By Apply: ltrW; Apply psi_is_ub.
Rewrite: (leqr_add2l (psi x1) (fracr R' f2) (psi x2)).
By Apply: ltrW; Apply psi_is_ub.
Qed.

Remark psi_1 : `(psi 1) = 1`.
Proof.
Apply: eqr_trans (fracr1 R'); Apply: eqr_trans (psi_frac F1).
IP; Rewrite: (psi_eq `1` (fracr R F1)); Apply: eqr_sym; Apply: fracr1.
Qed.

Remark psi_pinv : (x : R) `x > 0` -> `(psi 1/x) = 1 / (psi x)`.
Proof.
Move=> x Hx; Step Hx': `(psi x) > 0` By Rewrite: (psi_pos x).
Split.
  Apply: psi_leq_ub => [y [f Hfx]] {y}.
  Case Hf: (negb (posf f)).
    By Apply: (leqr_trans (fracr_posPx R' ? Hf)); Apply ltrW; Apply posr_inv.
  Rewrite: -posf_inv in Hf; Move/negbEf: Hf => Hf.
  Move: (fracr_pinv R' Hf) (fracr_pinv R Hf); Rewrite: !invf_inv.
  Move=> [H _] [_ Hf'x]; Apply: (leqr_trans H) {H}.
  Move/(fracr_posPx R' ?): {}Hf => Hf'; Move/(fracr_posPx R ?): Hf => Hf.
  IP; Rewrite: (leqr_pinv2 Hf' Hx').
  Case: (psi_frac (invf f)) => [H _]; Apply: leqr_trans H.
  IP; Rewrite: (psi_leq x (fracr R (invf f))) -(leqr_pinv2 Hf Hx).
  By Apply: leqr_trans (ltrW Hfx).
Case: (reals_classic R `(psi 1/x) >= 1 / (psi x)`); LeftDone.
Move/fracr_dense=> [f Hxf []].
Step Hf: (posf (invf f)).
  Rewrite: posf_inv; Apply/(fracr_posPx R' ?); Apply: ltr_trans Hxf.
  By Rewrite: (psi_pos `1/x`); Apply posr_inv.
Move: (fracr_pinv R' Hf) (fracr_pinv R Hf); Rewrite: !invf_inv.
Move=> [_ H] [Hf'x _]; Apply: leqr_trans H; Apply ltrW.
Move/(fracr_posPx R' ?): {}Hf => Hf'; Move/(fracr_posPx R ?): Hf => Hf. 
Rewrite: (leqr_pinv2 Hf' Hx'); Apply psi_is_ub.
Rewrite: -(leqr_pinv2 Hf Hx); Apply: ltr_leq_trans Hf'x.
Rewrite: -(psi_leq (fracr R f) `1/x`); Apply: (ltr_leq_trans Hxf).
By Case: (psi_frac f).
Qed.

Remark psi_inv : (x : R) `x <> 0` -> `(psi 1/x) = 1 / (psi x)`.
Proof.
Move=> x; Case/ltr_total=> [Hx]; RightBy Apply psi_pinv.
Step Hx': `(psi x) <> 0`.
  Apply ltr_neq; Case: {}psi_0 => [H _]; Apply: ltr_leq_trans H.
  By Rewrite: (psi_leq `0` x).
Step Hnx: `-x > 0`.
  Case: (oppr0 R) => [_ H]; Apply: (leqr_lt_trans H) {H}.
  By Rewrite: (leqr_opp2 x `0`).
Step Hnx': `(psi (-x)) <> 0` By Apply gtr_neq; Rewrite: (psi_pos `-x`).
Apply oppr_inj; Apply: eqr_trans (invr_opp Hx').
Apply: eqr_trans (invr_morphism Hnx' (psi_opp x)); Apply: eqr_trans (psi_pinv Hnx).
Apply eqr_sym; Apply: (eqr_trans ? (psi_opp ?)).
By IP; Rewrite: (psi_eq `1/-x` `-(1/x)`); Apply: invr_opp; Apply ltr_neq.
Qed.

Remark psi_mul : (x1, x2 : R) `(psi x1 * x2) = (psi x1) * (psi x2)`.
Proof.
Move=> x1; Cut (x2 : R) `x2 > 0` -> `(psi x1 * x2) = (psi x1) * (psi x2)`.
  Move=> Hrec x2; Case: (reals_classic R `x2 = 0`) => [Hx2].
    Apply: (eqr_trans (eqr_trans ? psi_0)).
      IP; Rewrite: (psi_eq `x1 * x2` `0`).
      By Apply: (eqr_trans ? (mulr0 x1)); Apply mulr_morphism.
    Apply: (eqr_sym (eqr_trans (mulr_morphism (eqr_refl ?) ?) (mulr0 ?))).
    By Apply: (eqr_trans ? psi_0); IP; Rewrite: (psi_eq x2 `0`).
  Case/ltr_total: Hx2 => [Hx2]; Auto; Step Hnx2: `-x2 > 0`.
    Case: (oppr0 R) => [_ H]; Apply: (leqr_lt_trans H) {H}.
    By Rewrite: (leqr_opp2 x2 `0`).
  Apply oppr_inj; Apply: (eqr_trans ? (mulr_oppr ? ?)).
  Apply: (eqr_trans (eqr_sym (psi_opp ?))).
  Apply: (eqr_trans (eqr_trans ? (Hrec ? Hnx2))).
    IP; Rewrite: (psi_eq `-(x1 * x2)` `x1 * -x2`); Apply: eqr_sym.
    Apply mulr_oppr.
  By Apply mulr_morphism; RightBy Apply psi_opp.
Move=> x2 Hx2; Move: x1.
Cut (x1 : R) `x1 > 0` -> `(psi x1 * x2) = (psi x1) * (psi x2)`.
  Move=> Hrec x1; Case: (reals_classic R `x1 = 0`) => [Hx1].
    Apply: (eqr_trans (eqr_trans ? psi_0)).
      IP; Rewrite: (psi_eq `x1 * x2` `0`).
      By Apply: (eqr_trans ? (mul0r x2)); Apply mulr_morphism.
    Apply: (eqr_sym (eqr_trans (mulr_morphism ? (eqr_refl ?)) (mul0r ?))).
    By Apply: (eqr_trans ? psi_0); IP; Rewrite: (psi_eq x1 `0`).
  Case/ltr_total: Hx1 => [Hx1]; Auto; Step Hnx1: `-x1 > 0`.
    Case: (oppr0 R) => [_ H]; Apply: (leqr_lt_trans H) {H}.
    By Rewrite: (leqr_opp2 x1 `0`).
  Apply oppr_inj; Apply: (eqr_trans ? (mulr_oppl ? ?)).
  Apply: (eqr_trans (eqr_sym (psi_opp ?))).
  Apply: (eqr_trans (eqr_trans ? (Hrec ? Hnx1))).
    IP; Rewrite: (psi_eq `-(x1 * x2)` `-x1 * x2`); Apply: eqr_sym.
    Apply mulr_oppl.
  By Apply mulr_morphism; LeftBy Apply psi_opp.
Move: x2 Hx2; Cut (x1, x2 : R) `x1 > 0` -> `x2 > 0` ->
   `(psi x1 * x2) <= (psi x1) * (psi x2)`.
  Move=> Hrec x2 Hx2 x1 Hx1; Split; Auto.
  Step Hx1': `(psi x1) > 0` By Rewrite: (psi_pos x1).
  IP; Rewrite: -`(leqr_pmul2l (psi x1)*(psi x2) (psi x1*x2) (posr_inv Hx1'))`.
  Case: (pmulr_inv (psi x2) Hx1') => [H _]; Apply: (leqr_trans H) {H}.
  Move: Hx2; Rewrite: -(posr_pmull x2 Hx1); Move=> Hx12.
  Move: (pmulr_inv x2 Hx1); Rewrite: -(psi_eq `1/x1 * (x1 * x2)` x2).
  Move=> [_ H]; Apply: (leqr_trans H) {H}.
  Apply: (leqr_trans (Hrec ? ? (posr_inv Hx1) Hx12)); Apply eqr_leq.
  By Apply mulr_morphism; LeftBy Apply psi_pinv.
Move=> x1 x2 Hx1 Hx2.
Step Hx1': `(psi x1) > 0` By Rewrite: (psi_pos x1).
Step Hx2': `(psi x2) > 0` By Rewrite: (psi_pos x2).
Apply: psi_leq_ub => [y [f Hfx]] {y}; Pose y2 := `(fracr R f) / x1`.
Case Hf: (negb (posf f)).
  Apply: (leqr_trans (fracr_posP Hf)); Apply ltrW.
  By IP; Rewrite: (posr_pmull (psi x2) Hx1') (psi_pos x2).
Step Hy2 : `y2 < x2`.
  Rewrite: -(leqr_pmul2l x2 y2 Hx1); Apply: leqr_lt_trans Hfx; Apply eqr_leq.
  Apply: (eqr_trans (mulrA ? ? ?)); Apply: (eqr_trans (mulrC ? ?)).
  By Apply: pmulr_inv.
Case: (fracr_dense Hy2) => [f2 Hy2f2 Hf2x2].
Step Hf2: (posf f2).
  Move/(fracr_posPx R ?): Hf => Hf; Apply/(fracr_posPx R ?).
  Apply: ltr_trans Hy2f2.
  By IP; Rewrite: /y2 (posr_pmull  `1/x1` Hf); Apply: posr_inv.
Pose f1 := (mulf f (invf f2)); Step Hf1: `(fracr R f1) < x1`.
  Move/(fracr_posPx R ?): {}Hf2 => Hf2'.
  Rewrite: -(leqr_pmul2l x1 (fracr R f1) Hf2').
  Case: (fracr_mul R f2 f1) => [_ H]; Apply: (leqr_lt_trans H) {H}.
  Apply leqr_lt_trans with (fracr R f).
    By Apply: fracr_leqP; Rewrite: /f1 mulfA mulfC; Case/andP: (pmulf_inv f Hf2).
  Case: (mulrC (fracr R f2) x1) => [_]; Apply: ltr_leq_trans; Move: Hy2f2.
  Rewrite: -(leqr_pmul2l (fracr R f2) y2 Hx1); Apply: leqr_lt_trans.
  Apply eqr_leq; Apply eqr_sym; Apply: (eqr_trans (mulrA ? ? ?)).
  By Apply: (eqr_trans (mulrC ? ?)); Apply pmulr_inv.
Apply leqr_trans with `(fracr R' f1) * (fracr R' f2)`.
  Case: (fracr_mul R' f1 f2) => [H _]; Apply: leqr_trans H; Apply: fracr_leqP.
  By Rewrite: /f1 -mulfA mulfC -mulfA; Case/andP: (pmulf_inv f Hf2).
Apply leqr_trans with `(psi x1) * (fracr R' f2)`; IP.
  Move/(fracr_posPx R' ?): {}Hf2 => Hf2'.
  Case: (mulrC (psi x1) (fracr R' f2)) => [_]; Apply: leqr_trans.
  Case: (mulrC (fracr R' f1) (fracr R' f2)) => [H _]; Apply: (leqr_trans H){H}.
  IP; Rewrite: (leqr_pmul2l (fracr R' f1) (psi x1) Hf2').
  By Apply: ltrW; Apply psi_is_ub.
Rewrite: (leqr_pmul2l (fracr R' f2) (psi x2) Hx1').
By Apply: ltrW; Apply psi_is_ub.
Qed.
  
Remark psi_sup : (E : R -> Prop) (has_supr E) ->
  `(psi sup E) = sup (imager psi E)`.
Proof.
Move=> E HE; Step [HloE' HhiE']: (has_supr (imager psi E)).
  Case: HE => [[x Hx] [z Hz]]; Split; LeftBy Exists (psi x); Exists x.
  Exists (psi z); Move=> y' [y [] Hy] {y'}.
  By IP; Rewrite: (psi_leq y z); Apply: Hz.
Split.
  Apply: psi_leq_ub => [x' [f Hf]] {x'}.
  Case: (supr_total (fracr R f) HE); RightBy Tauto.
  Case: (psi_frac f) => [_ H] [x Hx Hfx]; Apply: (leqr_trans H) {H}; Move: Hfx.
  Rewrite: -(psi_leq (fracr R f) x); Move=> H; Apply: (leqr_trans H){H}.
  By Apply: (ubr_sup HhiE'); Exists x.
Apply: (leqr_sup_ub HloE') => [x' [x [] Hx]] {x'}.
By IP; Rewrite: (psi_leq x (supr E)); Apply: (supr_upper_bound R).
Qed.

Definition canonical_real_morphism : R -> R' := psi.

Theorem canonical_real_morphism_morphism :
  (real_structure_morphism canonical_real_morphism).
Proof.
Exact (RealStructureMorphism
  psi_leq psi_sup psi_add psi_0 psi_opp psi_mul psi_1 psi_inv).
Qed.

End CanonicalRealMorphism.

Syntactic Definition psi := (!canonical_real_morphism ?).
Syntactic Definition Hphi := (!real_structure_morphism ? ?).

Theorem real_morphism_uniq : (R : real_structure; R' : real_model)
  (phi1, phi2 : R -> R') (Hphi phi1) -> (Hphi phi2) ->
  (x : R) `(phi1 x) = (phi2 x)`.
Proof.
Move=> R R'; Cut (phi1, phi2 : R -> R'; x : R)
    (Hphi phi1) -> (Hphi phi2) -> `(phi1 x) <= (phi2 x)`.
  By Move=> *; Split; Auto.
Move=> phi1 phi2 x Hphi1 Hphi2.
Case: (reals_classic R' `(phi1 x) <= (phi2 x)`); Auto.
Move/fracr_dense=> [f Hxf []].
Case: (morphr_frac Hphi1 f) => [H _]; Apply: leqr_trans H; Apply ltrW.
Rewrite: (morphr_leq Hphi1 (fracr R f) x) -(morphr_leq Hphi2 (fracr R f) x).
By Apply: (ltr_leq_trans Hxf); Case: (morphr_frac Hphi2 f).
Qed.

Theorem inverse_canonical_real_morphism : (R, R' : real_model)
  (x : R) `(psi R (psi R' x)) = x`.
Proof.
Move=> R R'; Apply (!real_morphism_uniq ? ? [x](psi R (psi R' x)) [x]x).
  Apply: (!real_morphism_comp R R' R); Apply canonical_real_morphism_morphism.
Apply real_morphism_id.
Qed.

End RealsCategorical.

Unset Implicit Arguments.


