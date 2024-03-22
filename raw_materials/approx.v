(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require tacticext.
Require boolprop.
Require funs.
Require dataset.
Require natprop.
Require seq.
Require paths.
Require hypermap.
Require geometry.
Require coloring.
Require znat.
Require grid.
Require matte.
Require real.
Require realmap.
Require realsyntax.
Require Setoid.
Require realprop.

Set Implicit Arguments.

Section ApproxMap.

(*   Approximations of real scalar, points, regions and rectangles, used for *)
(* casting the continuous four color problem into a combinatorial form.      *)
(*   Because the grid decomposition is based on dichotomy, we choose to      *)
(* approximate the real coordinates with binary decimals (i.e., floating     *)
(* nubers, rather than arbitrary rationals.                                  *)

Variable R : real_model.

Syntactic Definition point := (point R).
Syntactic Definition region := (region R).
Syntactic Definition map := (map R).
Syntactic Definition rect := (rect R).
Syntactic Definition interval := (interval R).

(* Because of the limitations of Coq v7 Setoid tactics, we need to repeat *)
(* some of the boilerplate from file realprop.v. here.                    *)

(* patch for v7.3.1 Setoid Prop rewrite at root bug *)
Local xProp [P : Prop] : Prop := P.
Remark xPropE : (P : Prop) (xProp P) -> P. Proof. Done. Qed.
Add Morphism xProp : dedekind_xProp_morphism. Proof. Tauto. Qed.
Tactic Definition IP := Apply xPropE.

Local RR : Type := R.
Local isR [x : RR] : RR := x.
Local leqR : RR -> RR -> Prop := (locked (!leqr ?)).
Local eqR : RR -> RR -> Prop := (!eqr ?).
Local addR : RR -> RR -> RR := (locked (!addr ?)).
Local oppR : RR -> RR := (locked (!oppr ?)).
Local mulR : RR -> RR -> RR := (locked (!mulr ?)).
Local selR : Prop -> RR -> RR -> RR := (locked (!selr ?)).
Local minR : RR -> RR -> RR := (locked (!minr ?)).
Local maxR : RR -> RR -> RR := (locked (!maxr ?)).
Local range1R : RR -> RR -> Prop := (!range1r ?).
Coercion Local natR := (!natr R).
Coercion Local znatR := (!znatr R).

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

Lemma range1RI : (x1, x2 : R) (range1r x1 x2) == (range1R (isR x1) (isR x2)).
Proof. Done. Qed.

Add Setoid RR eqR (eqr_theory R).

Hints Unfold eqR.

Remark eqR_refl : (x : R) (eqR x x). Proof. Apply: (!eqr_refl). Qed.
Hints Resolve eqr_refl eqR_refl leqrr ltrW ltr01 ltr02.

Syntactic Definition ltr01 := (ltr01 R).
Syntactic Definition ltr02 := (ltr02 R).
Syntactic Definition znatr_leqP := (znatr_leqPx R ? ?).
Syntactic Definition znatr_ltP := (znatr_ltPx R ? ?).

Add Morphism isR : discrmap_isr_morphism. Proof. Done. Qed.

Add Morphism leqR : discrmap_leqr_morphism. Proof. Exact (!leqR_morphism ?). Qed.

Add Morphism addR : discrmap_addr_morphism. Proof. Exact (!addR_morphism ?). Qed.

Add Morphism oppR : discrmap_oppr_morphism. Proof. Exact (!oppR_morphism ?). Qed.

Add Morphism mulR : discrmap_mulr_morphism. Proof. Exact (!mulR_morphism ?). Qed.

Add Morphism minR : discrmap_minr_morphism.
Proof. Unlock minR; Exact (!minr_morphism ?). Qed.

Add Morphism maxR : discrmap_maxr_morphism.
Proof. Unlock maxR; Exact (!maxr_morphism ?). Qed.

Add Morphism selR : discrmap_selR_morphism.
Proof. Unlock selR; Exact (!selr_morphism ?). Qed.

Add Morphism range1R : discrmap_range1r_morphism.
Proof. Exact (!range1r_morphism ?). Qed.

(* Real powers of 2, for scaling approximations.                          *)

Fixpoint exp2 [s : nat] : R := if s is (S s') then `2 * (exp2 s')` else `1`.

Lemma leqr1exp2 : (s : nat) `1 <= (exp2 s)`.
Proof.
Elim=> [|s]; [Apply leqrr | Rewrite: -(leqr_pmul2l `1` (exp2 s) ltr02) /=].
Apply: leqr_trans; Rewrite: leqRI (rwR (mulr1 `2`)) -leqRI.
By Apply: (znatr_leqPx ? (Znat 1) (Znat 2)).
Qed.

Lemma ltr0exp2 : (s : nat) `0 < (exp2 s)`.
Proof. Move=> s; Apply: (ltr_leq_trans ltr01); Apply leqr1exp2. Qed.
Implicits ltr0exp2 [].

Lemma exp2_add : (s1, s2 : nat) `(exp2 (addn s1 s2)) = (exp2 s1) * (exp2 s2)`.
Proof.
Move=> s1 s2; Elim: s1 => [|s1 Hrec] /=.
  By Rewrite: eqRI (rwR (mul1r (exp2 s2))).
Rewrite: eqRI mulRI addnI (rwR Hrec) -mulRI; Apply: mulrA.
Qed.

Lemma leq_exp2 : (s1, s2 : nat) (leq s1 s2) -> `(exp2 s1) <= (exp2 s2)`.
Proof.
Move=> s1 s2 Hs12; Rewrite: -(leq_add_sub Hs12); Move: {s2 Hs12}(subn s2 s1) => s2.
Rewrite: leqRI -(rwR (mulr1 (exp2 s1))) (rwR (exp2_add s1 s2)) -leqRI.
IP; Rewrite: (leqr_pmul2l `1` (exp2 s2) (ltr0exp2 s1)); Apply: leqr1exp2.
Qed.

Lemma ltr1exp2S : (s : nat) `1 < (exp2 (S s))`.
Proof.
Move=> s; Apply: ltr_leq_trans (leq_exp2 (ltn0Sn s)).
Rewrite: /= leqRI (rwR (mulr1 `2`)) -leqRI; Apply: ltrSr.
Qed.
Implicits ltr1exp2S [].

(* Scalar decimal approximation.                                       *)

Definition approx [s : nat; x : RR; m : znat] : Prop :=
  (range1r m `(exp2 s) * x`).

Add Morphism approx : approx_morphism.
Proof. By Move=> s x y m Dx; Rewrite: /approx range1RI !mulRI Dx. Qed.

Lemma approxI : (s : nat; x : R) (approx s x) == (approx s (isR x)).
Proof. Done. Qed.

Lemma approx_inj : (s : nat; x : R; m1, m2 : znat)
  (approx s x m1) -> (approx s x m2) -> m1 = m2.
Proof. Move=> s x; Apply: (!range1z_inj). Qed.

Lemma approx_exists : (s : nat; x : R) (EX m | (approx s x m)).
Proof. By Move=> s x; Apply: find_range1z. Qed.

Definition scale [s : nat; m : znat] : R := `m / (exp2 s)`.

Lemma approx_scale : (s : nat; m : znat) (approx s (scale s m) m).
Proof.
Move=> s m; Rewrite: /approx /scale range1RI.
Rewrite: (rwR (mulrCA (exp2 s) m `1 / (exp2 s)`)).
Rewrite: mulRI (rwR (divrr (gtr_neq (ltr0exp2 s)))) -mulRI.
Rewrite: (rwR (mulr1 m)); Apply: range1zz.
Qed.

Lemma approx_halfz : (s : nat; x : R; m : znat)
  (approx (S s) x m) -> (approx s x (halfz m)).
Proof.
Rewrite: /approx /=; Move/exp2=> y x m; Rewrite: range1RI -(rwR (mulrA `2` y x)).
Move: {y x}`y * x` => x; Rewrite: /range1R /range1r /isR !leqRI !addRI /znatR.
Rewrite: (rwR (znatr_addbit ? m)) -/znatR -/natR -!addRI -!leqRI.
Move/halfz: m (oddz m) => m b [Hxm Hmx].
Rewrite: -(leqr_pmul2l m x ltr02) -(leqr_pmul2l `m+1` x ltr02); Split.
  Apply: leqr_trans Hxm; Rewrite: leqRI -(rwR (add0r `2*m`)) -leqRI. 
  IP; Rewrite: `(leqr_add2r 2 * m 0 b)`; Apply: leqr0n.
Apply: (ltr_leq_trans Hmx); Rewrite: leqRI `(rwR (mulr_addr 2 m 1))`.
Rewrite: (addRI `2 * m`) (rwR (mulr1 `2`)) -addRI `(rwR (addrCA 2 * m 1 1))`.
Rewrite: -`(rwR (addrA b 2 * m 1))` -leqRI.
IP; Rewrite: `(leqr_add2r 2 * m + 1 b 1)` /xProp; Case: {}b => /=; Auto.
Qed.

Lemma scale_exists : (x : R) `0 < x` -> (EX s | `1 < (exp2 s) * x`).
Proof.
Move=> x Hx; Case: (find_range1z `1/x`) => [[s|s'] [_]].
  Rewrite: /= -/natR -`(leqr_pmul2l s + 1 1/x Hx)` leqRI.
  Rewrite: (rwR (divrr (gtr_neq Hx))) /natR mulRI -(rwR (natr_S ? s)) -/natR.
  Rewrite: -mulRI -leqRI; Move=> Hs.
  Exists s; Elim: s x Hx Hs => [|s Hrec] x Hx Hs /=.
    By Rewrite: leqRI `(rwR (mulrC 1 x))` -leqRI.
  Rewrite: leqRI -`(rwR (mulrA 2 (exp2 s) x))`.
  Rewrite: `(rwR (mulrCA 2 (exp2 s) x))` -leqRI; Apply Hrec.
    By Rewrite: leqRI -(rwR (mulr0 `2`)) -leqRI `(leqr_pmul2l x 0 ltr02)`.
  Apply: (ltr_leq_trans Hs); Rewrite: leqRI -(rwR `(mulrA 2 x (S s))`).
  Rewrite: (rwR `(mulrCA 2 x (S s))`) -leqRI.
  IP; Rewrite: `(leqr_pmul2l (S (S s)) 2 * (S s) Hx)`.
  Rewrite: leqRI (rwR `(mulr_addl (S s) 1 1)`) addRI (rwR (mul1r (S s))) -addRI.
  Rewrite: /natR (rwR (natr_S ? (S s))) -/natR -leqRI.
  IP; Rewrite: (leqr_add2l (S s) `1` (S s)).
  By Apply: (znatr_leqPx R (Znat 1) (Zpos (S s))) => /=; Rewrite leqz_nat.
Case; Apply ltrW; Apply: leqr_lt_trans (posr_inv Hx).
Rewrite: leqRI -/znatR (rwR `(addrC (Zneg s') 1)`).
Rewrite: addRI /znatR /znatr oppRI (rwR (natr_S ? s')) -/natR -oppRI.
Rewrite: (rwR (oppr_add s' `1`)) -addRI (rwR (addrCA `1` `-s'` `-1`)).
Rewrite: addRI (rwR (subrr `1`)) -addRI (rwR (addr0 `-s'`)) -(rwR (oppr0 ?)).
IP; Rewrite: -leqRI (leqr_opp2 s' `0`); Apply: leqr0n.
Qed.

Lemma approx_between : (s : nat; x1, x2 : R; m1, m2 : znat)
  (approx (S s) x1 m1) -> (approx (S s) x2 m2) ->
  `1 < (exp2 s) * (x2 - x1)` ->
  (EX m | (leqz (incz m1) m) & (leqz (incz m) m2)).
Proof.
Move=> s x1 x2 m1 m2; Pose s2 := (exp2 s); Pose z := `s2 * (x2 - x1)`.
Case: (approx_exists s `x1 + x2`) => [m]; Rewrite: /approx /= -/s2.
Pose y := `s2 * (x1 + x2)`.
Step Dx1: `2 * s2 * x1 = y - z`.
  Rewrite: eqRI -(rwR `(mulrA 2 s2 x1)`) (rwR `(mulrCA 2 s2 x1)`).
  Rewrite: mulRI (rwR `(mulr_addl x1 1 1)`) addRI (rwR (mul1r x1)).
  Rewrite: /y /z addRI -(rwR `(mulr_oppr s2 x2 - x1)`) !mulRI.
  Rewrite: (rwR (oppr_sub x2 x1)) -!mulRI -!addRI.
  Rewrite: -(rwR `(mulr_addr s2 x1 + x2 x1 - x2)`) !mulRI.
  Rewrite: (rwR `(addrCA x1+x2 x1 (-x2))`) 2!addRI.
  Rewrite: -(rwR (addrA x1 x2 `-x2`)) addRI (rwR (subrr x2)) -!addRI 2!addRI.
  By Rewrite: (rwR (addr0 x1)).
Step Dx2: `2 * s2 * x2 = y + z`.
  Rewrite: eqRI -(rwR `(mulrA 2 s2 x2)`) (rwR `(mulrCA 2 s2 x2)`).
  Rewrite: mulRI (rwR `(mulr_addl x2 1 1)`) addRI (rwR (mul1r x2)).
  Rewrite: /y /z -(rwR `(mulr_addr s2 x1 + x2 x2 - x1)`) !mulRI.
  Rewrite: (rwR `(addrCA x1+x2 x2 (-x1))`) addRI.
  Rewrite: -(rwR (addrA x1 x2 `-x1`)) (rwR (addrCA x1 x2 `-x1`)) addRI.
  By Rewrite: (rwR (subrr x1)) -!addRI 2!addRI (rwR (addr0 x2)).
Move=> [Hmy Hym]; Rewrite: range1RI (rwR Dx1) /isR ~{Dx1}; Move=> [Hm1 _].
Case=> [_]; Rewrite: leqRI -/znatR ~{Dx2}(rwR Dx2) -leqRI; Move=> Hm2 Hz.
Exists m; Apply/znatr_ltP; Rewrite: -/znatR.
  Apply: (leqr_lt_trans Hm1); Rewrite: -(leqr_add2l z m `y - z`) leqRI.
  Rewrite: (rwR (addrCA z y `-z`)) 2!addRI (rwR (subrr z)) -!addRI.
  Rewrite: (rwR (addr0 y)) (rwR (addrC z m)) -leqRI; Apply: (ltr_leq_trans Hym).
  By Apply ltrW; Rewrite: -/znatR (leqr_add2l m z `1`). 
Apply: (leqr_lt_trans Hmy); Rewrite: -(leqr_add2r z m2 y).
By Apply: (ltr_leq_trans Hm2); Apply ltrW; Rewrite: (leqr_add2l m2 z `1`).
Qed.

(* Geometrical binary approximation.                                   *)

Definition approx_point [s : nat; z : point; p : gpoint] : Prop :=
  let (x, y) = z in let (mx, my) = p in (approx s x mx) /\ (approx s y my).

Lemma approx_point_inj : (s : nat; z : point; p1, p2 : gpoint)
  (approx_point s z p1) -> (approx_point s z p2) -> p1 = p2.
Proof.
Move=> s [x y] [mx1 my1] [mx2 my2] [Hx1 Hy1] [Hx2 Hy2].
Congr Gpoint; EApply approx_inj; EAuto.
Qed.

Lemma approx_point_exists : (s : nat; z : point) (EX p | (approx_point s z p)).
Proof.
Move=> s [x y]; Case: (approx_exists s x) (approx_exists s y) => [mx Hmx] [my Hmy].
By Exists (Gpoint mx my); Split.
Qed.

Definition scale_point [s : nat; p : gpoint] : point :=
  let (mx, my) = p in (Point (scale s mx) (scale s my)).

Lemma approx_scale_point : (s : nat; p : gpoint)
  (approx_point s (scale_point s p) p).
Proof. Move=> s [mx my]; Split; Apply approx_scale. Qed.

Lemma approx_halfg : (s : nat; z : point; p : gpoint)
  (approx_point (S s) z p) -> (approx_point s z (halfg p)).
Proof. By Move=> s [x y] [mx my] [Hx Hy]; Split; Apply approx_halfz. Qed.

Syntactic Definition gpset := (set gpointData).

Definition mem_approx [s : nat; gr : gpset] : region :=
  [z](EX p | (approx_point s z p) & (gr p)).

Lemma sub_mem_approx : (s : nat; gr1, gr2 : gpointset)
  (sub_set gr1 gr2) -> (subregion (mem_approx s gr1) (mem_approx s gr2)).
Proof. Move=> s gr1 gr2 Hgr12 z [p Dp Hp]; Exists p; Auto. Qed.

Lemma mem_approx_scale : (s : nat; gr : gpset; p : gpoint)
  (reflect (mem_approx s gr (scale_point s p)) (gr p)).
Proof.
Move=> s gr p; Apply: (iffP idP) => [Hp | [p' Dp' Hp']].
  By Exists p; LeftBy Apply approx_scale_point.
By Rewrite: (approx_point_inj (approx_scale_point ? ?) Dp').
Qed.

Lemma mem_approx_refine1_rect : (s : nat; b : grect; z : point)
  (mem_approx (S s) (refine_rect b) z) <-> (mem_approx s b z).
Proof.
Move=> s b z; Split; Move=> [p Dp Hp].
  By Exists (halfg p); [Apply approx_halfg | Rewrite: -mem_refine_rect].
Case: (approx_point_exists (S s) z) => [p' Dp']; Exists p'; LeftDone.
By Rewrite: mem_refine_rect (approx_point_inj (approx_halfg Dp') Dp).
Qed.

Lemma mem_approx_refine_rect : (s, s' : nat; b : grect; z : point)
  (mem_approx (addn s s') (iter s refine_rect b) z) <-> (mem_approx s' b z).
Proof.
Move=> s s' b z; Elim: s => //= [|s Hrec]; LeftBy Split.
Rewrite: -Hrec addSn; Apply mem_approx_refine1_rect.
Qed.

Lemma mem_approx_refine1_matte : (s : nat; mm : matte; z : point)
  (mem_approx (S s) (refine_matte mm) z) <-> (mem_approx s mm z).
Proof.
Move=> s mm z; Split; Move=> [p Dp Hp].
  By Exists (halfg p); [Apply approx_halfg | Rewrite: -mem_refine_matte].
Case: (approx_point_exists (S s) z) => [p' Dp']; Exists p'; LeftDone.
By Rewrite: mem_refine_matte (approx_point_inj (approx_halfg Dp') Dp).
Qed.

Lemma mem_approx_refine_matte : (s, s' : nat; mm : matte; z : point)
  (mem_approx (addn s s') (iter s refine_matte mm) z) <-> (mem_approx s' mm z).
Proof.
Move=> s s' b z; Elim: s => //= [|s Hrec]; LeftBy Split.
Rewrite: -Hrec addSn; Apply: mem_approx_refine1_matte.
Qed.

Lemma mem_approx_inset2 : (s : nat; b : grect)
  (subregion (mem_approx s (inset b)) (mem_approx (S s) (inset2 (refine_rect b)))).
Proof.
Move=> s b z [p Dp Hp].
Case: (approx_point_exists (S s) z) => [p' Dp']; Exists p'; LeftDone.
By Apply inset2_refine; Rewrite: (approx_point_inj (approx_halfg Dp') Dp).
Qed.

Lemma mem_approx_inset1 : (s : nat; b : grect)
  (subregion (mem_approx s (inset b)) (mem_approx (S s) (inset (refine_rect b)))).
Proof.
By Move=> s r z; Case/mem_approx_inset2=> [p Dp Hp]; Case/andP: Hp; Exists p.
Qed.

Lemma mem_approx_inset : (s, s' : nat; b : grect)
  (subregion (mem_approx s' (inset b))
             (mem_approx (addn s s') (inset (iter s refine_rect b)))).
Proof.
Move=> s s' b z; Elim: s => [|s Hrec] //= Hz; Rewrite: addSn.
Apply: mem_approx_inset1; Auto.
Qed.

Lemma approx_rect : (z : point; r : rect) (r z) ->
  (EX s | (EX b | (mem_approx s (inset b) z) & (subregion (mem_approx s b) r))).
Proof.
Move=> [x y] [[xx zx] [xy zy]] [Hrx Hry].
Step [s [Hsxx Hszx] [Hsxy Hszy]]: (EX s |
    `1 < (exp2 s) * (x - xx)` /\ `1 < (exp2 s) * (zx - x)`
  & `1 < (exp2 s) * (y - xy)` /\ `1 < (exp2 s) * (zy - y)`).
  Case Hrx; Rewrite: (leqr_sub0 x xx) (leqr_sub0 zx x).
  Move/scale_exists=> [s1 Hs1]; Move/scale_exists=> [s2 Hs2].
  Case Hry; Rewrite: (leqr_sub0 y xy) (leqr_sub0 zy y).
  Move/scale_exists=> [s3 Hs3]; Move/scale_exists=> [s4 Hs4].
  Step Hleql: (n1, n2, n3 : nat) (leq n1 n2) -> (leq n1 (addn n2 n3)).
    Move=> n1 n2 n3 Hn12; Apply: (leq_trans Hn12); Apply leq_addr.
  Step Hleqr: (n1, n2, n3 : nat) (leq n1 n3) -> (leq n1 (addn n2 n3)).
    Move=> n1 n2 n3 Hn13; Apply: (leq_trans Hn13); Apply leq_addl.
  Step Hleqs: (n1, n2 : nat; u : R)
    `1 < (exp2 n1) * u` -> (leq n1 n2) ->`1 < (exp2 n2) * u`.
    Move=> n1 n2 u Hu1 Hn12.
    Step Hu: `0 < u`.
      Rewrite: -(leqr_pmul2l u `0` (ltr0exp2 n1)) leqRI (rwR (mulr0 (exp2 n1))).
      By Rewrite: -leqRI; Apply: ltr_trans Hu1.
    Apply: (ltr_leq_trans Hu1).
    Rewrite: leqRI (rwR (mulrC (exp2 n1) u)) (rwR (mulrC (exp2 n2) u)) -leqRI.
    By Move/leq_exp2: Hn12; Rewrite: (leqr_pmul2l (exp2 n1) (exp2 n2) Hu).
  Move: leqnn; Exists (addn (addn s1 s2) (addn s3 s4)); Split; EApply Hleqs; EAuto.
Case: (approx_exists (S s) x)  (approx_exists (S s) y)  => [mx Dmx]   [my Dmy].
Case: (approx_exists (S s) xx) (approx_exists (S s) xy) => [mxx Dmxx] [mxy Dmxy].
Case: (approx_exists (S s) zx) (approx_exists (S s) zy) => [mzx Dmzx] [mzy Dmzy].
Case: (approx_between Dmxx Dmx) => // [nxx Hnxx Hnxxx].
Case: (approx_between Dmx Dmzx) => // [nzx Hxnzx Hnzx].
Case: (approx_between Dmxy Dmy) => // [nxy Hnxy Hnxyy].
Case: (approx_between Dmy Dmzy) => // [nzy Hynzy Hnzy].
Rewrite leqz_inc_dec in Hnxxx; Rewrite leqz_inc_dec in Hnxyy.
Exists (S s); Exists (Grect nxx nzx nxy nzy).
  By Exists (Gpoint mx my); Try Apply/and4P; Split.
Step Hap: (u, v : R; nu, nv : znat) (approx (S s) u nu) -> (approx (S s) v nv) ->
          (leqz (incz nu) nv) -> `u < v`.
  Rewrite: /approx; Move=> u v nu nv [_ Hnu] [Hnv _] Huv.
  Rewrite: -(leqr_pmul2l v u (ltr0exp2 (S s))).
  Apply: (ltr_leq_trans Hnu); Apply: leqr_trans Hnv.
  By Rewrite: leqRI /znatR -(rwR (znatr_inc ? nu)) -leqRI; Apply: znatr_leqP.
Move=> [x' y'] [[mx' my'] [Dmx' Dmy']]; Move/and4P=> [Hmxxx' Hx'mzx Hmxyy' Hy'mzy].
By Split; Split; EApply Hap; EAuto; EApply leqz_trans; EAuto; Rewrite leqz_inc2.
Qed.

Lemma rect_approx : (s : nat; z : point; p : gpoint) (approx_point s z p) ->
  (EXT r : rect | (r z) & (subregion r (mem_approx s (ltouch p)))).
Proof.
Move=> s [x y] [mx my] [H H']; Case: H'; Case: H; Pose s1 := (exp2 s).
Step Hs1: `0 < s1` By Apply: ltr0exp2.
Step Es1: (u : R) `s1 * (u / s1) = u`.
  Move=> u; Rewrite: eqRI (rwR (mulrCA s1 u `1/s1`)) mulRI.
  By Rewrite: (rwR (divrr (gtr_neq Hs1))) -mulRI (rwR (mulr1 u)).
Move=> Hmxx Hxmx Hmyy Hymy.
Pose int_pm1 := [m : znat]`(Interval (m - 1) / s1 (m + 1) / s1)`.
Exists (Rect (int_pm1 mx) (int_pm1 my)).
  Split; Split.
   Rewrite: -(leqr_pmul2l x `(mx - 1) / s1` Hs1) leqRI (rwR (Es1 `mx - 1`)).
    Rewrite: /znatR -(rwR (znatr_dec ? mx)) -/znatR -leqRI.
    By Apply: ltr_leq_trans Hmxx; Apply: znatr_ltP; Rewrite: incz_dec leqzz.
   Rewrite: -(leqr_pmul2l `(mx + 1) / s1` x Hs1) leqRI (rwR (Es1 `mx + 1`)).
    By Rewrite: -leqRI.
   Rewrite: -(leqr_pmul2l y `(my - 1) / s1` Hs1) leqRI (rwR (Es1 `my - 1`)).
    Rewrite: /znatR -(rwR (znatr_dec ? my)) -/znatR -leqRI.
    By Apply: ltr_leq_trans Hmyy; Apply: znatr_ltP; Rewrite: incz_dec leqzz.
   Rewrite: -(leqr_pmul2l `(my + 1) / s1` y Hs1) leqRI (rwR (Es1 `my + 1`)).
   By Rewrite: -leqRI.
Move=> [x' y'] [H H']; Case: H'; Case: H.
Rewrite: -`(leqr_pmul2l x' (mx - 1) / s1 Hs1)` leqRI (rwR (Es1 `mx - 1`)).
  Rewrite: /znatR -(rwR (znatr_dec ? mx)) -/znatR -leqRI; Move=> Hmxx'.
Rewrite: -`(leqr_pmul2l (mx + 1) / s1 x' Hs1)` leqRI (rwR (Es1 `mx + 1`)).
  Rewrite: -leqRI; Move=> Hx'mx.
Rewrite: -`(leqr_pmul2l y' (my - 1) / s1 Hs1)` leqRI (rwR (Es1 `my - 1`)).
  Rewrite: /znatR -(rwR (znatr_dec ? my)) -/znatR -leqRI; Move=> Hmyy'.
Rewrite: -`(leqr_pmul2l (my+1) / s1 y' Hs1)` leqRI (rwR (Es1 `my + 1`)).
  Rewrite: -leqRI; Move=> Hy'my.
Case: (approx_point_exists s (Point x' y')) => [p' Hp']; Exists p'; Auto.
Case: p' Hp' => [mx' my'] [H H']; Case: H'; Case: H; Rewrite: -/s1.
Move=> Hmx'x Hxmx' Hmy'y Hymy'; Apply/and4P; Split;
   Rewrite: -leqz_inc2; Apply/znatr_ltP; Rewrite: leqRI /znatR;
   Rewrite: ?(rwR (znatr_inc ? mx')) ?(rwR (znatr_inc ? mx));
   Rewrite:  ?(rwR (znatr_inc ? my')) ?(rwR (znatr_inc ? my)) -/znatR -leqRI;
   EApply leqr_lt_trans; EAuto; EApply ltr_trans; EAuto.
Qed.

(* Some rectangle operations.                                                   *)

Definition cap_interval [xz1, xz2 : interval] : interval :=
  let (x1, z1) = xz1 in let (x2, z2) = xz2 in
  (Interval (maxr x1 x2) (minr z1 z2)).

Lemma mem_cap_interval : (xz1, xz2 : interval; y : R)
  (xz1 y) /\ (xz2 y) <-> (cap_interval xz1 xz2 y).
Proof.
Move=> [x1 z1] [x2 z2] y /=; Rewrite: (ltr_max x1 x2 y) (ltr_min z1 z2 y); Tauto.
Qed.

Definition cap_rect [r1, r2 : rect] : rect :=
   let (xint1, yint1) = r1 in let (xint2, yint2) = r2 in
   (Rect (cap_interval xint1 xint2) (cap_interval yint1 yint2)).

Lemma mem_cap_rect : (r1, r2 : rect; p : point)
  (r1 p) /\ (r2 p) <-> (cap_rect r1 r2 p).
Proof.
Move=> [xint1 yint1] [xint2 yint2] [px py] /=.
Rewrite: -(mem_cap_interval xint1 xint2 px) -(mem_cap_interval yint1 yint2 py).
Tauto.
Qed.

Definition sep_interval [x, z : R] : interval :=
  let y = `(x + z) / 2` in
  (Interval (selr `z <= y` `z - 1` y) (selr `y <= z` `z + 1` y)).

Lemma mem_sep_interval : (x, y : R) (sep_interval x y y).
Proof.
Move=> x y; Rewrite: /sep_interval; Move: {x}`(x + y) / 2` => x; Split.
  Case: (selr_cases `y <= x` `y - 1` x) => [z].
  Case=> [[Hz Dz]]; Rewrite: leqRI (rwR Dz) -leqRI //; Apply ltPrr.
Case: (selr_cases `x <= y` `y + 1` x) => [z].
Case=> [[Hz Dz]]; Rewrite: leqRI (rwR Dz) -leqRI //; Apply ltrSr.
Qed.

Lemma meet_sep_interval : (x, y, t : R)
  (sep_interval x y t) -> (sep_interval y x t) -> `x = y`.
Proof.
Cut (t, x, y : R) (sep_interval x y t) -> (sep_interval y x t) -> `x <= y`.
  By Move=> Hle x y t *; Split; Apply: (Hle t).
Move=> t x y Hxyt Hyxt; Case: (reals_classic R `x <= y`) => // [Hyx].
Case: Hyxt; Case: Hxyt.
Rewrite: !selRI !mulRI !leqRI  (rwR (addrC y x)) -!mulRI -!leqRI -!selRI. 
Pose z := `(x + y) / 2`; Step Ez2: `2 * z = x + y`.
  Rewrite: /z eqRI (rwR `(mulrCA 2 x + y 1/2)`) mulRI.
  Rewrite: (rwR (divrr (gtr_neq ltr02))) -mulRI; Apply: mulr1.
Step [Hyz Hzx]: `y < z` /\ `z < x`.
  Rewrite: -(leqr_pmul2l z y ltr02) -(leqr_pmul2l x z ltr02) !leqRI (rwR Ez2).
  Rewrite: (rwR (mul2r x)) (rwR (mul2r y)) -!leqRI.
  By Rewrite: (leqr_add2l x x y) (leqr_add2r y x y); Split.
Clear; Case: (selr_cases `z <= y` `y + 1` z) => [z'].
Case=> [[Hz _] | [_ Dz']]; LeftBy Case Hyz.
Rewrite: leqRI ~{z' Dz'}(rwR Dz') -leqRI; Move=> Hzt.
Case: (selr_cases `x <= z` `x - 1` z) => [z'].
Case=> [[Hz _] | [_ Dz']]; LeftBy Case Hzx.
By Rewrite: leqRI ~{z' Dz'}(rwR Dz') -leqRI; Case; Apply ltrW.
Qed.

Definition sep_rect [z1, z2 : point] : rect :=
  let (x1, y1) = z1 in let (x2, y2) = z2 in
  (Rect (sep_interval x1 x2) (sep_interval y1 y2)).

Lemma mem_sep_rect : (z1, z2 : point) (sep_rect z1 z2 z2).
Proof. By Move=> [x1 y1] [x2 y2] /=; Split; Apply mem_sep_interval. Qed.

Lemma meet_sep_rect : (z1, z2 : point)
  (meet (sep_rect z1 z2) (sep_rect z2 z1)) -> (rr : rect) (rr z1) -> (rr z2).
Proof.
Move=> [x1 y1] [x2 y2] [[x y] [[Hx12 Hy12] [Hx21 Hy21]]] [[t1 t2] [t3 t4]] Hrz1.
Rewrite: /= !leqRI -(rwR (meet_sep_interval Hx12 Hx21)).
By Rewrite: -(rwR (meet_sep_interval Hy12 Hy21)) -!leqRI.
Qed.

End ApproxMap.

Unset Implicit Arguments.


