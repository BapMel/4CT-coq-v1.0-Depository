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
Require cube.
Require present.
Require unavoidability.
Require reducibility.

Set Implicit Arguments.

Theorem four_color_hypermap :
  (g : hypermap) (planar_bridgeless g) -> (four_colorable g).
Proof.
Move=> g Hg; Apply cube_colorable.
Step Hqg: (planar_bridgeless_plain_precubic (cube g)).
  Split; RightBy Apply cubic_precubic; Apply cubic_cube.
  Split; RightBy Apply plain_cube.
  Split; [Rewrite planar_cube | Rewrite bridgeless_cube]; Exact Hg.
Pose n := (S (card (cube g))); Move: Hqg (leqnn n); Rewrite: {1}/n.
Elim: {g Hg}n (cube g) => // [n Hrec] g Hg Hgn.
Rewrite: ltnS leq_eqVlt in Hgn; Case/orP: Hgn; Auto.
Move/eqP=> Dn; Rewrite: -~{n}Dn in Hrec.
Case: (decide_colorable g) => [Hkg]; LeftDone.
Case: (!unavoidability the_reducibility g); Split; Auto.
Qed.

Unset Implicit Arguments.
