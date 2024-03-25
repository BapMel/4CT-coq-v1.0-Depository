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
Require coloring.
Require birkhoff.
Require znat.
Require part.
Require discharge.
Require hubcap.
Require configurations.
Require present.
Require present5.
Require present6.
Require present7.
Require present8.
Require present9.
Require present10.
Require present11.

Set Implicit Arguments.

Lemma unavoidability : reducibility ->
  (g : hypermap) ~(minimal_counter_example g).
Proof.
Move=> Hred g Hg; Case: (posz_dscore Hg) => [x Hx].
Step Hgx: (valid_hub x) By Split.
Move: (Hg::(pentagonal g) x); Rewrite: 7!leq_eqVlt leqNgt.
Rewrite: exclude5 ?exclude6 ?exclude7 ?exclude8 ?exclude9 ?exclude10 ?exclude11 //.
Case/idP; Apply: (!dscore_cap1 g (5)) => // [y] {x n Hn Hx Hgx}.
Pose x := (inv_face2 y); Pose n := (arity x).
Step []: (face (face x)) = y By Rewrite: /x /inv_face2 !Enode.
Rewrite: (dbound1_eq (DruleFork (DruleForkValues n))) // leqz_nat.
Case Hn: (negb (Pr58 n)); LeftBy Rewrite: source_drules_range //.
Def: Hrp := (no_fit_the_redpart 1!the_quiz_tree Hred Hg).
Apply: (check_dbound1P Hrp ? (exact_fitp_pcons_ Hg x)) => //.
Rewrite: -/n; Move: n Hn; Do 9 Case=> //.
Qed.

Unset Implicit Arguments.
