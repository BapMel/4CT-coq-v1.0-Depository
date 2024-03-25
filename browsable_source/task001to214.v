(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require tacticext.
Require natprop.
Require seq.
Require cfmap.
Require cfreducible.
Require configurations.
Require job001to106.
Require job107to164.
Require job165to189.
Require job190to206.
Require job207to214.

Lemma red000to214 : (reducible_in_range (0) (214) the_configs).
Proof.
CatReducible red000to106 red106to164 red164to189 red189to206 red206to214.
Qed.

