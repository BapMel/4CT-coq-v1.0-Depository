(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require tacticext.
Require natprop.
Require seq.
Require cfmap.
Require cfreducible.
Require configurations.
Require job486to489.
Require job490to494.
Require job495to498.
Require job499to502.
Require job503to506.

Lemma red485to506 : (reducible_in_range (485) (506) the_configs).
Proof.
CatReducible red485to489 red489to494 red494to498 red498to502 red502to506.
Qed.

