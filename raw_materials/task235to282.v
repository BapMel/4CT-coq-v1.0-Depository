(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require tacticext.
Require natprop.
Require seq.
Require cfmap.
Require cfreducible.
Require configurations.
Require job235to238.
Require job239to253.
Require job254to270.
Require job271to278.
Require job279to282.

Lemma red234to282 : (reducible_in_range (234) (282) the_configs).
Proof.
CatReducible red234to238 red238to253 red253to270 red270to278 red278to282.
Qed.

