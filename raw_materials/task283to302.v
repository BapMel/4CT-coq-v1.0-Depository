(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require tacticext.
Require natprop.
Require seq.
Require cfmap.
Require cfreducible.
Require configurations.
Require job283to286.
Require job287to290.
Require job291to294.
Require job295to298.
Require job299to302.

Lemma red282to302 : (reducible_in_range (282) (302) the_configs).
Proof.
CatReducible red282to286 red286to290 red290to294 red294to298 red298to302.
Qed.

