(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require tacticext.
Require natprop.
Require seq.
Require cfmap.
Require cfreducible.
Require configurations.
Require job589to610.
Require job611to617.
Require job618to622.
Require job623to633.

Lemma red588to633 : (reducible_in_range (588) (633) the_configs).
Proof.
CatReducible red588to610 red610to617 red617to622 red622to633.
Qed.

