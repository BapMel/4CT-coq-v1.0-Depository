(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require tacticext.
Require natprop.
Require seq.
Require cfmap.
Require cfreducible.
Require configurations.

Lemma red206to214 : (reducible_in_range (206) (214) the_configs).
Proof. CheckReducible. Qed.

