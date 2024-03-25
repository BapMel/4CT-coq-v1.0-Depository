(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require tacticext.
Require natprop.
Require seq.
Require cfmap.
Require cfreducible.
Require configurations.

Lemma red516to530 : (reducible_in_range (516) (530) the_configs).
Proof. CheckReducible. Qed.

