(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require tacticext.
Require natprop.
Require seq.
Require cfmap.
Require cfreducible.
Require configurations.

Lemma red510to516 : (reducible_in_range (510) (516) the_configs).
Proof. CheckReducible. Qed.

