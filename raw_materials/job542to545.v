(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require tacticext.
Require natprop.
Require seq.
Require cfmap.
Require cfreducible.
Require configurations.

Lemma red541to545 : (reducible_in_range (541) (545) the_configs).
Proof. CheckReducible. Qed.

