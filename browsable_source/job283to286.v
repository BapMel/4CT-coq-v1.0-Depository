(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require tacticext.
Require natprop.
Require seq.
Require cfmap.
Require cfreducible.
Require configurations.

Lemma red282to286 : (reducible_in_range (282) (286) the_configs).
Proof. CheckReducible. Qed.

