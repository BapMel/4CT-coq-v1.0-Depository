(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require tacticext.
Require natprop.
Require seq.
Require cfmap.
Require cfreducible.
Require configurations.

Lemma red294to298 : (reducible_in_range (294) (298) the_configs).
Proof. CheckReducible. Qed.

