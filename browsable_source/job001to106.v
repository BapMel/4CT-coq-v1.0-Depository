(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require tacticext.
Require natprop.
Require seq.
Require cfmap.
Require cfreducible.
Require configurations.

Lemma red000to106 : (reducible_in_range (0) (106) the_configs).
Proof. CheckReducible. Qed.

