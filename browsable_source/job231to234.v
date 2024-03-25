(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require tacticext.
Require natprop.
Require seq.
Require cfmap.
Require cfreducible.
Require configurations.

Lemma red230to234 : (reducible_in_range (230) (234) the_configs).
Proof. CheckReducible. Qed.

