(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require tacticext.
Require natprop.
Require seq.
Require cfmap.
Require cfreducible.
Require configurations.

Lemma red314to318 : (reducible_in_range (314) (318) the_configs).
Proof. CheckReducible. Qed.

