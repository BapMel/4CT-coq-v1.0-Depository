(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require tacticext.
Require natprop.
Require seq.
Require cfmap.
Require cfreducible.
Require configurations.

Lemma red214to218 : (reducible_in_range (214) (218) the_configs).
Proof. CheckReducible. Qed.

