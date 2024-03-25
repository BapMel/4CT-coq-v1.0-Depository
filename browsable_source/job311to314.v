(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require tacticext.
Require natprop.
Require seq.
Require cfmap.
Require cfreducible.
Require configurations.

Lemma red310to314 : (reducible_in_range (310) (314) the_configs).
Proof. CheckReducible. Qed.

