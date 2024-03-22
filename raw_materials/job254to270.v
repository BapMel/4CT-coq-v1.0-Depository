(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require tacticext.
Require natprop.
Require seq.
Require cfmap.
Require cfreducible.
Require configurations.

Lemma red253to270 : (reducible_in_range (253) (270) the_configs).
Proof. CheckReducible. Qed.

