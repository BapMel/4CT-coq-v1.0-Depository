(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require tacticext.
Require natprop.
Require seq.
Require cfmap.
Require cfreducible.
Require configurations.

Lemma red610to617 : (reducible_in_range (610) (617) the_configs).
Proof. CheckReducible. Qed.

