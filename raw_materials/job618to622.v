(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require tacticext.
Require natprop.
Require seq.
Require cfmap.
Require cfreducible.
Require configurations.

Lemma red617to622 : (reducible_in_range (617) (622) the_configs).
Proof. CheckReducible. Qed.

