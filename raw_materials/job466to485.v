(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require tacticext.
Require natprop.
Require seq.
Require cfmap.
Require cfreducible.
Require configurations.

Lemma red465to485 : (reducible_in_range (465) (485) the_configs).
Proof. CheckReducible. Qed.

