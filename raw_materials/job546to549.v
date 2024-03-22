(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require tacticext.
Require natprop.
Require seq.
Require cfmap.
Require cfreducible.
Require configurations.

Lemma red545to549 : (reducible_in_range (545) (549) the_configs).
Proof. CheckReducible. Qed.

