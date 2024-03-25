(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require tacticext.
Require natprop.
Require seq.
Require cfmap.
Require cfreducible.
Require configurations.

Lemma red562to588 : (reducible_in_range (562) (588) the_configs).
Proof. CheckReducible. Qed.

