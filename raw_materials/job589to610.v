(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require tacticext.
Require natprop.
Require seq.
Require cfmap.
Require cfreducible.
Require configurations.

Lemma red588to610 : (reducible_in_range (588) (610) the_configs).
Proof. CheckReducible. Qed.

