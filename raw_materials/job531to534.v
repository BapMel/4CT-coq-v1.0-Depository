(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require tacticext.
Require natprop.
Require seq.
Require cfmap.
Require cfreducible.
Require configurations.

Lemma red530to534 : (reducible_in_range (530) (534) the_configs).
Proof. CheckReducible. Qed.

