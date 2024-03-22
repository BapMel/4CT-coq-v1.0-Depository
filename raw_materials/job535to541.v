(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require tacticext.
Require natprop.
Require seq.
Require cfmap.
Require cfreducible.
Require configurations.

Lemma red534to541 : (reducible_in_range (534) (541) the_configs).
Proof. CheckReducible. Qed.

