(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require tacticext.
Require natprop.
Require seq.
Require cfmap.
Require cfreducible.
Require configurations.

Lemma red278to282 : (reducible_in_range (278) (282) the_configs).
Proof. CheckReducible. Qed.

