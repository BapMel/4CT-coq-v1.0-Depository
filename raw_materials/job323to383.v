(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require tacticext.
Require natprop.
Require seq.
Require cfmap.
Require cfreducible.
Require configurations.

Lemma red322to383 : (reducible_in_range (322) (383) the_configs).
Proof. CheckReducible. Qed.

