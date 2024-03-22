(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require tacticext.
Require natprop.
Require seq.
Require cfmap.
Require cfreducible.
Require configurations.

Lemma red318to322 : (reducible_in_range (318) (322) the_configs).
Proof. CheckReducible. Qed.

