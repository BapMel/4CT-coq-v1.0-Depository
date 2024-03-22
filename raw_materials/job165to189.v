(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require tacticext.
Require natprop.
Require seq.
Require cfmap.
Require cfreducible.
Require configurations.

Lemma red164to189 : (reducible_in_range (164) (189) the_configs).
Proof. CheckReducible. Qed.

