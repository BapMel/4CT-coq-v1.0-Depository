(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require tacticext.
Require natprop.
Require seq.
Require cfmap.
Require cfreducible.
Require configurations.

Lemma red189to206 : (reducible_in_range (189) (206) the_configs).
Proof. CheckReducible. Qed.

