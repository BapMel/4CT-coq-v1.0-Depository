(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require tacticext.
Require natprop.
Require seq.
Require cfmap.
Require cfreducible.
Require configurations.

Lemma red234to238 : (reducible_in_range (234) (238) the_configs).
Proof. CheckReducible. Qed.

