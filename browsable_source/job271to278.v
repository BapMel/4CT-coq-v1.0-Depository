(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require tacticext.
Require natprop.
Require seq.
Require cfmap.
Require cfreducible.
Require configurations.

Lemma red270to278 : (reducible_in_range (270) (278) the_configs).
Proof. CheckReducible. Qed.

