(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require tacticext.
Require natprop.
Require seq.
Require cfmap.
Require cfreducible.
Require configurations.

Lemma red286to290 : (reducible_in_range (286) (290) the_configs).
Proof. CheckReducible. Qed.

