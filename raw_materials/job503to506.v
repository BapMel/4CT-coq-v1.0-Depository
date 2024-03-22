(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require tacticext.
Require natprop.
Require seq.
Require cfmap.
Require cfreducible.
Require configurations.

Lemma red502to506 : (reducible_in_range (502) (506) the_configs).
Proof. CheckReducible. Qed.

