(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require tacticext.
Require natprop.
Require seq.
Require cfmap.
Require cfreducible.
Require configurations.

Lemma red498to502 : (reducible_in_range (498) (502) the_configs).
Proof. CheckReducible. Qed.

