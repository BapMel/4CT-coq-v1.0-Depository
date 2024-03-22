(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require tacticext.
Require natprop.
Require seq.
Require cfmap.
Require cfreducible.
Require configurations.

Lemma red549to553 : (reducible_in_range (549) (553) the_configs).
Proof. CheckReducible. Qed.

