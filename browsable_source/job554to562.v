(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require tacticext.
Require natprop.
Require seq.
Require cfmap.
Require cfreducible.
Require configurations.

Lemma red553to562 : (reducible_in_range (553) (562) the_configs).
Proof. CheckReducible. Qed.

