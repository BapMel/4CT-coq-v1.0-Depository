(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require tacticext.
Require natprop.
Require seq.
Require cfmap.
Require cfreducible.
Require configurations.

Lemma red306to310 : (reducible_in_range (306) (310) the_configs).
Proof. CheckReducible. Qed.

