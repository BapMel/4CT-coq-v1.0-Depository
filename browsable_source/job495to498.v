(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require tacticext.
Require natprop.
Require seq.
Require cfmap.
Require cfreducible.
Require configurations.

Lemma red494to498 : (reducible_in_range (494) (498) the_configs).
Proof. CheckReducible. Qed.

