(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require tacticext.
Require natprop.
Require seq.
Require cfmap.
Require cfreducible.
Require configurations.

Lemma red226to230 : (reducible_in_range (226) (230) the_configs).
Proof. CheckReducible. Qed.

