(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require tacticext.
Require natprop.
Require seq.
Require cfmap.
Require cfreducible.
Require configurations.

Lemma red238to253 : (reducible_in_range (238) (253) the_configs).
Proof. CheckReducible. Qed.

