(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require tacticext.
Require natprop.
Require seq.
Require cfmap.
Require cfreducible.
Require configurations.

Lemma red106to164 : (reducible_in_range (106) (164) the_configs).
Proof. CheckReducible. Qed.

