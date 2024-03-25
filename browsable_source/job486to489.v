(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require tacticext.
Require natprop.
Require seq.
Require cfmap.
Require cfreducible.
Require configurations.

Lemma red485to489 : (reducible_in_range (485) (489) the_configs).
Proof. CheckReducible. Qed.

