(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require tacticext.
Require natprop.
Require seq.
Require cfmap.
Require cfreducible.
Require configurations.

Lemma red489to494 : (reducible_in_range (489) (494) the_configs).
Proof. CheckReducible. Qed.

