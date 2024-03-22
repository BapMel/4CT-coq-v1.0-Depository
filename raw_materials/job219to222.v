(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require tacticext.
Require natprop.
Require seq.
Require cfmap.
Require cfreducible.
Require configurations.

Lemma red218to222 : (reducible_in_range (218) (222) the_configs).
Proof. CheckReducible. Qed.

