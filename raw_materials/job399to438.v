(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require tacticext.
Require natprop.
Require seq.
Require cfmap.
Require cfreducible.
Require configurations.

Lemma red398to438 : (reducible_in_range (398) (438) the_configs).
Proof. CheckReducible. Qed.

