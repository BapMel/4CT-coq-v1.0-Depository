(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require tacticext.
Require natprop.
Require seq.
Require cfmap.
Require cfreducible.
Require configurations.

Lemma red506to510 : (reducible_in_range (506) (510) the_configs).
Proof. CheckReducible. Qed.

