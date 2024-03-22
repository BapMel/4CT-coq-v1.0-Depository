(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require tacticext.
Require natprop.
Require seq.
Require cfmap.
Require cfreducible.
Require configurations.
Require job542to545.
Require job546to549.
Require job550to553.
Require job554to562.
Require job563to588.

Lemma red541to588 : (reducible_in_range (541) (588) the_configs).
Proof.
CatReducible red541to545 red545to549 red549to553 red553to562 red562to588.
Qed.

