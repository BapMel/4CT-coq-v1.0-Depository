(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require tacticext.
Require natprop.
Require seq.
Require cfmap.
Require cfreducible.
Require configurations.
Require job323to383.
Require job384to398.
Require job399to438.
Require job439to465.
Require job466to485.

Lemma red322to485 : (reducible_in_range (322) (485) the_configs).
Proof.
CatReducible red322to383 red383to398 red398to438 red438to465 red465to485.
Qed.

