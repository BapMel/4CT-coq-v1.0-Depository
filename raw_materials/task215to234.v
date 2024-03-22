(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require tacticext.
Require natprop.
Require seq.
Require cfmap.
Require cfreducible.
Require configurations.
Require job215to218.
Require job219to222.
Require job223to226.
Require job227to230.
Require job231to234.

Lemma red214to234 : (reducible_in_range (214) (234) the_configs).
Proof.
CatReducible red214to218 red218to222 red222to226 red226to230 red230to234.
Qed.

