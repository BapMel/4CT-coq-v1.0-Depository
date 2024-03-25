(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require tacticext.
Require natprop.
Require seq.
Require cfmap.
Require cfreducible.
Require configurations.
Require job303to306.
Require job307to310.
Require job311to314.
Require job315to318.
Require job319to322.

Lemma red302to322 : (reducible_in_range (302) (322) the_configs).
Proof.
CatReducible red302to306 red306to310 red310to314 red314to318 red318to322.
Qed.

