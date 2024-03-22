(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require tacticext.
Require natprop.
Require seq.
Require cfmap.
Require cfreducible.
Require configurations.
Require job507to510.
Require job511to516.
Require job517to530.
Require job531to534.
Require job535to541.

Lemma red506to541 : (reducible_in_range (506) (541) the_configs).
Proof.
CatReducible red506to510 red510to516 red516to530 red530to534 red534to541.
Qed.

