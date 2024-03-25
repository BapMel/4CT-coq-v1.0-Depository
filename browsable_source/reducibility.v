(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require tacticext.
Require natprop.
Require seq.
Require cfmap.
Require cfreducible.
Require configurations.
Require present.
Require task001to214.
Require task215to234.
Require task235to282.
Require task283to302.
Require task303to322.
Require task323to485.
Require task486to506.
Require task507to541.
Require task542to588.
Require task589to633.

Lemma the_reducibility : reducibility.
Proof.
Rewrite: /reducibility.
CatReducible red000to214 red214to234 red234to282 red282to302 red302to322
             red322to485 red485to506 red506to541 red541to588 red588to633.
Qed.

