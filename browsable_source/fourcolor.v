(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Arith.
Require real.
Require realmap.
Require combinatorial4ct.
Require discretize.
Require finitize.

Section FourColorTheorem.

Variable R : real_model.

Theorem four_color_finite : (m : (map R))
  (finite_simple_map m) -> (map_colorable (4) m).
Proof.
Exact [m; Hm] let (g, Hg, Hgm) = (discretize_to_hypermap Hm) in
      (Hgm (four_color_hypermap Hg)).
Qed.

Theorem four_color : (m : (map R))
  (simple_map m) -> (map_colorable (4) m).
Proof.
Exact (compactness_extension four_color_finite).
Qed.

End FourColorTheorem.

Unset Implicit Arguments.
