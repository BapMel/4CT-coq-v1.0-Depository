(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Arith.
Require real.

Set Implicit Arguments.

Section RealMap.

Variable R : real_structure.

(* Elementary set theory for the plane. *)

Inductive point : Type := Point : (x, y : R) point.

Definition region : Type := point -> Prop.

Identity Coercion mem_region : region >-> FUNCLASS.

Definition union [r1, r2 : region] : region :=
  [z] (r1 z) \/ (r2 z).

Definition intersect [r1, r2 : region] : region :=
  [z] (r1 z) /\ (r2 z).

Definition nonempty [r : region] : Prop :=
  (EXT z | (r z)).

Definition subregion [r1, r2 : region] : Prop :=
  (z : point) (r1 z) -> (r2 z).

Definition meet [r1, r2 : region] : Prop :=
  (nonempty (intersect r1 r2)).

(* Maps are represented as relations; proper maps are partial equivalence *)
(* relations (PERs).                                                      *)

Definition map : Type := point -> region.

Identity Coercion mem_map : map >-> FUNCLASS.

Definition inmap [m : map] : region := [z](m z z).

Definition covers [m, m' : map] : Prop :=
  (z : point) (subregion (m z) (m' z)).

Definition size_at_most [n : nat; m : map] : Prop :=
  (EXT f | (z : point) (inmap m z) -> (EX i | (lt i n) & (m (f i) z))).

Record proper_map [m : map] : Prop := ProperMap {
  map_sym : (z1, z2 : point) (m z1 z2) -> (m z2 z1);
  map_trans : (z1, z2 : point) (m z1 z2) -> (subregion (m z2) (m z1))
  }.

(* Elementary geometry. *)

Inductive interval : Type := Interval : R -> R -> interval.

Definition mem_interval [xz : interval; y : R] : Prop :=
  let (x, z) = xz in (ltr x y) /\ (ltr y z).

Coercion mem_interval : interval >-> FUNCLASS.

Inductive rect : Type := Rect : (xint, yint : interval) rect.

Definition mem_rect [r : rect] : region :=
  [z]let (xint, yint) = r in let (x, y) = z in (xint x) /\ (yint y).

Coercion mem_rect : rect >-> region.

(* Elementary topology. *)

Definition open [r : region] : Prop :=
  (z : point) (r z) -> (EXT rr : rect | (rr z) & (subregion rr r)).

Definition closure [r : region] : region :=
  [z](r' : region) (open r') -> (r' z) -> (meet r r').

Definition connected [r : region] : Prop :=
  (r1, r2 : region) (subregion r (union r1 r2)) ->
    (meet r1 r) -> (meet r2 r) ->
    (open r1) -> (open r2) -> (meet r1 r2).     

Record simple_map [m : map] : Prop := SimpleMap {
    simple_map_proper :> (proper_map m);
    map_open : (z : point) (open (m z));
    map_connected : (z : point) (connected (m z))
  }.

Record finite_simple_map [m : map] : Prop := FiniteSimpleMap {
    finite_simple_map_base :> (simple_map m);
    finite_simple_map_size : (EX n | (size_at_most n m))
  }.

(* Borders, corners, adjacency and coloring. *)

Definition border [m : map; z1, z2 : point] : region :=
  (intersect (closure (m z1)) (closure (m z2))).

Definition corner_map [m : map; z : point] : map :=
  [z1, z2](and (m z1 z2) (closure (m z1) z)).

Definition not_corner [m : map] : region :=
  [z](size_at_most (2) (corner_map m z)).

Definition adjacent [m : map; z1, z2 : point] : Prop :=
  (meet (not_corner m) (border m z1 z2)).

Record coloring [m, k : map] : Prop := Coloring {
  coloring_proper :> (proper_map k);
  coloring_inmap : (subregion (inmap k) (inmap m));
  coloring_covers : (covers m k);
  coloring_adj : (z1, z2 : point) (k z1 z2) -> (adjacent m z1 z2) -> (m z1 z2)
 }.

Definition map_colorable [nc : nat; m : map] : Prop := 
  (EXT k | (coloring m k) & (size_at_most nc k)).

End RealMap.

Unset Implicit Arguments.
