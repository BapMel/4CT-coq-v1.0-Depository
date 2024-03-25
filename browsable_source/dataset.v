(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require tacticext.
Require boolprop.
Require funs.

(* Generic definitions and lemmas for datatypes with reflected (decidable) *)
(* equality. The structure includes the actual boolean predicate, not just *)
(* the decision procedure. A canonical structure for the booleans is given *)
(* here, and one will be provided for the integers in natprop.v.           *)
(*   Congruence properties of injective functions wrt reflected equality   *)
(* are established.                                                        *)
(*   Basic definitions are also given for sets and relations (i.e., unary  *)
(* and binary boolean predicates); however, the boolean algebra is NOT     *)
(* lifted to sets.                                                         *)
(*   The main technical result is the construction of the subdomain        *)
(* associated with a set.                                                  *)
(*   Syntactic sugar is provided for the equality predicate and its        *)
(* reflection property.                                                    *)
(*   We also provide a "dirty trick" to compensate for the fact that the   *)
(* Coq typechecker will not look up the canonical structure when pressed   *)
(* for the actual structure; a projection data will do the coercion.       *)

Set Implicit Arguments.

Definition reflect_eq [d : Set; eq_d : d -> d -> bool] : Set :=
  (x, y : d) (reflect x = y (eq_d x y)).

Structure dataSet : Type := DataSet {
  datum :> Set;
  eqdata : datum -> datum -> bool;
  eqdataP : (reflect_eq eqdata)
}.

Definition data [d : dataSet; u : (option d)] : dataSet :=
  if u is None then d else d.

Implicits data [].

Syntax constr level 0 :
  show_dataset_coercion [ (data $d $t) ] ->
    [ (EXPOPFORM data $d $t) ]
| hide_dataset_coercion [ (data $_ (None $t)) ] ->
    [ (OPFORM data $t) ].

Grammar constr constr0 : constr :=
  coerce_set_to_data ["(" "data" constr9($t) ")"] ->
    [ (!data ? (None $t)) ].

Definition eqd : (d : dataSet; x, y : d) bool := (nosimpl eqdata).

Lemma eqd_data : eqd = eqdata. Proof. Done. Qed.

Grammar constr constr1 : constr :=
  eqd_impl [constr0($x) "=d" constr0($y) ] ->
  [ (eqd $x $y) ]
| data_eq_expl ["<" lconstr($d) ">" constr0($x) "=d" constr0($y) ] ->
  [ (!eqd $d $x $y) ].

Syntax constr level 1:
  pp_data_eq [ (eqd $t1 $t2) ] ->
      [ [<hov 0> $t1:L [0 1]  " =d " $t2:L ] ].

Lemma eqPx : (d : dataSet; x, y : d) (reflect x = y x =d y).
Proof. Exact eqdataP. Qed.

Syntactic Definition eqP := eqPx | 2.

Grammar constr constr1 : constr :=
  data_eqP_impl [constr0($x) "=P" constr0($y) ] ->
  [ (eqPx $x $y) ]
| data_eqP_exl ["<" lconstr($d) ">" constr0($x) "=P" constr0($y) ] ->
  [ (!eqPx $d $x $y) ].

Syntax constr level 1:
  pp_data_eqP [ (eqdP $t1 $t2) ] ->
      [ [<hov 0> $t1:L [0 1]  " =P " $t2:L ] ].

Lemma eqd_refl : (d : dataSet; x : d) x =d x.
Proof. By Move=> *; Apply/eqP. Qed.

Lemma eqd_sym : (d : dataSet; x, y : d) (x =d y) = (y =d x).
Proof. By Move=> *; Apply/eqP/eqP. Qed.

(* A short proof of the K axiom (proof-irrelevance for x = x) on dataSets. *)

Theorem eqP_K : (d : dataSet; x : d; Ex : x = x) Ex == (erefl x).
Proof.
Move=> d x; Step Er: (E : x = x) (eq_ind ? x [y]y = x E x E) == (erefl x).
  By Case: {2 3 4 6 7 8}x /.
Move=> Ex; Case (Er if x =P x is (Reflect_true E) then E else Ex).
Case: {2 4 6 8 10 12 14 16}x / {-3}Ex; Case: (x =P x) => [E | []]; Auto.
Qed.

Lemma data_eqT : (d : dataSet; x, y : d;  E, E' : x = y) E == E'.
Proof. By Move=> d x y [] *; Rewrite eqP_K. Qed.

(* Comparison for booleans. *)

Lemma eqbPx : (reflect_eq eqb).
Proof. By Do 2 Case; Constructor. Qed.

Syntactic Definition eqbP := eqbPx | 2.

Canonical Structure boolData := (DataSet eqbPx).

Lemma eqbE : eqb = (!eqd?). Proof. Done. Qed.

Lemma bool_eqT : (x, y : bool; E, E' : x = y) E == E'.
Proof. Exact (!data_eqT?). Qed.

(* Subsets and relations, defined by their characteristic functions.       *)

Section DataSubset.

Variable d : dataSet.

Definition set : Set := d -> bool.
Definition rel : Set := d -> set.

Definition sub_set [a, a' : set] : Prop := (x : d) (a x) -> (a' x).
Definition sub_rel [e, e' : rel] : Prop := (x, y : d) (e x y) -> (e' x y).

Syntactic Definition set1 := (!eqd d).
Definition set2 [x1, x2 : d] : set := [y](orb x1 =d y x2 =d y).
Definition set3 [x1, x2, x3 : d] : set := [y](or3b x1 =d y x2 =d y x3 =d y).
Definition set4 [x1, x2, x3, x4 : d] : set :=
  [y](or4b x1 =d y x2 =d y x3 =d y x4 =d y).
Definition setU [a, b : set] : set := [x](orb (a x) (b x)).
Definition setU1 [x : d; a : set] : set := [y](orb x =d y (a y)).
Definition setI [a, b : set] : set := [x](andb (a x) (b x)).
Definition setC [a : set] : set := [x](negb (a x)).
Definition setC1 [x : d] : set := [y](negb x =d y).
Definition setD [a, b : set] : set := [x](andb (negb (b x)) (a x)).
Definition setD1 [a : set; x : d] : set := [y](andb (negb x =d y) (a y)).

Definition eqdf [f : d -> d] : rel := [x](set1 (f x)).
Definition relU [e, e' : rel] : rel := [x](setU (e x) (e' x)).

Lemma set11 : (x : d) (set1 x x). Proof. Apply: (!eqd_refl). Qed.

Lemma setU11 : (x : d; a : set) (setU1 x a x).
Proof. By Move=> *; Rewrite: /setU1 set11. Qed.

Lemma setU1r : (x : d; a : set) (sub_set a (setU1 x a)).
Proof. By Move=> x a y Hy; Rewrite: /setU1 Hy orbT. Qed.

Lemma setU1Px : (x : d; a : set; y : d) (reflect x = y \/ (a y) (setU1 x a y)).
Proof.
By Move=> x a y; Apply: (iffP orP) => [[Dy | Hy]]; Auto; Left;
   Rewrite: ?(eqP Dy) ?Dy ?set11.
Qed.

Lemma setC11 : (x : d) (setC1 x x) = false.
Proof. By Move=> *; Rewrite: /setC1 set11. Qed.

Lemma setD11 : (x : d; a : set) (setD1 a x x) = false.
Proof. By Move=> *; Rewrite: /setD1 set11. Qed.

Lemma set21 : (x1, x2 : d) (set2 x1 x2 x1). 
Proof. By Move=> *; Rewrite: /set2 set11. Qed.

Lemma set22 : (x1, x2 : d) (set2 x1 x2 x2). 
Proof. By Move=> *; Rewrite: /set2 set11 orbT. Qed.

Lemma set31 : (x1, x2, x3 : d) (set3 x1 x2 x3 x1). 
Proof. By Move=> *; Rewrite: /set3 set11 ?orbT. Qed.

Lemma set32 : (x1, x2, x3 : d) (set3 x1 x2 x3 x2). 
Proof. By Move=> *; Rewrite: /set3 set11 ?orbT. Qed.

Lemma set33 : (x1, x2, x3 : d) (set3 x1 x2 x3 x3). 
Proof. By Move=> *; Rewrite: /set3 set11 ?orbT. Qed.

Lemma sub_relUl : (e, e' : rel) (sub_rel e (relU e e')).
Proof. By Move=> e e' x y Hxy; Rewrite: /relU /setU Hxy. Qed.

Lemma sub_relUr : (e, e' : rel) (sub_rel e' (relU e e')).
Proof. By Move=> e e' x y Hxy; Rewrite: /relU /setU Hxy orbT. Qed.

End DataSubset.

Syntactic Definition set0 := [_:?]false.
Syntactic Definition set1 := (!eqd ?).
Syntactic Definition setU1P := setU1Px | 3.

Syntax constr level 0:
    pp_setO [<<(LAMBDALIST $_ [<>]<<false>>)>>] -> [ "set0" ]
  | pp_set1 [(eqd $x)] -> [ (OPFORM set1 $x) ].

Coercion setA := [d : dataSet; x : d]true : (d : dataSet)(set d).

Identity Coercion membership : set >-> FUNCLASS.

(* Lemmas for reflected equality and endo functions.   *)

Section DataSetFun.

Lemma inj_eqd : (d, d' : dataSet; h : d -> d'; Hh : (injective h); x, y : d)
  ((h x) =d (h y)) = (x =d y).
Proof. By Move=> *; Apply/eqP/eqP => *; [Auto | Congr h]. Qed.

Variables d : dataSet; f, g : d -> d.

Lemma monic_eqd : (monic f g) -> (x, y : d) ((f x) =d (f y)) = (x =d y).
Proof. Exact [Hf](inj_eqd (monic_inj Hf)). Qed.

Lemma iso_eqd : (iso f) -> (x, y : d) ((f x) =d (f y)) = (x =d y).
Proof. Exact [Hf](inj_eqd (iso_inj Hf)). Qed.

Lemma monic2_eqd :
  (monic f g) -> (monic g f) -> (x, y : d) ((f x) =d y) = (x =d (g y)).
Proof. Move=> Ef Eg x y; Rewrite: -{1 y}Eg; Apply (monic_eqd Ef). Qed.

Variable d' : dataSet.

Definition preimage [k : d -> d'; a : (set d')] : (set d) := [x] (a (k x)).

(* The invariant of an function f wrt a projection k is the set of points that *)
(* have the same projection as their image. We use this mainly with k a        *)
(* coloring function (in fact "coloring" a map is defined using "invariant").  *)

Definition invariant [k : d -> d'] : (set d) := [x] (k (f x)) =d (k x).

Lemma invariant_comp : (h : d' -> d'; k : d -> d')
  (sub_set (invariant k) (invariant (comp h k))).
Proof. By Move=> h k x Dkfx; Rewrite: /comp /invariant (eqP Dkfx) set11. Qed.

Lemma invariant_inj : (h : d' -> d'; Hh : (injective h); k : d -> d')
  (invariant (comp h k)) =1 (invariant k).
Proof. By Move=> h Hh k x; Rewrite: /comp /invariant (inj_eqd Hh). Qed.

End DataSetFun.

(* Various dataset constructions (however, we tend to roll out our own, in *)
(* order to retain control over the equality predicate).                   *)

Section ComparableDataSet.

Variable d : Set.

Definition comparable : Set := (x, y : d) {x = y} + {~ x = y}.

Hypothesis Hdec : (x, y : d) {x = y} + {~ x = y}.

Definition compareb [x, y : d] : bool :=
  if (Hdec x y) is (left _) then true else false.

Lemma compareP : (reflect_eq compareb).
Proof. By Move=> x y; Rewrite: /compareb; Case (Hdec x y); Constructor. Qed.

Definition compareData : dataSet := (DataSet compareP).

End ComparableDataSet.

Lemma comparable_data : (d : dataSet) (comparable d).
Proof. By Move=> d x y; Case (x =P y); Auto. Qed.

Section SubDataSet.

Variable d : dataSet; a : (set d).

Record subd : Set := subdI {subdE : d; subd_mem : (a subdE)}.

Lemma subd_eqPx : (reflect_eq [u, v : subd](subdE u) =d (subdE v)).
Proof.
Move=> [x Hx] [y Hy]; Apply: (iffP eqP) => [Hxy]; RightBy Congr subdE.
By Simpl in Hxy; Rewrite: -Hxy in Hy *; Rewrite (bool_eqT Hy Hx).
Qed.

Canonical Structure subData : dataSet := (DataSet subd_eqPx).

Lemma subd_eqd : (u, v : subData) (u =d v) = ((subdE u) =d (subdE v)).
Proof. Done. Qed.

Lemma subdE_inj : (injective subdE).
Proof. Move=> u v; Move/(introT eqP); Rewrite: -subd_eqd; Exact eqP. Qed.

Definition subdIopt [x : d] : (option subData) :=
  if (idPx (a x)) is (Reflect_true Hx) then (Some ? (subdI Hx)) else (None ?).

Inductive subdI_spec [x : d] : (option subData) -> Set :=
  Some_subd : (u : subData) (a x) -> (subdE u) = x -> (subdI_spec x (Some ? u))
| None_subd : (negb (a x)) -> (subdI_spec x (None ?)).

Lemma subdIoptP : (x : d) (subdI_spec x (subdIopt x)).
Proof.
Move=> x; Rewrite: /subdIopt; Case: {2}(a x) / (idPx (a x)); LeftBy Left.
By Move/(introT negP) => Hx; Right.
Qed.

End SubDataSet.

Syntactic Definition subd_eqP := subd_eqPx | 2.

Section ProdDataSet.

Variables d1, d2 : dataSet.

Record prodd : Set := proddI {proddE1 : d1; proddE2 : d2}.

Definition prodd_eqd [u, v : prodd] : bool :=
  let (x1, x2) = u in let (y1, y2) = v in (andb x1 =d y1 x2 =d y2).

Lemma prodd_eqPx : (reflect_eq prodd_eqd).
Proof.
Move=> [x1 x2] [y1 y2] /=; Apply: (iffP idP); LeftBy Case/andP; Do 2 Case/eqP.
By Injection=> [] []; Rewrite: !set11.
Qed.

Canonical Structure prodData := (DataSet prodd_eqPx).

Lemma prodd_eqE : prodd_eqd = (!eqd prodData). Proof. Done. Qed.

Lemma prodd_eqdl : (u, v : prodData) u =d v -> (proddE1 u) =d (proddE1 v).
Proof. By Move=> [x1 x2] [y1 y2]; Case/andP. Qed.

Lemma prodd_eqdr : (u, v : prodData) u =d v -> (proddE2 u) =d (proddE2 v).
Proof. By Move=>  [x1 x2] [y1 y2]; Case/andP. Qed.

End ProdDataSet.

Syntactic Definition prodd_eqP := prodd_eqPx | 2.

Section SumDataSet.

Variables I : dataSet; d : I -> dataSet.

Record sumd : Set := sumdI {sumdE1 : I; sumdE2 : (d sumdE1)}.

Local sumdE3 [u, v : sumd] : (d (sumdE1 u)) :=
  if (sumdE1 u) =P (sumdE1 v) is (Reflect_true Huv) then
    (eq_rec_r I (sumdE1 v) d (sumdE2 v) (sumdE1 u) Huv)
  else (sumdE2 u).

Remark sumdE3I : (i : I; x, y : (d i)) (sumdE3 (sumdI x) (sumdI y)) = y.
Proof.
Move=> i x y; Rewrite: /sumdE3 /=; Case: (i =P i) => [Hii | []]; Auto.
By Rewrite (eqP_K Hii).
Qed.

Definition sumd_eqd [u, v : sumd] : bool :=
  (andb (sumdE1 u) =d (sumdE1 v) (sumdE2 u) =d (sumdE3 u v)).

Lemma sumd_eqPx : (reflect_eq sumd_eqd).
Proof.
Move=> [i x] [j y]; Rewrite: /sumd_eqd /=; Case: (i =P j) y => [[]|Hij] y.
  By Apply: (iffP eqP) => [Dx | Huv]; Rewrite: 1?Dx -?Huv sumdE3I.
Right; Exact [Huv](Hij (congr sumdE1 Huv)).
Qed.

Canonical Structure sumData := (DataSet sumd_eqPx).

Lemma sumd_eqE : sumd_eqd = (!eqd sumData). Proof. Done. Qed.

Lemma sumd_eqdl : (u, v : sumData) u =d v -> (sumdE1 u) =d (sumdE1 v).
Proof.
By Move=> [i x] [j y]; Rewrite: {1}/eqd /= /sumd_eqd /=; Case (i =d j).
Qed.

Lemma sumd_eqdr : (i : I; x, y : (d i))
  (<sumData> (sumdI x) =d (sumdI y)) = (x =d y).
Proof.
Move=> i x y; Rewrite: {1}/eqd /= /sumd_eqd /= eqd_refl /=.
Exact (congr (eqd x) (sumdE3I x y)).
Qed.

End SumDataSet.

Syntactic Definition sumd_eqP := sumd_eqPx | 2.

Unset Implicit Arguments.
