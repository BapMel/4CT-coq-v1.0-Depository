(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require tacticext.
Require boolprop.
Require funs.
Require dataset.
Require natprop.
Require seq.
Require color.

Set Implicit Arguments.

(*   Sets of perimeter colorings are represented by a ternary tree structure *)
(* indexed by edge traces, with ``leaf'' nodes indicating full subtrees.     *)
(*   We use these trees to represent sets of unreachable traces, or a subset *)
(* of such traces that has just become reachable. In either case, all the    *)
(* leaves of a tree should be at the same depth (the ring size minus one).   *)
(*   The ctree_proper predicate checks this condition (we contract empty too *)
(* but this isn't necessary for correctness, so we don't check for this).    *)
(*   Trees representing full sets of unreachable traces store the number of  *)
(* matching unreachable chromograms at their leaves, in unary, as a stack of *)
(* ``subleaves''.                                                            *)
(*   We provide basic functions in this file : classifiers, accessors, and   *)
(* constructors, union and rotation of reachable path sets, and a disjoint   *)
(* test for checking contracts.                                              *)
(*   The more complex unreachable set functions, initialisation and matching *)
(* restriction by a will be defined in separate files.                       *)
(*   The restriction returns a pair of trees; these could be compressed into *)
(* a single ``marked tree'' structure, but the additional overhead doesn't   *)
(* seem worthwhile (in particular, it complicates the ``inner loop'' of the  *)
(* chromogram tree restriction operation).                                   *)

Inductive ctree : Set :=
    Ctree_node : (t1, t2, t3 : ctree) ctree
  | Ctree_leaf : (lf : (* leaf or empty *) ctree) ctree
  | Ctree_empty : ctree.

Inductive ctree_pair : Set :=
  Ctree_pair: (t0, t1 : ctree) ctree_pair.

(* Classifiers. *)

Definition ctree_empty [t : ctree] : bool :=
  if t is Ctree_empty then true else false.

Definition ctree_leaf [t : ctree] : bool :=
  if t is (Ctree_leaf _) then true else false.

(* Empty nodes are always contracted, so that we can check for an empty tree *)
(* by pattern-matching on Ctree_empty. The empty node test is used to        *)
(* interlock the computation in ctree_restrict: it is strict on all branches.*)

Definition ctree_empty_node [t : ctree] : bool :=
 Cases t of
   (Ctree_node Ctree_empty Ctree_empty Ctree_empty) => true
 | (Ctree_node _ Ctree_empty Ctree_empty) => false
 | (Ctree_node _ _ Ctree_empty) => false
 | _ => false
 end.

Inductive eq3_Ctree_empty : (t1, t2, t3 : ctree) Prop :=
  Eq3_Ctree_empty : (eq3_Ctree_empty Ctree_empty Ctree_empty Ctree_empty).

(* Node accessor. *)

Definition ctree_sel [t : ctree] : color -> ctree :=
  if t is (Ctree_node t1 t2 t3) then (palette Ctree_empty t1 t2 t3)
  else [_]Ctree_empty.

(* The correctness predicate for exact sets checks that leaves occur at a    *)
(* uniform height h, and only point to leaves or empty nodes.                *)

Fixpoint ctree_proper [h : nat; t : ctree] : Prop :=
  Cases t h of
    Ctree_empty _ => True
  | (Ctree_node t1 t2 t3) (S h') =>
       (and4 (ctree_empty_node t) = false
             (ctree_proper h' t1) (ctree_proper h' t2) (ctree_proper h' t3))
  | (Ctree_leaf lf) (0) => (ctree_proper (0) lf)
  | _ _ => False
  end.

(* Path accessors : ctree_sub returns a count (for unreachable traces),      *)
(* which ctree_mem simplies to a boolean for reachable traces.               *)

Fixpoint ctree_sub [t : ctree] :  colseq -> nat :=
  [et]Cases t et of
    (Ctree_node t1 t2 t3) (Adds e et') =>
      ((palette [_](0) (ctree_sub t1) (ctree_sub t2) (ctree_sub t3)) e et')
  | (Ctree_leaf lf) Seq0 => (S (ctree_sub lf et))
  | _ _ => (0)
  end.

Definition ctree_mem [t : ctree; et : colseq] : bool :=
  (negb ((0) =d (ctree_sub t et))).

(* Constructor and accessor for pairs.                                       *)

Definition ctree_empty_pair : ctree_pair :=
  (Ctree_pair Ctree_empty Ctree_empty).

Definition ctree_pair_sub [ctp : ctree_pair; b : bool] : ctree :=
  let (t0, t1) = ctp in if b is false then t0 else t1.

(* A function for constructing canonical leaves. *)

Definition ctree_leaf_of [n : nat] : ctree :=
  (iter n Ctree_leaf Ctree_empty).

(* A general cons function, used for now only in the restriction operation  *)
(* We could use it in the union and rot operations too, but it doesn't seem *)
(* worthwhile. The redundant case analysis is needed to interlock the       *)
(* computation and prevent the accumulation of thunks.                      *)

Definition ctree_cons [t1, t2, t3 : ctree] : ctree :=
  let t = (Ctree_node t1 t2 t3) in
  Cases t of
    (Ctree_node Ctree_empty Ctree_empty Ctree_empty) => t1
  | (Ctree_node _ Ctree_empty Ctree_empty) => t
  | (Ctree_node _ _ Ctree_empty) => t
  | _ => t
  end.

(* Specialized constructors, used to build single-branch trees.              *)

Definition ctree_cons0 [_ : ctree] : ctree :=
  Ctree_empty.

Definition ctree_cons1 [t : ctree] : ctree :=
  (ctree_cons t Ctree_empty Ctree_empty).

Definition ctree_cons2 [t : ctree] : ctree :=
  (ctree_cons Ctree_empty t Ctree_empty).
  
Definition ctree_cons3 [t : ctree] : ctree :=
  (ctree_cons Ctree_empty Ctree_empty t).

(* Any proper leaf will do for reachable trees, so we provide a single one   *)
(* that can be shared.                                                       *)

Definition ctree_simple_leaf : ctree := (Ctree_leaf Ctree_empty).

(* The actual, optimized construction of a single-branch tree from a config  *)
(* coloring map belongs in colorconfig.v, but we can give a spec right here, *)
(* and prove its main properties.                                            *)

Definition ctree_cons_e : color -> ctree -> ctree :=
  (palette ctree_cons0 ctree_cons1 ctree_cons2 ctree_cons3).

Definition ctree_of_ttail : colseq -> ctree :=
  (foldr ctree_cons_e ctree_simple_leaf).

(* The union operation is now interlocked, to match the rotlr operation that *)
(* is also interlocked now, to avoid the generation of a large number of     *)
(* transient thunks in the intermediate reachable tree (for the initial tree *)
(* the 150,000 or so thunks we unlikely to be a problem.                     *)

Fixpoint ctree_union [tl, tr : ctree] : ctree :=
  Cases tl tr of
    Ctree_empty _ => tr
  | _ Ctree_empty => tl
  | (Ctree_leaf _) _ => ctree_simple_leaf
  | _ (Ctree_leaf _) => ctree_simple_leaf
  | (Ctree_node tl1 tl2 tl3) (Ctree_node tr1 tr2 tr3) =>
      (ctree_cons
        (ctree_union tl1 tr1) (ctree_union tl2 tr2) (ctree_union tl3 tr3))
  end.

(* Rotations are done directly on the reachable sets, in order to save work *)
(* during the inner loop of gram tree restriction. The input to the initial *)
(* restriction is the cons of the three rotations of the tree reflecting    *)
(* the normal paths.                                                        *)

Fixpoint ctree_rotl [t : ctree] : ctree :=
  if t is (Ctree_node t1 t2 t3) then
    (ctree_cons (ctree_rotl t3) (ctree_rotl t1) (ctree_rotl t2))
  else t.

Fixpoint ctree_rotr [t : ctree] : ctree :=
  if t is (Ctree_node t1 t2 t3) then
    (ctree_cons (ctree_rotr t2) (ctree_rotr t3) (ctree_rotr t1))
  else t.

Definition ctree_cons_rot [t : ctree] : ctree :=
  (ctree_cons t (ctree_rotl t) (ctree_rotr t)).

(*   The input to subsequent restrictions is the union of the left and right *)
(* rotations of the set of traces that were reached in during the previous   *)
(* iteration (by construction, there are no chromograms left that match      *)
(* reached traces); here we define an optimized union-of-rotations function  *)
(* for that case.                                                            *)
(*   Oddly, with this design the chromogram tree is NEVER symmetrical except *)
(* when we reach the fixpoint. Forcing the symmetry by building the union of *)
(* all rotations would save half the work here, only to add 33% more to the  *)
(* gram tree restriction. Contrarily, it might be useful to intersect the    *)
(* set with actually unreachable paths as some pruning might occur higher;   *)
(* for now, we don't --- we'd need to define intersecting versions of rotl   *)
(* and rotr as those special cases of union occur often (reachable sets are  *)
(* sparse). We could also preremove these colorings that have been reached   *)
(* ``by permutation'', rather than wait for the next ctree iteration to      *)
(* clear them; again, it's not obvious how much we stand to gain.            *)

Fixpoint ctree_union_rotlr [tl, tr : ctree] : ctree :=
  Cases tl tr of
    Ctree_empty (Ctree_node t1 t2 t3) =>
      (ctree_cons (ctree_rotr t2) (ctree_rotr t3) (ctree_rotr t1))
  | (Ctree_node t1 t2 t3) Ctree_empty =>
      (ctree_cons (ctree_rotl t3) (ctree_rotl t1) (ctree_rotl t2))
  | (Ctree_node tl1 tl2 tl3) (Ctree_node tr1 tr2 tr3) =>
      let cur = ctree_union_rotlr in
      (ctree_cons (cur tl3 tr2) (cur tl1 tr3) (cur tl2 tr1))
  | Ctree_empty _ => tr
  | _ Ctree_empty => tl
  | _ (Ctree_node t1 t2 t3) =>
    if (ctree_cons (ctree_rotr t2) (ctree_rotr t3) (ctree_rotr t1)) is Ctree_empty
    then tl else ctree_simple_leaf
  | (Ctree_node t1 t2 t3) _ =>
    if (ctree_cons (ctree_rotl t3) (ctree_rotl t1) (ctree_rotl t2)) is Ctree_empty
    then tr else ctree_simple_leaf
  | _ _ => ctree_simple_leaf
  end.

Definition ctree_rotlr [t : ctree] := (ctree_union_rotlr t t).

(* A disjointness test, for checking contracts.                             *)

Fixpoint ctree_disjoint [tl, tr : ctree] : bool :=
  Cases tl tr of
    (Ctree_leaf _) (Ctree_leaf _) => false
  | (Ctree_node tl1 tl2 tl3) (Ctree_node tr1 tr2 tr3) =>
       if (ctree_disjoint tl1 tr1) then
         if (ctree_disjoint tl2 tr2) then (ctree_disjoint tl3 tr3) else false
       else false
  | _ _ => true
  end.

(* Properties of classifiers : folding back expanded tests, using equality. *)

Lemma fold_ctree_empty : (A : Set; ve, vne : A; t : ctree)
  (Cases t of Ctree_empty => ve | _ => vne end)
    = (if (ctree_empty t) then ve else vne).
Proof. By Move=> A ve vne; Case. Qed.

Lemma fold_ctree_leaf : (A : Set; vlf, vnlf : A; t : ctree)
  (Cases t of (Ctree_leaf _) => vlf | _ => vnlf end)
    = (if (ctree_leaf t) then vlf else vnlf).
Proof. By Move=> A vlf vnlf; Case. Qed.

Lemma ctree_empty_eq : (t : ctree) (ctree_empty t) -> t = Ctree_empty.
Proof. By Case. Qed.

Lemma ctree_empty_node_eq : (t1, t2, t3 : ctree)
  (Ht : (ctree_empty_node (Ctree_node t1 t2 t3)) = true)
  (eq3_Ctree_empty t1 t2 t3).
Proof. By Do 3 (Case; [Do 3 Intro | Intro | Idtac]). Qed.

Lemma ctree_empty_nodeP : (t : ctree)
  (reflect t = (Ctree_node Ctree_empty Ctree_empty Ctree_empty)
          (ctree_empty_node t)).
Proof.
By Case; First [Right | Do 3 (Case; [Do 3 Intro | Intro | Idtac]); Constructor].
Qed.

(* Most properties of ctree_sel and ctree_proper are given below, but there  *)
(* are a few identities that are not reductions.                             *)

Lemma ctree_sel_0 : (t : ctree)
  (ctree_sel t Color0) = Ctree_empty.
Proof. By Case. Qed.

Lemma ctree_proper_sel : (h : nat; t : ctree; e : color)
  (ctree_proper h t) -> (ctree_proper (pred h) (ctree_sel t e)).
Proof. By Move=> [|h] [t1 t2 t3|lf|] //= [|||] [Hne Ht1 Ht2 Ht3] /=. Qed.

(* Properties of the lookup functions.                                       *)

Lemma ctree_sub_0 : (t : ctree; et : colseq)
  (et Color0) -> (ctree_sub t et) = (0).
Proof.
Move=> t et; Elim: et t => [|e et Hrec] //.
By Case=> // [t1 t2 t3]; Case: e => /=; Auto.
Qed.

Lemma ctree_mem_0 : (t : ctree; et : colseq)
  (et Color0) -> (ctree_mem t et) = false.
Proof. By Move=> *; Rewrite: /ctree_mem ctree_sub_0. Qed.

Lemma ctree_mem_seq0 :  (t : ctree)
  (ctree_mem t seq0) = (ctree_leaf t).
Proof. By Case. Qed.

Lemma ctree_sub_sel :  (t : ctree; e : color; et : colseq)
   (ctree_sub t (Adds e et)) = (ctree_sub (ctree_sel t e) et).
Proof. By Move=> [t1 t2 t3|lf|] // [|||] et. Qed.

Lemma ctree_mem_sel :  (t : ctree; e : color; et : colseq)
   (ctree_mem t (Adds e et)) = (ctree_mem (ctree_sel t e) et).
Proof. By Move=> *; Rewrite: /ctree_mem !ctree_sub_sel. Qed.

Lemma ctree_mem_leaf : (lf : ctree; et : colseq)
  (ctree_mem (Ctree_leaf lf) et) = ((0) =d (size et)).
Proof. By Move=> lf [|e et]. Qed.

(* Properties of the leaf constructor. *)

Lemma ctree_leaf_of_proper : (n : nat) (ctree_proper (0) (ctree_leaf_of n)).
Proof. By Case=> //=; Elim=> /=. Qed.

Lemma ctree_sub_leaf_of : (n : nat; et : colseq)
  (ctree_sub (ctree_leaf_of n) et)
     = (if (size et) =d (0) then n else (0)).
Proof. By Move=> [|n] [|e et] //=; Elim: n => [|n Hrec] /=; Auto. Qed.

(* Properties of the interlocking constructor. *)

Lemma ctree_cons_spec : (t1, t2, t3 : ctree)
  (ctree_cons t1 t2 t3) =
      (if (ctree_empty_node (Ctree_node t1 t2 t3)) then Ctree_empty
       else (Ctree_node t1 t2 t3)).
Proof. By Move=> t1 t2 t3; Case t1; Case t2; Case t3. Qed.

Lemma ctree_leaf_cons : (t1, t2, t3 : ctree)
  (ctree_leaf (ctree_cons t1 t2 t3)) = false.
Proof.
Move=> t1 t2 t3; Rewrite ctree_cons_spec.
By Case Ht: (ctree_empty_node (Ctree_node t1 t2 t3)).
Qed.

Lemma ctree_sel_cons : (t1, t2, t3 : ctree; e : color)
  (ctree_sel (ctree_cons t1 t2 t3) e) = (ctree_sel (Ctree_node t1 t2 t3) e).
Proof.
Move=> t1 t2 t3 e; Rewrite ctree_cons_spec.
Case Ht: (ctree_empty_node (Ctree_node t1 t2 t3)) => //.
By Rewrite (ctree_empty_nodeP ? Ht); Case e.
Qed.

Lemma ctree_cons_proper : (h : nat; t1, t2, t3 : ctree)
  (ctree_proper h t1) -> (ctree_proper h t2) -> (ctree_proper h t3) ->
     (ctree_proper (S h) (ctree_cons t1 t2 t3)).
Proof.
Move=> h t1 t2 t3 Ht1 Ht2 Ht3; Rewrite ctree_cons_spec.
By Case Ht: (ctree_empty_node (Ctree_node t1 t2 t3)); Split.
Qed.

Lemma ctree_sub_cons : (t1, t2, t3 : ctree; et : colseq)
  (ctree_sub (ctree_cons t1 t2 t3) et) = (ctree_sub (Ctree_node t1 t2 t3) et).
Proof.
Move=> t1 t2 t3 [|e et]; Rewrite ctree_cons_spec;
  Case Ht: (ctree_empty_node (Ctree_node t1 t2 t3)) => //.
By Rewrite (ctree_empty_nodeP ? Ht); Case e.
Qed.

Lemma ctree_mem_cons : (t1, t2, t3 : ctree; et : colseq)
  (ctree_mem (ctree_cons t1 t2 t3) et) = (ctree_mem (Ctree_node t1 t2 t3) et).
Proof. By Move=> *; Rewrite: /ctree_mem ctree_sub_cons. Qed.

(* Properties of the branch constructors. *)

Lemma ctree_cons_e_spec : (e : color; t : ctree)
  let t_if_e = [c](if c =d e then t else Ctree_empty) in
  (ctree_cons_e e t) =
     (ctree_cons (t_if_e Color1) (t_if_e Color2) (t_if_e Color3)).
Proof. By Do 2 Case. Qed.

Lemma ctree_cons_e_proper : (h : nat; e : color; t : ctree)
  (ctree_proper h t) -> (ctree_proper (S h) (ctree_cons_e e t)).
Proof.
Move=> h e t Ht; Rewrite ctree_cons_e_spec.
By Apply ctree_cons_proper; Case e; Simpl.
Qed.

Lemma ctree_of_ttail_proper : (h : nat; et : colseq)
  (size et) = h -> (ctree_proper h (ctree_of_ttail et)).
Proof.
By Move=> h et; Case {h}; Elim: et => [|e et Hrec] //; Apply: ctree_cons_e_proper.
Qed.

Lemma ctree_of_ttail_mem : (et, et' : colseq)
  (negb (et Color0)) -> (reflect et' = et (ctree_mem (ctree_of_ttail et) et')).
Proof.
Elim=> [|e et Hrec] et' /=; LeftBy Case et'; Constructor.
Move/norP=> [He Het]; Rewrite: ctree_cons_e_spec ctree_mem_cons.
Case: et' => [|e' et'] /=; LeftBy Constructor.
Case De': e'; First
[ By Constructor; Move=> H; Case/idP: He; Injection: H => _ []
| Rewrite: ctree_mem_sel /= -De'; Case: (e' =P e) => [Ee | He'] /=;
  Try (Rewrite: -Ee /=; Case: (Hrec et' Het) => [Det' | Het']);
  By Constructor; First [Rewrite Det' | Injection]].
Qed.

(* Properties of the union. *)

Lemma ctree_union_Nl : (t : ctree) (ctree_union Ctree_empty t) = t.
Proof. By Case. Qed.

Lemma ctree_union_Nr : (t : ctree) (ctree_union t Ctree_empty) = t.
Proof. By Case. Qed.

Lemma ctree_union_sym : (t1, t2 : ctree)
  (ctree_union t1 t2) = (ctree_union t2 t1).
Proof.
Elim=> [t11 Hrec1 t12 Hrec2 t13 Hrec3|l1 Hrec|] [t21 t22 t23|l2|] //=.
By Rewrite: Hrec1 Hrec2 Hrec3.
Qed.

Lemma ctree_union_proper : (h : nat; tl, tr : ctree)
  (ctree_proper h tl) -> (ctree_proper h tr) ->
    (ctree_proper h (ctree_union tl tr)).
Proof.
Elim=> [|h Hrec] tl tr; LeftBy Case: tl => //; Case tr.
Case: tl; [Move=> tl1 tl2 tl3| Contradiction | By Case tr].
Case: tr; [Move=> tr1 tr2 tr3| Contradiction | Done]; Simpl.
Move=> [Htlne Htl1 Htl2 Htl3] [Htrne Htr1 Htr2 Htr3].
Apply ctree_cons_proper; Auto.
Qed.

Lemma ctree_mem_union : (h : nat; tl, tr : ctree; et : colseq)
  (Htl : (ctree_proper h tl); Htr : (ctree_proper h tr))
  (ctree_mem (ctree_union tl tr) et)
     = (orb (ctree_mem tl et) (ctree_mem tr et)).
Proof.
Rewrite: /ctree_mem; Elim=> [|h Hrec] tl tr et.
  Case: tl; [Done | Idtac | By Rewrite: ctree_union_Nl].
  By Case: tr => //; Case et.
Case: tl; [Simpl | Done | By Rewrite ctree_union_Nl].
Move=> tl1 tl2 tl3 [Htlne Htl1 Htl2 Htl3].
Case: tr; Simpl; [Move=> tr1 tr2 tr3 | Done | By Rewrite orbF].
Move=> [Htrne Htr1 Htr2 Htr3]; Rewrite ctree_sub_cons.
Case: et => [|[|||] et] /=; Auto.
Qed.

(* Properties of the rotations. *)

Lemma ctree_rotl_proper : (h : nat; t : ctree)
  (ctree_proper h t) -> (ctree_proper h (ctree_rotl t)).
Proof.
Elim=> [|h Hrec] [t1 t2 t3|lf|] //= [Hne Ht1 Ht2 Ht3].
Apply ctree_cons_proper; Auto.
Qed.

Lemma ctree_rotr_proper : (h : nat; t : ctree)
  (ctree_proper h t) -> (ctree_proper h (ctree_rotr t)).
Proof.
Elim=> [|h Hrec] [t1 t2 t3|lf|] //= [Hne Ht1 Ht2 Ht3].
Apply ctree_cons_proper; Auto.
Qed.

Lemma ctree_mem_rotl : (t : ctree; et : colseq)
  (ctree_mem (ctree_rotl t) et) = (ctree_mem t (permt Eperm312 et)).
Proof.
Rewrite: /ctree_mem; Move=> t et; Elim: et t => [|e et Hrec] [t1 t2 t3|lf|] //=;
  By Rewrite: ctree_sub_cons //; Case: e => /=.
Qed.

Lemma ctree_mem_rotr : (t : ctree; et : colseq)
  (ctree_mem (ctree_rotr t) et) = (ctree_mem t (permt Eperm231 et)).
Proof.
Rewrite: /ctree_mem; Move=> t et; Elim: et t => [|e et Hrec] [t1 t2 t3|lf|] //=;
  By Rewrite: ctree_sub_cons //; Case: e => /=.
Qed.

(* Properties of the initial reachable set constructor. *)

Lemma ctree_cons_rot_proper : (h : nat; t : ctree)
  (ctree_proper h t) -> (ctree_proper (S h) (ctree_cons_rot t)).
Proof.
Move=> h t Ht; Rewrite: /ctree_cons_rot.
By Apply ctree_cons_proper;
   [Idtac | Apply ctree_rotl_proper | Apply ctree_rotr_proper].
Qed.

Lemma ctree_mem_cons_rot : (t : ctree; et : colseq)
  (ctree_mem (ctree_cons_rot t) et) = (ctree_mem t (ttail et)).
Proof.
Rewrite: /ctree_cons_rot /ttail; Move=> t [|e et].
  By Rewrite: /= ctree_mem_seq0 ctree_leaf_cons ctree_mem_0.
Case: e; Try (By Rewrite: /= !ctree_mem_0);
  Rewrite: ctree_mem_cons {1}/ctree_mem /=;
  By Rewrite: ?permt_id -1?ctree_mem_rotl -1?ctree_mem_rotr.
Qed.

(* Properties of the union-of-rotations combination. *)

Lemma ctree_union_rotlr_spec : (tl, tr : ctree)
  (ctree_union_rotlr tl tr) = (ctree_union (ctree_rotl tl) (ctree_rotr tr)).
Proof.
Move=> tl; Elim: tl => [tl1 Hrec1 tl2 Hrec2 tl3 Hrec3|lfl Hrec|] tr.
    Case: tr => [tr1 tr2 tr3|lf|] //=.
      Symmetry; Rewrite: 2!ctree_cons_spec Hrec1 Hrec2 Hrec3.
      Move: (ctree_rotl tl3) (ctree_rotl tl1) (ctree_rotl tl2) => tl1' tl2' tl3'.
      Move: (ctree_rotr tr2) (ctree_rotr tr3) (ctree_rotr tr1) => tr1' tr2' tr3'.
      Case Etl: (ctree_empty_node (Ctree_node tl1' tl2' tl3')).
        Case (ctree_empty_node_eq Etl).
        By Rewrite: 4!ctree_union_Nl ctree_cons_spec.
      Case Etr: (ctree_empty_node (Ctree_node tr1' tr2' tr3')); RightDone.
      Case (ctree_empty_node_eq Etr).
      By Rewrite: 4!ctree_union_Nr ctree_cons_spec Etl.
    By Case: (ctree_cons (ctree_rotl tl3) (ctree_rotl tl1) (ctree_rotl tl2)).
  Case: tr => [tr1 tr2 tr3|lf|] //=.
  By Case (ctree_cons (ctree_rotr tr2) (ctree_rotr tr3) (ctree_rotr tr1)).
By Rewrite: /ctree_rotl ctree_union_Nl; Case tr.
Qed.

Lemma ctree_rotlr_proper : (h : nat; t : ctree)
  (ctree_proper h t) -> (ctree_proper h (ctree_rotlr t)).
Proof.
Move=> h t Ht; Rewrite: /ctree_rotlr ctree_union_rotlr_spec.
By Apply ctree_union_proper; [Apply ctree_rotl_proper | Apply ctree_rotr_proper].
Qed.

Lemma ctree_mem_rotlr : (h : nat; t : ctree; et : colseq)
  (Ht : (ctree_proper h t))
  let mem_et312 = (ctree_mem t (permt Eperm312 et)) in
  let mem_et231 = (ctree_mem t (permt Eperm231 et)) in
  (ctree_mem (ctree_rotlr t) et) = (orb mem_et312 mem_et231).
Proof.
Move=> h t et Ht; Rewrite: /ctree_rotlr ctree_union_rotlr_spec.
By Rewrite: -ctree_mem_rotl -ctree_mem_rotr (!ctree_mem_union h) //;
  [Apply  ctree_rotl_proper | Apply ctree_rotr_proper].
Qed.

(* Exact interpretation of the disjointness test (the 4ct requires only one *)
(* direction).                                                              *)

Lemma ctree_mem_disjoint_spec : (tl, tr : ctree)
  (reflect (EX et | (andb (ctree_mem tl et) (ctree_mem tr et))) 
           (negb (ctree_disjoint tl tr))).
Proof.
Move=> tl; Def: Ineg := [t,t'](negb_intro (ctree_disjoint t t')).
Elim: tl => [tl1 Hrec1 tl2 Hrec2 tl3 Hrec3|lfl Hrec|] [tr1 tr2 tr3|lfr|];
  Try (Constructor; Hnf; Move=> [et Het]; Case/negPf: Het => //=;
       Case: et => //= *; Apply andbF).
  Rewrite: /= -if_negb; Case: {Hrec1}(Hrec1 tr1) => [Hc1 | Hn1].
    By Left; Case: Hc1 => [et Het]; Exists (Adds Color1 et); Simpl.
  Rewrite: /= -if_negb; Case: {Hrec2}(Hrec2 tr2) => [Hc2 | Hn2].
    By Left; Case: Hc2 => [et Het]; Exists (Adds Color2 et); Simpl.
  Case: {Hrec3}(Hrec3 tr3) => [Hc3 | Hn3].
    By Left; Case: Hc3 => [et Het]; Exists (Adds Color3 et); Simpl.
  Right; Move=> [et Het]; Case/idP: {}Het.
  By Case: et Het => [|[|||] et] Het //;
     [Case Hn1 | Case Hn2 | Case Hn3]; Exists et.
By Constructor; Exists (seq0 :: colseq).
Qed.

Lemma ctree_mem_disjoint : (tl, tr : ctree; et : colseq)
                           (Ht : (ctree_disjoint tl tr))
  (ctree_mem tr et) -> (ctree_mem tl et) = false.
Proof.
Move=> tl tr et Ht Hpr; Apply: (introF idP) => [Hpl].
By Case/(ctree_mem_disjoint_spec ? ?): Ht; Exists et; Rewrite: Hpr Hpl.
Qed.

Unset Implicit Arguments.
