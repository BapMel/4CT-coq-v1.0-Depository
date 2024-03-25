(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require tacticext.
Require boolprop.
Require funs.
Require dataset.
Require natprop.
Require seq.
Require paths.
Require color.
Require finset.
Require connect.
Require hypermap.
Require geometry.

Set Implicit Arguments.

(* Configuration maps are entered as little linear construction programs : *)
(* staring from a basic triangle, it builds a sequence of concentric quasi *)
(* cubic maps, alternatively rotating the perimeter, and adding a single   *)
(* outer node (and a new region) or two adjacent ones (which closes up a   *)
(* region, and introduces a new one).                                      *)
(*   We also need two generalizations of this construction:                *)
(*    - the proof of the birkhoff theorem requires computing the coloring  *)
(* of a few non-two connected quasi cubic plain maps; they can be obtained *)
(* by starting the construction from a single edge, and allowing adding    *)
(* a disconnected face during the construction.                            *)
(*    - the contract colorings are computed as colorings of reduced maps,  *)
(* whose construction is similar to the above, but also two operations     *)
(* that enclose a region by either merging its two neighbors (this creates *)
(* a binary node), or making them adjacent (this creates a ternary node).  *)
(*    We define all the necessary map constructions here. The two "add     *)
(* node" contructions are factored through the "add face" and a rotated    *)
(* variant of the "enclose face" constructions.                            *)

Inductive cpstep : Set :=
  CpR : nat -> cpstep  (* rotation around the outer ring (noop on overflow) *)
| CpR' : cpstep        (* single-step reverse rotation (for encodings)      *)
| CpY : cpstep         (* new Y junction & face                             *)
| CpH : cpstep         (* new H junction & face (closing an inner face)     *)
| CpU : cpstep         (* new face, no junctions (U-shaped loop)            *)
| CpK : cpstep         (* new K (inverted Y) junction (closing off a face)  *)
| CpA : cpstep.        (* inverted-V junction, merging neighbors of a face  *)

Lemma cpstepDataP : (comparable cpstep).
Proof. Rewrite: /comparable; Decide Equality; Apply: comparable_data. Qed.
Definition cpstepData := Eval Compute in (compareData cpstepDataP).
Canonical Structure cpstepData.

(* A configuration map construction program is just a sequence of steps.     *)
(* It is interpreted RIGHT TO LEFT, starting from a simple U-shaped map.     *)

Definition cprog : Set := (seq cpstepData).

Grammar constr constr0 : constr :=
  cprog_enum [ "(" "Cprog" cpsteps($p) ")"] -> [$p]
with cpsteps : constr :=
  cpstepR [nat:number($n) cpsteps($p)] -> [(Adds (CpR $n) $p)]
| cpstepR' ["-" "1" cpsteps($p)] -> [(Adds CpR' $p)]
| cpstepY ["Y" cpsteps($p)] -> [(Adds CpY $p)]
| cpstepH ["H" cpsteps($p)] -> [(Adds CpH $p)]
| cpstepU ["U" cpsteps($p)] -> [(Adds CpU $p)]
| cpstepK ["K" cpsteps($p)] -> [(Adds CpK $p)]
| cpstepA ["A" cpsteps($p)] -> [(Adds CpA $p)]
| cpstep0 []                -> [(Seq0 cpstepData)].

Syntax constr level 10 :
  pp_cprog_fold_call [(Pretty (seq cpstepData) $cp)] -> [<<(Pretty cprog $cp)>>]
| pp_cprog_fold2_call [(Pretty (seq (DataSet eq_cpstepP)) $cp)] ->
  [<<(Pretty cprog $cp)>>]
| pp_cprog_box [(Pretty cprog $cp)] -> ["Cprog" [<hov 1> (CPROG $cp)]]
| pp_cprog_default [<<(CPROG $cp)>>] -> [[1 0] "& " $cp:L]
| pp_cprog0 [<<(CPROG <<(Seq0 $_)>>)>>] -> []
| pp_cprogR [<<(CPROG <<(Adds (CpR $n) $cp)>>)>>] -> [[1 0] $n (CPROG $cp)]
| pp_cprogR' [<<(CPROG <<(Adds CpR' $cp)>>)>>] -> [[1 0] "-1" (CPROG $cp)]
| pp_cprogY [<<(CPROG <<(Adds CpY $cp)>>)>>] -> [[1 0] "Y" (CPROG $cp)]
| pp_cprogH [<<(CPROG <<(Adds CpH $cp)>>)>>] -> [[1 0] "H" (CPROG $cp)]
| pp_cprogU [<<(CPROG <<(Adds CpU $cp)>>)>>] -> [[1 0] "U" (CPROG $cp)]
| pp_cprogK [<<(CPROG <<(Adds CpK $cp)>>)>>] -> [[1 0] "K" (CPROG $cp)]
| pp_cprogA [<<(CPROG <<(Adds CpA $cp)>>)>>] -> [[1 0] "A" (CPROG $cp)].

Fixpoint cubic_prog [cp : cprog] : bool :=
  Cases cp of
    Seq0 => true
  | (Adds (CpR _) cp') => (cubic_prog cp')
  | (Adds CpU cp') => (cubic_prog cp')
  | (Adds CpY cp') => (cubic_prog cp')
  | (Adds CpH cp') => (cubic_prog cp')
  | _ => false
  end.

(* The configuration data comprises the construction program for the         *)
(* configuration map, the reducibility contract, represented as a sequence   *)
(* of integers (indexing the contract edges in the construction process),    *)
(* and a boolean flagging symmetrical maps, whose reflection does not need   *)
(* to be checked when scanning a part for reducible patterns (see quiztree). *)
(*   The reducibility program aways starts with an H, and ends with a Y; we  *)
(* need to check this explicitly (both in cfquiz.v and cfcontract.v). The    *)
(* initial H signals the end of the contract in the concrete syntax. The     *)
(* pattern-matching tree store further assumes that if a face has arity 9,   *)
(* 10, or 11, it is the one containing the first dart created.               *)
(*    We define equality on configurations, but only in order to be able to  *)
(* use sequences of configurations.                                          *)

Record config : Set := ConfigRecord {
  cfsym : bool;
  cfcontract_ref : natseq;
  cfprog : cprog}.

Grammar constr constr0 : constr :=
  config_spec
     [ "(" "Config" cfsym($sym) cfccref($cc) "H" cpsteps($p) ")"] ->
  [(ConfigRecord $sym $cc (Adds CpH $p))]
with cfsym : constr :=
  some_cfsym ["*"] -> [true]
| no_cfsym [ ] -> [false]
with cfccref : constr :=
  cfccref_adds [nat:number($e1) cfccref($cc)] -> [(Seq $e1 & $cc)]
| cfccref_last [nat:number($e1)] -> [(Seq $e1)].

(* Config pretty-printing is automatically turned on when the cfprog value *)
(* explicitly starts with an initial CpH.                                  *)
Syntax constr level 10 :
  pp_config_H [(ConfigRecord $s $cc(Adds CpH $cp))] ->
  [<<(Pretty config (ConfigRecord $s $cc (Adds CpH $cp)))>>]
| pp_config_form [(Pretty $_ (ConfigRecord $s $cc $cp))] ->
  ["Config" (CFSYM $s) [<hov 1> (CFCC $cc) (CPROG $cp)]]
| pp_cfsym_default [<<(CFSYM $s)>>] ->
  [<<(Pretty bool $s)>>:L]
| pp_cfsym_true [<<(CFSYM <<true>>)>>] ->
  ["*"]
| pp_cfsym_false [<<(CFSYM <<false>>)>>] ->
  []
| pp_cfcc_defaut [<<(CFCC $cc)>>] ->
  [[1 0] "&" <<(Pretty (seq natData) $cc)>>:L]
| pp_cfcc_adds [<<(CFCC <<(Adds $i $cc)>>)>>] ->
  [[1 0] $i (CFCC $cc)]
| pp_cfcc_seq0 [<<(CFCC <<(Seq0 $_)>>)>>] ->
  [].

Fixpoint config_prog [cp : cprog] : bool :=
  Cases cp of
    (Adds (CpR _) cp') => (config_prog cp')
  | (Adds CpY Seq0) => true
  | (Adds CpY cp') => (config_prog cp')
  | (Adds CpH cp') => (config_prog cp')
  | _ => false
  end.

Lemma config_prog_cubic : (cp : cprog) (config_prog cp) -> (cubic_prog cp).
Proof. By Elim=> [|[n||||||] cp  Hrec] //=; Case: cp Hrec; Auto. Qed.

Lemma configDataP : (comparable config).
Proof. Rewrite: /comparable; Decide Equality; Apply: (!comparable_data). Qed.
Definition configData := Eval Compute in (compareData configDataP).
Canonical Structure configData.

Definition configseq : Set := (seq configData).

Section ConfigSamples.

(* Samples: the pentaton map construction, and the first reducible config.   *)

Local pentamap := (Cprog H 4 Y Y).
Local config1 := (Config* 15 H 3 H 5 H 5 Y 4 H 4 Y 2 Y 1 Y).

(* Eval Compute in (config_prog (cfprog config1)). *)

End ConfigSamples.

Record pointed_map : Type :=
  PointedMap { pointee :> hypermap; pointer :> pointee }.

Section CpRing.

Variables g : hypermap; x0 : g.

Definition cpring : (seq g) := (rev (orbit node (node (node x0)))).

Definition proper_cpring : bool := (negb x0 =d (node x0)).
Definition long_cpring : bool := (negb (face (edge x0)) =d (node x0)).

Lemma uniq_cpring : (uniq cpring).
Proof. By Rewrite: /cpring uniq_rev uniq_orbit. Qed.

Lemma mem_cpring : cpring =1 (cnode x0).
Proof. By Move=> x; Rewrite: /cpring mem_rev -fconnect_orbit -!cnode1. Qed.

Lemma size_cpring : (size cpring) = (order node x0).
Proof. By Rewrite: -(card_uniqP uniq_cpring) (eq_card mem_cpring). Qed.

Lemma size_proper_cpring : proper_cpring = (ltn (1) (size cpring)).
Proof.
Move: (iter_order (Inode g) x0) (uniq_orbit node x0).
Rewrite: size_cpring /proper_cpring eqd_sym /orbit -(orderSpred node x0) .
Case: (pred (order node x0)) => [|n] //= Dnx; LeftBy Rewrite: Dnx set11.
By Case/andP; Case/norP.
Qed.

Lemma size_long_cpring : long_cpring = (ltn (2) (size cpring)).
Proof.
Move: (orderSpred node x0) (iter_order (Inode g) x0) (uniq_orbit node x0).
Rewrite: size_cpring /long_cpring eqd_sym -(monic2F_eqd (Enode g)) /orbit.
Case: (order node x0) => [|[|[|n]]] //= _ Dnx; Try By Rewrite: !Dnx set11.
By Case/andP; Case/norP; Clear; Case/norP.
Qed.

Lemma cycle_rev_cpring : (fcycle node (rev cpring)).
Proof. By Rewrite: /cpring rev_rev (cycle_orbit (Inode g)). Qed.

Lemma ucycle_rev_cpring : (ufcycle node (rev cpring)).
Proof. By Rewrite: /ucycle uniq_rev uniq_cpring cycle_rev_cpring. Qed.

Lemma cpring_def : (p : (seq g))
  (if p is (Adds x _) then x = (node x0) else False) ->
  (ufcycle node (rev p)) -> cpring = p.
Proof.
Move=> p; Case Dp: {1}p => // [x p'] Dx; Rewrite: ~Dx in Dp; Move/andP=> [Hp Up].
Step Dn: (size (rev p)) = (order node (node (node x0))).
  Step Hx0: (rev p (node x0)) By Rewrite: mem_rev Dp /= setU11.
  By Rewrite: (order_cycle Hp Up) // -(fconnect_cycle Hp Hx0) fconnect1.
Rewrite: (cycle_path x0) {1 p}Dp rev_adds last_add_last in Hp.
Move/fpathP: Hp {Up} => [n Dp']; Rewrite: -Dp' size_traject in Dn.
By Rewrite: /cpring /orbit -Dn Dp' rev_rev.
Qed.

Lemma head_cpring : cpring = (Adds (node x0) (behead cpring)).
Proof.
Rewrite: /cpring /orbit -orderSpred /= lastI rev_add_last; Congr Adds.
By Apply Inode; Rewrite: last_traject f_iter orderSpred (iter_order (Inode g)).
Qed.

Lemma head_long_cpring : long_cpring ->
  cpring = (Adds (node x0) (Adds x0 (Adds (face (edge x0)) (drop (3) cpring)))).
Proof.
Move: {}cycle_rev_cpring; Rewrite: size_long_cpring head_cpring.
Case: {}cpring => [|x' [|x [|y p]]] //= Hp _; Rewrite: !rev_adds in Hp.
Do 3 Rewrite: -rot1_adds cycle_rot -?add_last_adds in Hp.
Move/and3P: Hp => [Dy Dx _]; Rewrite: -(Inode g (eqP Dx)).
By Rewrite: -{5 x}(eqP Dy) Enode drop0.
Qed.

Lemma head_proper_cpring : proper_cpring ->
  cpring = (Adds (node x0) (Adds x0 (drop (2) cpring))).
Proof.
Case Hx0: long_cpring; LeftBy Rewrite head_long_cpring.
Rewrite: size_proper_cpring leq_eqVlt -size_long_cpring Hx0 orbF.
Rewrite: /cpring size_rev size_orbit /orbit; Case/eqP.
By Move/eqP: Hx0 => Dnx0; Rewrite: -{1 (node x0)}Dnx0 Eedge.
Qed.

End CpRing.

Section ExtConfig.

Variables n0 : nat; g : hypermap; x0 : g.

(* We list all the assumptions on g here so that they appear in the standard *)
(* order, but most of the lemmas below only depend on a few assumptions. In  *)
(* particular, the map constructions do not depend on any assumption on g.   *)

Hypotheses Hpg : (planar g); Hbg : (bridgeless g).
Hypotheses HgE : (plain g); HgN : (quasicubic (rev (cpring x0))).
Hypotheses Hcg : (connected g); Hrg : (proper_cpring x0).

Remark Hg : (ucycle_plain_quasicubic_connected (rev (cpring x0))).
Proof. Repeat Split; Auto; Apply ucycle_rev_cpring. Qed.

(* Reverse ring rotation; note that the map construction matches the ring   *)
(* rotation for arbitrary n0 (it is the identity if n0 >= (order node x0)). *)

Definition ecpR : pointed_map :=
  (PointedMap (iter (subn (order node x0) n0) node x0)).

Definition icpR [x : g] : ecpR := x.

Lemma cpring_ecpR : (cpring ecpR) = (rot n0 (cpring x0)).
Proof.
Apply cpring_def; RightBy Rewrite: rev_rot ucycle_rotr; Apply ucycle_rev_cpring.
Rewrite: /cpring -rev_rotr /rotr size_orbit /=.
Pose m := (order node (node (node x0))).
Step []: m = (order node x0) By Apply: eq_card => [x]; Rewrite: -!cnode1.
Case: (subn m n0) (leq_subr n0 m) => [|n] Hn.
  By Rewrite: rot0 -/(cpring x0) head_cpring. 
Rewrite: /rot rev_cat (take_sub (node (node x0))); RightBy Rewrite size_orbit.
By Rewrite: rev_add_last /= /orbit -/m sub_traject // !iter_f.
Qed.

Lemma size_cpring_ecpR : (size (cpring ecpR)) = (size (cpring x0)).
Proof. By Rewrite: cpring_ecpR size_rot. Qed.

Lemma cubic_ecpR : (quasicubic (rev (cpring ecpR))).
Proof.
Apply: etrans HgN; Apply: eq_subset => [x]; Congr negb.
By Rewrite: cpring_ecpR !mem_rev mem_rot.
Qed.

(* Merging neighbors; this trivially produces a plain graph, but otherwise *)
(* it has very few properties; fortunately, we only need the preservation  *)
(* of face connectivity, since we only use the merge to build contract     *)
(* coloring maps. To make sure this property is always true, we must check *)
(* whether the neighbors are already merged, in which case we need to      *)
(* create a hyperedge to avoid the creation of a separate componenet.      *)
(*    The merge operation breaks both the cface and edge relation, but in  *)
(* the right direction for cface (the resulting map is more connected than *)
(* the base one), and it preserves the adj relation, which is enough for   *)
(* colorings.                                                              *)


Definition ecpA_edge [x : g] : g :=
  if (negb (cface (edge x0) (node x0))) then (edge x) else
  if x =d x0 then (edge (node (node x0))) else
  if x =d (node (node x0)) then (edge x0) else (edge x).

Definition ecpA_node [x : g] : g :=
  if x =d (node x0) then x0 else
  if (node x) =d x0 then (node (node x0)) else (node x).

Definition ecpA_face [x : g] : g :=
  if (cface (edge x0) (node x0)) then (face x) else
  if x =d (edge x0) then (node x0) else
  if (face x) =d (node x0) then (face (edge x0)) else (face x).

Lemma ecpAP : (monic3 ecpA_edge ecpA_node ecpA_face).
Proof.
Move=> x; Rewrite: /ecpA_edge /ecpA_face.
Case (cface (edge x0) (node x0)); Rewrite: /= /ecpA_node.
  Case Dx: (x =d x0); LeftBy Rewrite: Enode set11 (eqP Dx).
  Case Dx': (x =d (node (node x0))); Rewrite: -(inj_eqd (Inode g)) Eedge.
    By Rewrite: -(eqP Dx') set11 eqd_sym Dx.
  By Rewrite: Dx' Dx.
Rewrite: (inj_eqd (Iedge g)); Case Dx: (x =d x0); LeftBy Rewrite: set11 (eqP Dx).
Case Dfex: ((face (edge x)) =d (node x0)).
  By Rewrite: -(eqP Dfex) -(inj_eqd (Inode g)) !Eedge eqd_sym Dx set11.
By Rewrite: Dfex Eedge Dx.
Qed.

Definition ecpA : pointed_map :=
  (PointedMap (face (!edge (Hypermap ecpAP) (face (edge x0))))).

Definition icpA [x : g] : ecpA := x.

Lemma baseN_ecpA : (rel_base icpA (eqdf node) (eqdf node)
      (setC (set2 (node x0) (face (edge x0))))).
Proof.
Rewrite: /icpA /= /eqdf /ecpA_node; Move=> x; Move/norP=> [Hx1 Hx2] y.
By Rewrite: (monic2F_eqd (Enode g)) !(eqd_sym x) (negbE Hx1) (negbE Hx2).
Qed.

Lemma cpring_ecpA :
  (cpring ecpA) =
     (if (long_cpring x0) then (behead (behead (cpring x0))) else (cpring x0)).
Proof.
Case Hx0: (long_cpring x0).
  Apply cpring_def; LeftBy Rewrite: (head_long_cpring Hx0) /= ecpAP.
  Apply/andP; Split;
    RightBy Move: (uniq_cpring x0); Rewrite: uniq_rev (head_long_cpring Hx0);
            Case/and3P.
  Move: (cycle_rev_cpring x0); Rewrite: (head_long_cpring Hx0) /= !rev_adds.
  Do 4 Rewrite: -rot1_adds cycle_rot -?add_last_adds.
  Rewrite: /=; Case/and3P; Do 2 Clear.
  Step Eptr: (ecpA_node (face (edge x0))) = (node (node x0)).
    Rewrite: /ecpA_node -(inj_eqd (Inode g)) Eedge set11.
    By Case Dx0: (x0 =d (node (node x0))); Rewrite: // -(eqP Dx0).
  Case Dp: (rev (drop (3) (cpring x0))) => [|x p]; LeftBy Rewrite: /eqdf /= Eptr.
  Rewrite: /= {3}/eqdf Eptr -(path_maps baseN_ecpA) /icpA ?maps_id //.
  Rewrite belast_add_last; Apply: (elimT subsetP); Rewrite: -disjoint_subset.
  Rewrite: disjoint_sym -[y,z : g](eq_disjoint (mem_seq2 y z)) disjoint_has /=.
  Move: (uniq_cpring x0); Rewrite: (head_long_cpring Hx0) /=.
  Case/and4P; Do 2 (Case/norP; Clear); Move=> Hfex0 _ Hnx0 _.
  Rewrite: -mem_rev Dp /= in Hfex0; Rewrite: -mem_rev Dp /= in Hnx0.
  By Rewrite: (negbE Hfex0) (negbE Hnx0).
Apply cpring_def; LeftBy Move/eqP: Hx0 => Dx0; Rewrite: head_cpring /= ecpAP.
Rewrite: /ucycle uniq_rev /= uniq_cpring andbT.
Move: Hx0 (cycle_rev_cpring x0) (uniq_cpring x0).
Rewrite: size_long_cpring head_cpring /= /eqdf /ecpA_node.
Case: (behead (cpring x0)) => [|x [|y p]] //= _;
 Rewrite: !andbT !set11 !(inj_eqd (Inode g)) eqd_sym // /setU1 orbF.
Case/andP; Case/eqP {x}; Clear; Move/negPf=> Hx0.
By Rewrite: -(eqd_sym x0) Hx0 !set11.
Qed.

Definition sub2ifgt2 [n : nat] : nat :=
  if n is (S (S (S n'))) then (S n') else n.

Lemma size_cpring_ecpA : (size (cpring ecpA)) = (sub2ifgt2 (size (cpring x0))).
Proof.
Rewrite: cpring_ecpA /=; Case Hx0: (long_cpring x0).
  By Rewrite: head_long_cpring.
By Move: Hx0; Rewrite: size_long_cpring; Case: (size (cpring x0)) => [|[|[|n]]].
Qed.

Lemma baseF_ecpA :
   (rel_base icpA (eqdf face) (eqdf face)
      (setC (set2 (edge x0) (edge (node (node x0)))))).
Proof.
Rewrite: /icpA /= /eqdf /ecpA_face; Move=> x; Move/norP=> [Hx1 Hx2] y.
Case (cface (edge x0) (node x0)); LeftDone.
By Rewrite: (monic2F_eqd (Eface g)) !(eqd_sym x) (negbE Hx1) (negbE Hx2).
Qed.

Lemma ecpA_merge: (cface (node ecpA) (node x0)).
Proof.
Rewrite: /= ecpAP; Case Hx02: (cface (edge x0) (node x0)).
  By Rewrite: /= /ecpA_face Hx02; Rewrite: cface1 in Hx02.
Step Hx01: (cface (node x0) (edge (node (node x0)))).
  By Rewrite: cface1r Enode connect0.
Case/connectP: Hx01; Move=> p0; Case/shortenP=> [p Hp Up _] {p0} Ep.
Rewrite: -(path_maps baseF_ecpA) /icpA maps_id in Hp.
  Rewrite: (Sface ecpA); Apply connect_trans with (edge (node (node x0))).
    By Apply/connectP; Exists p.
  Apply connect1; Apply/eqP; Rewrite: /eqdf /= /ecpA_face Hx02.
  Rewrite: -(inj_eqd (Iface g)) Enode set11.
  By Case: ((node x0) =P (face (edge x0))).
Rewrite: lastI Ep uniq_add_last in Up; Move/andP: Up => [Hpx01 _].
Move=> x Hx; Apply/orP; Case; Move/eqP=> Dx; RightBy Case/idP: Hpx01; Rewrite Dx.
By Case/idP: Hx02; Rewrite: Sface Dx; Apply (path_connect Hp); Apply mem_belast.
Qed.

Lemma sub_cface_icpA : (sub_rel cface::(rel g) cface::(rel ecpA)).
Proof.
Apply: connect_sub => [x y]; Case/eqP {y}.
Rewrite: (!cface1 ecpA) /= {2}/ecpA_face.
Case Hx02: (cface (edge x0) (node x0)); LeftBy Rewrite connect0.
Def: Hx01 := ecpA_merge; Rewrite: /= ecpAP in Hx01.
Case: (x =P (edge x0)) => [Dx|_]; LeftBy Rewrite: Dx (Sface ecpA).
By Case: ((face x) =P (node x0)) => [Dx|_]; [Rewrite Dx | Rewrite connect0].
Qed.

Lemma cface_icpA : (x, y : g)
  (cface x::ecpA y) =
    (orb (cface x y) (all (fband (seq2 (face (edge x0)) (node x0))) (seq2 x y))).
Proof.
Pose a := (fband (seq2 (face (edge x0)) (node x0))).
Case: (strict_adjunction 3!id 4!(!eqdf g face) (Sface ecpA) 7!(setC a)) => //.
        Apply: setC_closed; Apply: fbandF.
      By Move=> x.
    Apply/subsetP=> [x _]; Apply/set0Pn; Exists x; Apply: set11.
  Move=> x Hx y; Symmetry; Apply: baseF_ecpA; Apply/orP; Rewrite: /icpA in Hx *.
  Case; Move/eqP=> Dx; Case/idP: Hx; Rewrite: /a /id /= -~{x}Dx ?fconnect1 //.
  By Rewrite: orbC cface1 Enode connect0.
Rewrite: /id /setC /=; Move=> _ Ha x y; Rewrite: orbC.
Case Hx: (a x); RightBy Apply: Ha; Rewrite: Hx.
Case Hy: (a y); RightBy Rewrite: Sface (Sface ecpA); Apply: Ha; Rewrite: Hy.
Rewrite: /a /fband in Hx Hy; Case/hasP: Hx => [x' Dx' Hxx'].
Apply: (connect_trans (sub_cface_icpA Hxx')) {x Hxx'}.
Case/hasP: Hy => [y' Dy' Hyy']; Rewrite: Sface in Hyy'.
Apply: (connect_trans ? (sub_cface_icpA Hyy')) {y Hyy'}.
Def: Hx01 := ecpA_merge; Rewrite: /= ecpAP in Hx01.
Move: Dx' Dy'; Rewrite: !mem_seq2.
By Do 2 (Case/orP; Case/eqP); Rewrite: ?connect0 // (Sface ecpA).
Qed.

Lemma sub_adj_icpA : (sub_rel adj::(rel g) adj::(rel ecpA)).
Proof.
Move=> x y; Case/adjP=> [z Hxz Hzy]; Apply/adjP.
Exists z; Apply: sub_cface_icpA; Rewrite: //= /ecpA_edge.
Case Hx0: (cface (edge x0) (node x0)) => //=.
Case: (z =P x0) => [Dz|_]; LeftBy Rewrite: cface1 Enode -(same_cface Hx0) -Dz.
Case: (z =P (node (node x0))) => [Dz|_]; RightDone.
By Rewrite: (same_cface Hx0) -{(node x0)}Enode -Dz -cface1.
Qed.

(* The two basic extension constructions. Since they both add an edge pair, *)
(* they share the common underlying dart set construction. We use a special *)
(* purpose concrete type, rather than the general set sum, so that case     *)
(* analysis will be better behaved.                                         *)

Inductive ecp_dart : Set :=
  IcpX : ecp_dart
| IcpXe : ecp_dart
| Icp : g -> ecp_dart.

Lemma ecp_inj : (injective Icp). Proof. By Move=> x y Hxy; Injection Hxy. Qed.

Definition ecp_eq [x, y : ecp_dart] : bool :=
  Cases x y of
    IcpX IcpX => true
  | IcpXe IcpXe => true
  | (Icp x') (Icp y') => x' =d y'
  | _ _ => false
  end.

Lemma ecp_eqP : (reflect_eq ecp_eq).
Proof.
Move=> [||x] [||y]; Try By Constructor.
By Apply: (iffP eqP) => [[] | H]; RightBy Injection: H.
Qed.

Canonical Structure ecp_dartData := (DataSet ecp_eqP).

Lemma ecp_enumP : (x : ecp_dart)
  (count (set1 x) (Adds IcpX (Adds IcpXe (maps Icp (enum g))))) = (1).
Proof.
Move=> [||x];
  Try By Apply: eqP; Rewrite: /= /addn /= eqdSS -leqn0 leqNgt;
      Rewrite:  -has_count has_set1; Apply/mapsP; Case.
Rewrite: /= !add0n count_filter filter_maps size_maps -count_filter.
Exact (count_set1_enum x).
Qed.

Canonical Structure ecp_dartEnum := (FinSet ecp_enumP).

Lemma card_ecp : (card ecp_dartEnum) = (S (S (card g))).
Proof. By Rewrite: !cardA /= size_maps. Qed.

Definition ecp_edge [x : ecp_dart] : ecp_dart :=
  Cases x of
    IcpX => IcpXe
  | IcpXe => IcpX
  | (Icp x') => (Icp (edge x'))
  end.

Definition ecpU_node [x : ecp_dart] : ecp_dart :=
  Cases x of
    IcpX => IcpXe
  | IcpXe => (Icp (node (node x0)))
  | (Icp y) => if y =d (node x0) then IcpX else (Icp (node y))
  end.

Definition ecpU_face [x : ecp_dart] : ecp_dart :=
  Cases x of
    IcpX => IcpX
  | IcpXe => (Icp (node x0))
  | (Icp y) => if (face y) =d (node x0) then IcpXe else (Icp (face y))
  end.

Lemma ecpUP : (monic3 ecp_edge ecpU_node ecpU_face).
Proof.
Move=> [||x] //=; LeftBy Rewrite: set11.
Case Hfex: ((face (edge x)) =d (node x0)); LeftBy Rewrite: /= -(eqP Hfex) Eedge.
By Rewrite: /= Hfex Eedge.
Qed.

Definition ecpU : pointed_map := (PointedMap IcpX::(Hypermap ecpUP)).

Definition icpU : g -> ecpU := Icp.

Lemma icpU_inj : (injective icpU). Proof. Exact ecp_inj. Qed.

Lemma icpU_edge : (x : g) (icpU (edge x)) = (edge (icpU x)). Proof. Done. Qed.

(* The N step is a K step applied immediately to the left of the ring head.   *)
(* We get the K step below by composition with R steps, and the H and Y steps *)
(* by composition with a U step.                                              *)

Definition ecpN_node [x : ecp_dart] : ecp_dart :=
  Cases x of
    IcpX =>
    if (long_cpring x0) then (Icp (node x0)) else IcpX
  | IcpXe =>
    (Icp (face (edge x0)))
  | (Icp y) =>
     if y =d x0 then IcpXe else
     if (node (node y)) =d x0  then IcpX else (Icp (node y))
  end.

Definition ecpN_face [x : ecp_dart] : ecp_dart :=
  Cases x of
    IcpX =>
   (Icp x0)
  | IcpXe =>
    if (long_cpring x0) then (Icp (face (edge (face (edge x0))))) else IcpX
  | (Icp y) =>
    if y =d (edge (face (edge x0))) then IcpXe else
    if y =d (edge (node x0)) then IcpX else (Icp (face y))
  end.

Lemma ecpNP : (monic3 ecp_edge ecpN_node ecpN_face).
Proof.
Move=> [||x]; Rewrite: /= ?set11 //.
  Case Hx0: (long_cpring x0) => /=; RightBy Rewrite: Hx0.
  By Rewrite: -(inj_eqd (Inode g)) !Eedge set11 (negbE Hx0).
Rewrite: !(inj_eqd (Iedge g)) -(monic2F_eqd (Enode g)).
Case Dnx: ((node x) =d x0); LeftBy Rewrite: /= -(eqP Dnx) Enode.
Case Dx: (x =d (node x0)) => /=.
  By Rewrite: /= /long_cpring eqd_sym -(monic2F_eqd (Enode g)) -(eqP Dx) Dnx.
By Rewrite: -(inj_eqd (Inode g)) Eedge Dx Dnx.
Qed.

Definition ecpN : pointed_map := (PointedMap IcpX::(Hypermap ecpNP)).

Definition icpN : g -> ecpN := Icp.

Lemma icpN_inj : (injective icpN). Proof. Exact ecp_inj. Qed.

Lemma icpN_edge : (x : g) (icpN (edge x)) = (edge (icpN x)). Proof. Done. Qed.

Lemma plain_ecpU : (plain ecpU).
Proof.
Apply/plainP; Move=> [||x] // _; Case: (plainP HgE x) => // [Dx Hx] /=.
By Rewrite: Dx; Split.
Qed.

Lemma plain_ecpN : (plain ecpN).
Proof. Exact plain_ecpU. Qed.

Lemma baseN_ecpU :
  (rel_base Icp (!eqdf ecpU node) (eqdf node) (setC1 (Icp (node x0)))).
Proof.
Move=> x; Rewrite: /setC1 /eqd /eqdf /= eqd_sym.
By Move/negPf=> Hx; Rewrite: Hx.
Qed.

Lemma icpU_node : (x : g) (negb (seq1 (node x0) x)) ->
  (node (icpU x)) = (icpU (node x)).
Proof.
Move=> x; Rewrite: mem_seq1; Move=> HxnX.
By Rewrite: /= eqd_sym (negbE HxnX).
Qed.

Lemma cpring_ecpU :
  (cpring ecpU) = (Adds (node ecpU) (Adds ecpU (maps icpU (cpring x0)))).
Proof.
Apply: cpring_def => //; Apply/andP; Split.
  Move: (uniq_cpring x0) (cycle_rev_cpring x0); Rewrite: head_cpring /=.
  Rewrite: !rev_adds -maps_rev -mem_rev -uniq_rev.
  Move: (rev (behead (cpring x0))) => p; Move/andP=> [Up _].
  Do 4 Rewrite: -rot1_adds cycle_rot -?add_last_adds.
  Rewrite: /= {2}/eqdf /= !set11 /= -maps_add_last.
  Case: p Up => [|x p] Up //=; Rewrite: (path_maps baseN_ecpU) //.
  Rewrite: belast_add_last; Move=> y Hy; Apply/eqP=> [Dy]; Case/idPn: Hy.
  By Rewrite: -Dy (mem_maps ecp_inj).
Rewrite: uniq_rev /= /setU1 /= (uniq_maps ecp_inj) uniq_cpring andbT.
By Apply/andP; Split; Apply/mapsP; Case.
Qed.

Lemma size_cpring_ecpU : (size (cpring ecpU)) = (S (S (size (cpring x0)))).
Proof. By Rewrite: cpring_ecpU /= size_maps. Qed.

Lemma cubic_ecpU : (quasicubic (rev (cpring ecpU))).
Proof.
Rewrite: cpring_ecpU; Apply/cubicP=> [u]; Rewrite: /setC mem_rev /= /setU1.
Case: u => [||x] //=; Rewrite: (mem_maps ecp_inj) -mem_rev; Move=> Hx.
Case: (cubicP HgN ? Hx) => [Dn3x Hn1x]; Rewrite: mem_rev mem_cpring in Hx.
Case: (x =P (node x0)) => [Dx|_]; LeftBy Rewrite: Dx fconnect1 in Hx.
Split; RightDone; Rewrite: /= (inj_eqd (Inode g)).
Case: (x =P x0) => [Dx|_]; LeftBy Rewrite: Dx connect0 in Hx.
Rewrite: /= (inj_eqd (Inode g)) Dn3x.
By Case: ((node x) =P x0) => [Dnx | _] //; Rewrite: -Dnx Snode fconnect1 in Hx.
Qed.

Lemma baseN_ecpN :
  (rel_base icpN (eqdf node) (eqdf node)
     (setC (set2 (Icp x0) (Icp (face (edge (face (edge x0)))))))).
Proof.
Move=> x; Rewrite: /setC /icpN /set2 /eqd /eqdf /= -!(eqd_sym x).
Rewrite: -!(monic2F_eqd (Enode g)).
By Move/norP=> [Hx Hnnx]; Rewrite: (negbE Hx) (negbE Hnnx).
Qed.

Lemma cpring_ecpN :
  (cpring ecpN) =
    (if (long_cpring x0) then 
      (Adds (icpN (node x0)) (Adds ecpN (maps icpN (drop (3) (cpring x0)))))
     else (seq1 ecpN)).
Proof.
Case Hx0: (long_cpring x0);
  RightBy Apply cpring_def; Rewrite: /ucycle /= /eqdf /ecpN_node Hx0 ?set11.
Apply cpring_def; LeftBy Rewrite: /= Hx0.
Apply/andP; Split.
  Move: (uniq_cpring x0) (cycle_rev_cpring x0).
  Rewrite: (head_long_cpring Hx0) /= drop0; Move: (drop (3) (cpring x0)) => p.
  Rewrite: !rev_adds -maps_rev /setU1 -!(mem_rev p) -uniq_rev (negbE Hx0) /=.
  Move/rev: p => p; Case/and4P; Move/norP=> [Hnx0 Unx0]; Move/norP=> [_ Ux0] _.
  Move=> Up; Do 5 Rewrite: -rot1_adds cycle_rot -?add_last_adds.
  Rewrite: (cycle_path x0) (cycle_path IcpX) /= last_maps.
  Case/and4P; Move/eqP=> Ep _ _ Hp.
  Move: {}baseN_ecpN => HbN; Rewrite: /icpN /= in HbN.
  Rewrite: {1 2}/eqdf {1 2}/ecpN_node Hx0 !set11 /= (path_maps HbN).
    By Rewrite: -(inj_eqd (Inode g)) Ep Hp (negbE Hx0) Eedge !set11.
  Rewrite: -Ep Enode; Move=> x Hx; Apply/orP.
  Case; Move/eqP=> Dx; Rewrite: -~{x}Dx (mem_maps ecp_inj) in Hx.
    By Case/norP: (mem_belast Hx); Split; LeftBy Rewrite eqd_sym.
  Step Up': (uniq (Adds (node x0) p)) By Rewrite: /= Unx0.
  By Rewrite: lastI uniq_add_last Hx in Up'.
Move: (uniq_cpring x0); Rewrite: (head_long_cpring Hx0) uniq_rev /= drop0.
Move: (drop (3) (cpring x0)) => p; Rewrite: /setU1 /= (uniq_maps ecp_inj).
Rewrite: (mem_maps ecp_inj) orbA orbC; Case/and4P.
By Move/norP=> [Unx0 _] _ _ Up; Rewrite: Unx0 Up /= andbT; Apply/mapsP; Case.
Qed.

Lemma rot1_cpring_ecpN :
  (rot (1) (cpring ecpN)) =
    (Adds ecpN (maps icpN (drop (2) (rot (1) (cpring x0))))).
Proof.
Rewrite cpring_ecpN; Case Hx0: (long_cpring x0).
  By Rewrite: (head_long_cpring Hx0) /= !drop0 maps_cat.
By Move: Hx0; Rewrite size_long_cpring; Case: (cpring x0) => [|x [|y [|z p]]].
Qed.

Lemma size_cpring_ecpN :
  (size (cpring ecpN)) = (S (pred (pred (size (cpring x0))))).
Proof.
Rewrite: -(size_rot (1)) rot1_cpring_ecpN drop_behead.
By Rewrite: /= size_maps !size_behead size_rot.
Qed.

Lemma cubic_ecpN : (quasicubic (rev (cpring ecpN))).
Proof.
Pose qXe := (seq3 IcpXe::ecpN (Icp (face (edge x0))) (Icp x0)).
Step HqXe: (cubicb qXe).
  Step HqXeN: (fcycle node qXe).
    Rewrite: /= /eqdf /= !set11 -(inj_eqd (Inode g)) Eedge -(eqd_sym x0).
    By Rewrite: (negbE Hrg) set11.
  Apply/subsetP=> [u Hu]; Rewrite: /order_set (order_cycle HqXeN) //.
  By Rewrite: /= /setU1 /eqd /= -(monic2F_eqd (Enode g)) eqd_sym (negbE Hrg).
Apply/cubicP=> [u]; Rewrite: /setC mem_rev -(mem_rot (1)) rot1_cpring_ecpN.
Case HqXeu: (qXe u); LeftBy Clear; Exact (cubicP HqXe ? HqXeu).
Case: u HqXeu => [||x] //=.
Rewrite: /setU1 orbF (mem_maps ecp_inj) /= {1 2}/eqd /= !(eqd_sym x).
Move/norP=> [Hfex0x Hx0x] Hx'; Rewrite (negbE Hx0x).
Step Hx: (negb (rev (cpring x0) x)).
  Case Hx0': (long_cpring x0).
    Move: Hx'; Rewrite: (head_long_cpring Hx0') rot1_adds /= drop0 mem_add_last.
    By Rewrite: /= mem_rev /= /setU1 (negbE Hx0x) (negbE Hfex0x).
  Rewrite: mem_rev mem_cpring fconnect_orbit /orbit.
  Move: {}Hx0' {Hx'}; Rewrite: size_long_cpring size_cpring -orderSpred /=.
  Rewrite: /setU1 (negbE Hx0x); Case: (pred (order node x0)) => [|[|n]] //=.
  By Case/eqP: Hx0'; Rewrite: /setU1 orbF.
Case: (cubicP HgN ? Hx) => [Dn3x Hn1x]; Rewrite: mem_rev mem_cpring in Hx.
Case Hnnx: ((node (node x)) =d x0).
  By Rewrite: 2!cnode1r (eqP Hnnx) connect0 in Hx.
Rewrite: eqd_sym -(monic2F_eqd (Enode g)) in Hfex0x.
Split; RightDone; Rewrite: /= (negbE Hfex0x) Dn3x eqd_sym (negbE Hx0x) /= Hnnx.
By Rewrite: Dn3x (negbE Hfex0x).
Qed.

Lemma connected_ecpU : (connected ecpU).
Proof.
Apply/eqP; Case (n_comp_connect (Sglink ecpU) IcpX); Symmetry.
Step HXe: (gcomp IcpX::ecpU IcpXe).
  By Apply: (connect_trans (connect1 (glinkE ?)) ?); Rewrite: /= connect0.
Step Hnnx0: (gcomp IcpX::ecpU (Icp (node (node x0)))).
  By Do 2 Apply: (connect_trans (connect1 (glinkN ?)) ?); Rewrite: /= connect0.
Apply: eq_n_comp_r => [[||x]]; Rewrite: /setA //; LeftBy Apply: connect0.
Case: (connected_clink Hcg x (node (node x0))); Move=> p.
Elim: p x => [|y p Hrec] x /=; LeftBy Move=> _ Dx; Rewrite Dx.
Case/andP; Move/clinkP=> [Dx | Dy] Hp Ep;
  Move: {p Hrec Hp Ep}(Hrec ? Hp Ep) => Hrec.
  Move: {Hrec}(connect_trans Hrec (connect1 (glinkN ?))) => /=.
  By Rewrite: -Dx; Case: (y =P (node x0)) => [Dy | _] // _; Rewrite: Dx Dy.
Rewrite: (Sglink ecpU); Apply: (connect_trans (connect1 (glinkF ?)) ?).
By Rewrite: (Sglink ecpU) /= Dy; Case (y =d (node x0)).
Qed.

Lemma connected_ecpN : (connected ecpN).
Proof.
Apply/eqP; Case (n_comp_connect (Sglink ecpN) IcpX); Symmetry.
Step HXe: (gcomp IcpX::ecpN IcpXe).
  By Apply: (connect_trans (connect1 (glinkE ?)) ?); Rewrite: /= connect0.
Step Hx0: (gcomp IcpX::ecpN (Icp x0)).
  By Apply: (connect_trans (connect1 (glinkF ?)) ?); Rewrite: /= connect0.
Step Hfex0: (gcomp IcpX::ecpN (Icp (face (edge x0)))).
  Apply: (connect_trans (connect_trans HXe (connect1 (glinkN ?))) ?).
  By Rewrite: /= connect0.
Step Hnx0: (gcomp IcpX::ecpN (Icp (node x0))).
  Case Hx0p: (long_cpring x0); RightBy Case/eqP: Hx0p.
  By Apply: (connect_trans (connect1 (glinkN ?)) ?); Rewrite: /= Hx0p connect0.
Apply: eq_n_comp_r => [[||x]]; Rewrite: /setA //; LeftBy Apply: connect0.
Case: (connected_clink Hcg x x0); Move=> p.
Elim: p x => [|y p Hrec] x /=; LeftBy Move=> _ Dx; Rewrite Dx.
Case/andP; Move/clinkP=> [Dx | Dy] Hp Ep;
  Move: {p Hrec Hp Ep}(Hrec ? Hp Ep) => Hrec.
  Move: {Hrec}(connect_trans Hrec (connect1 (glinkN ?))) => /=.
  Rewrite: -Dx; Case: (y =P x0) => [Dy|_]; LeftBy Rewrite: Dx Dy.
  By Case: ((node x) =P x0) => [Dnx | _]; LeftBy Rewrite: -{x}Enode Dnx.
Rewrite: (Sglink ecpN); Apply: (connect_trans (connect1 (glinkF ?)) ?).
Rewrite: (Sglink ecpN) /= Dy. Case: (x =d (edge (face (edge x0)))) => //.
By Case (x =d (edge (node x0))); LeftBy Rewrite connect0.
Qed.

Lemma cface_ecpU : (cface ecpU) =1 (set1 ecpU).
Proof. By Move=> u; Rewrite: -mem_seq1; Apply: fconnect_cycle. Qed.

Lemma closedF_ecpU : (fclosed face (setC1 ecpU)).
Proof.
By Move=> u v; Case/(? =P v) {v}; Rewrite: /setC1 -!cface_ecpU -cface1r.
Qed.

Lemma adjnF_ecpU :
  (rel_adjunction icpU (eqdf face) (eqdf face) (setC1 ecpU)).
Proof.
Pose h := [u; _: (setC1 IcpX u)]if u is (Icp x) then x else (node x0).
Apply intro_adjunction with h. Apply: Sface. Apply closedF_ecpU.
  Case=> [||x] //= _.
    Split; LeftBy Apply connect1; Rewrite: /eqdf /= set11.
    Case=> [||y] //= _; Rewrite: {1}/eqdf {1}/eqd /=.
    By Case/eqP; Apply connect0.
  Split; LeftBy Apply connect0.
  Case=> [||y] //= _; Rewrite: {1}/eqdf /=; Case: ((face x) =P (node x0)) => //.
    By Case; Clear; Apply fconnect1.
  By Clear; Case/(? =P y); Apply fconnect1.
Move=> x /= _; Split; LeftBy Apply connect0.
Move=> y; Case/eqP {y}; Rewrite: (!cface1 ecpU) /=.
Case: ((face x) =P (node x0)) => [Dx| _]; RightBy Rewrite connect0.
By Rewrite: (!cface1 ecpU) Dx /= connect0.
Qed.

Lemma cface_icpU : (x, y : g) (cface (icpU x) (icpU y)) = (cface x y).
Proof. By Case: {}adjnF_ecpU => [_ H] x y; Rewrite: H. Qed.

Lemma adj_ecpU : (adj ecpU) =1 (fband (seq1 (icpU (node x0)))).
Proof.
Move=> u; Rewrite: /adj /orbit /order (eq_card cface_ecpU) card1 /=.
By Rewrite: /rlink cface1 Sface.
Qed.

Lemma adj_icpU :  (x, y : g) (adj (icpU x) (icpU y)) = (adj x y).
Proof.
Move=> x y; Apply/adjP/adjP=> [[[||z] Hxz Hzy] | [z Hxz Hzy]].
      By Rewrite: Sface cface_ecpU in Hxz.
    By Rewrite: /rlink /= cface_ecpU in Hzy.
  By Exists z; Rewrite: /rlink -cface_icpU.
By Rewrite: /rlink -!cface_icpU in Hxz Hzy; Exists (icpU z).
Qed.

Lemma fband_icpU : (u : ecpU) {x : g | (cface u (icpU x))} + {(cface ecpU u)}.
Proof.
Move=> u; Case Hu: (cface ecpU u); [By Right | Left; Move: Hu].
Rewrite: cface_ecpU; Case: u => [||x] // _.
  By Exists (node x0); Rewrite: cface1 /= cface_icpU connect0.
By Exists x; Rewrite: cface_icpU connect0.
Qed.

Lemma bridgeless_ecpU : (bridgeless ecpU).
Proof.
Step HXF : (cface ecpU IcpXe) = false By Rewrite: cface_ecpU.
Apply/set0P => [[||x]] //; LeftBy Rewrite: Sface.
By Case: {}adjnF_ecpU => /= [_ EfF]; Rewrite: -EfF // (set0P Hbg).
Qed.

Lemma planar_ecpU : (planar ecpU).
Proof.
Step Hcp: (fcard face ecpU) = (S (fcard face g)).
  Rewrite: (n_compC (set1 ecpU)) -add1n; Congr addn.
    Rewrite: -(eq_n_comp_r cface_ecpU) n_comp_connect //; Apply: Sface.
  Apply: (etrans (adjunction_n_comp (Sface ?) (Sface ?)
                closedF_ecpU adjnF_ecpU)).
  By Apply: eq_n_comp_r.
Step HecpU: (ucycle_plain_quasicubic_connected (rev (cpring ecpU))).
  Split; [Split; RightBy Apply ucycle_rev_cpring | Exact connected_ecpU].
  Split; [Exact plain_ecpU | Exact cubic_ecpU].
Rewrite: (quasicubic_Euler HecpU).
Rewrite: {(card ecpU)}card_ecp Hcp size_rev size_cpring_ecpU.
Rewrite: head_cpring rev_adds headI /= addnI !doubleS !addSn.
Move: {}Hpg; Rewrite: (quasicubic_Euler Hg).
By Rewrite: size_rev head_cpring rev_adds headI /= addnI !addnS.
Qed.

Lemma cface_ecpN : (cface ecpN (icpN x0)).
Proof. Apply connect1; Apply: set11. Qed.

Lemma adjnF_ecpN :
  (rel_adjunction icpN (eqdf face) (eqdf face) ecpN).
Proof.
Pose h := [u; _: true]Cases u of
           (Icp x) => x
          | IcpX => x0
          | IcpXe => (edge (face (edge x0)))
          end.
Apply intro_adjunction with h. Apply: Sface. Done.
  Case=> [||x] //= _.
      Split; LeftBy Apply connect1; Rewrite: /eqdf /= !set11.
      Case=> [||y] //= _; Rewrite: {1}/eqdf {1}/eqd /=.
      By Case/eqP; Apply connect0.
    Split; LeftBy Rewrite: (!cface1r ecpN) /= set11 connect0.
    Case=> [||y] //= _; Rewrite: ?connect0 // {1}/eqdf /=;
      (Case Hx0: (long_cpring x0) => // [] Dy).
      By Move/eqP: Hx0 => Dx0; Rewrite: Dx0 cface1 Enode connect0.
    By Rewrite: cface1 (? =P y Dy) connect0.
  Split; LeftBy Apply connect0.
  Case=> [||y] //= _; Rewrite: {1}/eqdf /=;
    Case: (x =P (edge (face (edge x0)))) => [[]|_] //; Rewrite: ?connect0 //;
    Case: (x =P (edge (node x0))) => [Dx|_] //.
    By Rewrite: -{x0}Enode -Dx fconnect1.
  By Case/(? =P y); Rewrite fconnect1.
Move=> x /= _; Split; LeftBy Apply connect0.
Move=> y; Case/eqP {y}; Rewrite: (!cface1 ecpN) /=.
Case: (x =P (edge (face (edge x0)))) => [Dx|_].
  Rewrite: (!cface1 ecpN) /= -Dx.
  Case Hx0: (long_cpring x0); LeftBy Rewrite connect0.
  By Move/eqP: Hx0 => Dx0; Rewrite: (!cface1 ecpN) Dx Dx0 Enode /= connect0.
Case: (x =P (edge (node x0))) => [Dx|_]; RightBy Rewrite connect0.
By Rewrite: (!cface1 ecpN) Dx Enode /= connect0.
Qed.

Lemma cface_icpN : (x, y : g) (cface (icpN x) (icpN y)) = (cface x y).
Proof. By Case: {}adjnF_ecpN => [_ H] x y; Rewrite: H. Qed.

Lemma adj_icpN : (x, y : g)
   (adj (icpN x) (icpN y)) =
      (or3b (adj x y)
            (andb (cface (edge (face (edge x0))) x) (cface x0 y))
            (andb (cface (edge (face (edge x0))) y) (cface x0 x))).
Proof.
Move=> x y; Apply/adjP/or3P => [[[||z] Hxz Hzy] | ].
      Constructor 3; Apply/andP; Split.
        By Rewrite: -cface_icpN cface1 /= set11.
      By Rewrite: cface1r /= cface_icpN Sface in Hxz *.
    Constructor 2; Apply/andP; Split.
      By Rewrite: -cface_icpN cface1 Sface /= set11.
    By Rewrite: /rlink cface1 /= cface_icpN in Hzy *.
  By Constructor 1; Apply/adjP; Exists z; Rewrite: /rlink -cface_icpN.  
Case.
    By Case/adjP=> [z Hxz Hzy]; Exists (icpN z); Rewrite: /rlink /= cface_icpN.
  Case/andP=> [Hzx Hzy]; Exists (IcpXe::ecpN).
    By Rewrite: Sface -cface_icpN cface1r /= set11 in Hzx.
  By Rewrite: /rlink cface1 /= cface_icpN.
Case/andP=> [Hzy Hzx]; Exists (IcpX::ecpN).
  By Rewrite: Sface cface1 /= cface_icpN.
By Rewrite: -cface_icpN cface1 /= set11 in Hzy.
Qed.

Lemma sub_adj_icpN : (x, y : g) (adj x y) -> (adj (icpN x) (icpN y)).
Proof. By Move=> x y Hxy; Rewrite: adj_icpN Hxy. Qed.

Lemma fband_icpN : (u : ecpN) {x : g | (cface u (icpN x))}.
Proof.
Case=> [||x].
    By Exists x0; Rewrite: cface1 /= cface_icpN connect0.
  By Exists (edge (face (edge x0))); Rewrite: cface1r /= set11 connect0.
By Exists x; Rewrite: cface_icpN connect0.
Qed.

Lemma planar_ecpN : (planar ecpN).
Proof.
Step Hcp: (fcard face ecpN) = (fcard face g).
  By Apply: (adjunction_n_comp (Sface ?) (Sface ?) ? adjnF_ecpN).
Step HecpN: (ucycle_plain_quasicubic_connected (rev (cpring ecpN))).
  Split; [Split; RightBy Apply ucycle_rev_cpring | Exact connected_ecpN].
  Split; [Exact plain_ecpN | Exact cubic_ecpN].
Rewrite: (quasicubic_Euler HecpN) {(card ecpN)}card_ecp Hcp size_rev.
Rewrite: size_cpring_ecpN head_cpring rev_adds headI /= !doubleS !addSn.
Move: {}Hpg; Rewrite: (quasicubic_Euler Hg).
Rewrite: size_rev size_cpring head_cpring rev_adds headI /= addnI.
Case: (order node x0) (orderSpred node x0) (iter_order (Inode g) x0) => //.
By Case=> [|n] /= _ Dnx0; [Case/eqP: Hrg | Rewrite: !doubleS !addSn !addnS].
Qed.

End ExtConfig.

Lemma ecpR1_eq : (g : hypermap; x0 : g) ((ecpR (1) x0)::g) = (face (edge x0)).
Proof. By Move=> g *; Rewrite: /ecpR /= subn1 -{3 x0}(f_finv (Inode g)) Enode. Qed.

Section CompExtConfig.

Variables n0 : nat; g : hypermap; x0 : g.

Hypotheses Hpg : (planar g); Hbg : (bridgeless g).
Hypotheses HgE : (plain g); HgN : (quasicubic (rev (cpring x0))).
Hypotheses Hcg : (connected g); Hrg : (proper_cpring x0).
Hypothesis Urg : (simple (cpring x0)).

Definition ecpR' : pointed_map := (ecpR (pred (order node x0)) x0).

Definition icpR' : g -> ecpR' := (icpR ? ?).

Lemma ecpR'_eq : (ecpR' :: g) = (node x0).
Proof. By Rewrite: /ecpR' /ecpR /= -orderSpred /= subSnn. Qed.

Definition ecpK : pointed_map := (ecpR (1) (ecpN ecpR')).

Definition icpK [x : g] : ecpK := (icpR (1) (ecpN ecpR') (icpN ecpR' (icpR' x))).

Lemma size_cpring_ecpK :
  (size (cpring ecpK)) = (S (pred (pred (size (cpring x0))))).
Proof.
By Rewrite: /ecpK size_cpring_ecpR size_cpring_ecpN /ecpR' size_cpring_ecpR /=.
Qed.

Lemma icpK_inj : (injective icpK). Proof. By Move=> x y; Injection=> Hxy. Qed.

Lemma icpK_edge : (x : g) (edge (icpK x)) = (icpK (edge x)). Proof. Done. Qed.

Lemma cpring_ecpK :
  (cpring ecpK) = (Adds (node ecpK) (maps icpK (drop (2) (cpring x0)))).
Proof.
Rewrite: /ecpK cpring_ecpR rot1_cpring_ecpN ecpR1_eq Eedge; Congr Adds.
Congr (maps icpK); Congr drop.
Rewrite: /ecpR' cpring_ecpR -subn1 -size_cpring; Apply: rot_rotr.
Qed.

Lemma cface_icpK : (x, y : g) (cface (icpK x) (icpK y)) = (cface x y).
Proof. Exact (cface_icpN ecpR'). Qed.

Lemma adj_icpK : (x, y : g)
  (adj (icpK x) (icpK y)) =
     (or3b (adj x y)
           (andb (cface (edge x0) x) (cface (node x0) y))
           (andb (cface (edge x0) y) (cface (node x0) x))).
Proof.
By Move=> *; Apply: (etrans (adj_icpN ecpR' ? ?)); Rewrite: ecpR'_eq Enode.
Qed.

Lemma sub_adj_icpK : (x, y : g) (adj x y) -> (adj (icpK x) (icpK y)).
Proof. By Move=> x y Hxy; Rewrite: adj_icpK Hxy. Qed.

Lemma cface_node_ecpK : (cface (node ecpK) (icpK (node x0))).
Proof. Rewrite: /ecpK ecpR1_eq Eedge ecpR'_eq; Apply: cface_ecpN. Qed.

Lemma cface_ecpK : (cface ecpK (icpK (face (edge x0)))).
Proof.
Rewrite: /ecpK ecpR1_eq ecpR'_eq /= Enode.
Case Hx0: (long_cpring (node x0)); LeftBy Apply: connect0.
Apply: connect1; Apply/eqP=> /=; Move/eqP: Hx0 => Dx0.
By Rewrite: -{(node x0)}Enode -Dx0 Enode.
Qed.

Lemma fband_icpK : (u : ecpK) {x : g | (cface u (icpK x))}.
Proof. Exact (fband_icpN 2!ecpR'). Qed.

Definition ecpY : pointed_map := (ecpN (ecpU x0)).

Lemma plain_ecpY : (plain ecpY).
Proof. By Do 2 Apply: plain_ecpN. Qed.

Lemma cubic_ecpY : (quasicubic (rev (cpring ecpY))).
Proof. By Apply: cubic_ecpN => //; Apply: cubic_ecpU. Qed.

Lemma size_cpring_ecpY : (size (cpring ecpY)) = (S (size (cpring x0))).
Proof. By Rewrite: /ecpY size_cpring_ecpN size_cpring_ecpU /=. Qed.

Lemma planar_ecpY : (planar ecpY).
Proof.
Apply: planar_ecpN => //.
 By Apply planar_ecpU.
 By Apply plain_ecpU.
 By Apply: cubic_ecpU.
 By Apply connected_ecpU.
Qed.

Lemma connected_ecpY : (connected ecpY).
Proof. By Apply: connected_ecpN; Apply connected_ecpU. Qed.

Definition icpY [x : g] : ecpY := (icpN ? (icpU x0 x)).

Lemma icpY_inj : (injective icpY). Proof. By Move=> x y; Injection=> *. Qed.

Lemma icpY_edge : (x : g) (edge (icpY x)) = (icpY (edge x)). Proof. Done. Qed.

Lemma icpY_node : (x : g) (negb (seq2 (node x0) x0 x)) ->
  (node (icpY x)) = (icpY (node x)).
Proof.
Move=> x; Rewrite: mem_seq2; Move/norP=> [HxnX HxX].
Rewrite: /= (eqd_sym x) (negbE HxnX) /= (inj_eqd (Inode g)).
By Rewrite: (eqd_sym x)  (negbE HxX).
Qed.

Lemma drop2_cpring_ecpY :
  (drop (2) (cpring ecpY)) = (maps icpY (behead (cpring x0))).
Proof.
By Rewrite: /ecpY cpring_ecpN cpring_ecpU head_cpring /= !drop0 -maps_comp.
Qed.

Lemma cpring_ecpY :
  (cpring ecpY) = (Adds (node ecpY) (Adds ecpY (maps icpY (behead (cpring x0))))).
Proof. By Rewrite: -drop2_cpring_ecpY -head_proper_cpring. Qed.

Lemma cface_icpY : (x, y : g) (cface (icpY x) (icpY y)) = (cface x y).
Proof. By Move=> x y; Rewrite: /icpY /ecpY cface_icpN cface_icpU. Qed.

Lemma adj_icpY : (x, y : g) (adj (icpY x) (icpY y)) = (adj x y).
Proof.
By Move=> *; Rewrite: /icpY /ecpY adj_icpN adj_icpU !cface_ecpU /= !andbF !orbF.
Qed.

Lemma cface_node_ecpY : (cface (node ecpY) (icpY (node x0))).
Proof.
Rewrite: cface1; Apply: (etrans (cface_icpY ? ?)); Apply connect0.
Qed.

Lemma cface_ecpY : (cface ecpY) =1 (seq2 ecpY (face ecpY)).
Proof. By Apply: fconnect_cycle. Qed.

Lemma adj_ecpY : (adj ecpY) =1 (fband (maps icpY (seq2 (node x0) x0))).
Proof.
Move=> u; Apply/adjP/hasP => [[v Hv Huv]].
  Rewrite: cface_ecpY mem_seq2 in Hv; Case/orP: Hv Huv; Case/eqP; Move=> Hu.
    Exists (icpY x0); LeftBy Rewrite: (mem_maps icpY_inj) mem_seq2 set22.
    By Rewrite: /rlink cface1 Sface /= Enode (negbE Hrg) in Hu.
  Exists (icpY (node x0)); LeftBy Rewrite: (mem_maps icpY_inj) mem_seq2 set21.
  By Rewrite: /rlink cface1 Sface in Hu.
Exists (node v); RightBy Rewrite: /rlink cface1 Enode Sface.
Rewrite: cface_ecpY mem_seq2 ~{Huv}; Apply/orP.
Repeat Case/setU1P: Hv => [[]| Hv] //=; LeftBy Rewrite set11; Right.
By Left; Rewrite: (negbE Hrg) /= !set11.
Qed.

Lemma fband_icpY : (u : ecpY) {x : g | (cface u (icpY x))} + {(cface ecpY u)}.
Proof.
Move=> u; Case: (fband_icpN u) => [v Huv].
Case: (fband_icpU v) => [[x Hxv] | Hv]; [Left | Right].
  By Exists x; Rewrite: (same_cface Huv) /icpY cface_icpN.
Rewrite: cface1 Sface (same_cface Huv) Sface.
By Rewrite: -(cface_icpN (ecpU x0)) in Hv.
Qed.

Lemma bridgeless_ecpY : (bridgeless ecpY).
Proof.
Def: Hu0 := (cface_ecpY (edge ecpY)).
Def: Hfu0 := (cface_ecpY (edge (face ecpY))); Rewrite cface1 in Hfu0.
Apply/set0P=> [[||[||x]]] //; Try By Rewrite Sface.
By Move: (set0P Hbg x); Rewrite: -cface_icpY.
Qed.

Definition ecpH : pointed_map := (ecpN ecpY).

Lemma plain_ecpH : (plain ecpH).
Proof. Apply: plain_ecpN; Exact plain_ecpY. Qed.

Lemma cubic_ecpH : (quasicubic (rev (cpring ecpH))).
Proof. Apply: cubic_ecpN => //; Exact cubic_ecpY. Qed.

Lemma size_cpring_ecpH : (size (cpring ecpH)) = (size (cpring x0)).
Proof.
By Rewrite: /ecpH size_cpring_ecpN size_cpring_ecpY head_cpring.
Qed.

Lemma planar_ecpH : (planar ecpH).
Proof.
Apply: planar_ecpN => //.
 Exact planar_ecpY.
 Exact plain_ecpY.
 Exact cubic_ecpY.
 Exact connected_ecpY.
Qed.

Lemma connected_ecpH : (connected ecpH).
Proof. Apply: connected_ecpN; Exact connected_ecpY. Qed.

Definition icpH [x : g] : ecpH := (icpN ? (icpY x)).

Lemma icpH_inj : (injective icpH). Proof. By Move=> x y; Injection=> *. Qed.

Lemma icpH_edge : (x : g) (edge (icpH x)) = (icpH (edge x)). Proof. Done. Qed.

Lemma icpH_node : (x : g) (negb (seq3 (node x0) x0 (face (edge x0)) x)) ->
  (node (icpH x)) = (icpH (node x)).
Proof.
Move=> x; Rewrite: mem_seq3; Case/norP=> [HxnX]; Move/norP => [HxX HxfeX].
Rewrite: /= (eqd_sym x) (negbE HxnX) /=.
Do 2 Rewrite: (inj_eqd (Inode g)) (eqd_sym x)  (negbE HxX) /=.
By Rewrite: (inj_eqd (Inode g)) (monic2F_eqd (Enode g)) (eqd_sym x) (negbE HxfeX).
Qed.

Lemma cface_icpH : (x, y : g) (cface (icpH x) (icpH y)) = (cface x y).
Proof. By Move=> x y; Rewrite: /icpH /ecpH cface_icpN cface_icpY. Qed.

Lemma adj_icpH : (x, y : g) (adj (icpH x) (icpH y)) = (adj x y).
Proof.
Move=> *; Rewrite: /icpH /ecpH adj_icpN adj_icpY !cface_ecpY.
By Rewrite: andbC orbC {1 andb}lock andbC -lock.
Qed.

Lemma drop2_cpring_ecpH :
  (drop (2) (cpring ecpH)) = (maps icpH (drop (2) (cpring x0))).
Proof.
Rewrite: /ecpH cpring_ecpN size_long_cpring size_cpring_ecpY.
Rewrite: (drop_behead (3)) -f_iter -drop_behead drop2_cpring_ecpY.
By Case: (cpring x0) => [|y1[|y2[|y3 r]]] //=; Rewrite: -maps_comp.
Qed.

Lemma cpring_ecpH :
  (cpring ecpH)
     = (Adds (node ecpH) (Adds ecpH (maps icpH (drop (2) (cpring x0))))).
Proof.
Rewrite: -drop2_cpring_ecpH -head_proper_cpring //.
By Rewrite: size_proper_cpring size_cpring_ecpH -size_proper_cpring.
Qed.

Lemma cface_node_ecpH : (cface (node ecpH) (icpH (node x0))).
Proof.
Rewrite: cface1 /= /long_cpring /=; Do 2 Rewrite: Enode (negbE Hrg) /=.
Apply: connect0.
Qed.

Lemma cface_ecpH :
  (cface ecpH) =1 (seq3 ecpH (face ecpH) (face (face ecpH))).
Proof. By Apply: fconnect_cycle; Rewrite: //= /eqdf /= Enode (negbE Hrg). Qed.

Lemma adj_ecpH :
  (adj ecpH) =1 (fband (maps icpH (seq3 (node x0) x0 (face (edge x0))))).
Proof.
Move=>u; Rewrite: adjF1; Transitivity (adj (icpN ecpY ecpY) u); LeftDone.
Case: (fband_icpN u) => [v Huv]; Rewrite: (adjFr Huv) adj_icpN connect0 andbT.
Rewrite: Sface !cface_ecpY [q](closed_connect (fbandF q) Huv) ~{u Huv} adj_ecpY.
Step []: (icpY x0) = (face (edge ecpY)) By Rewrite: /= Enode (negbE Hrg).
Rewrite: /icpH /seq3 {1 4}/seq2 /seq1 /fband /has /maps !(cface_icpN ecpY) !orbF.
Rewrite: -(Sface ? v) icpY_edge; Case: (fband_icpY v) => [[x Hvx] | Hv].
 By Rewrite: !(same_cface Hvx) !cface_icpY -cface1r -orbA.
By Rewrite: -!(same_cface Hv) !cface_ecpY.
Qed.

Lemma fband_icpH : (u : ecpH) {x : g | (cface u (icpH x))} + {(cface ecpH u)}.
Proof.
Move=> u; Case: (fband_icpN u) => [v Huv].
Case: (fband_icpY v) => [[x Hvx] | Hv]; [Left; Exists x | Right].
  By Rewrite: (same_cface Huv) /icpH cface_icpN.
Rewrite: cface1 Sface (same_cface Huv) Sface.
By Rewrite: -(cface_icpN ecpY) in Hv.
Qed.

Lemma bridgeless_ecpH : (bridgeless ecpH).
Proof.
Def: Hu0 := (cface_ecpH (edge ecpH)).

Def: Hfu0 := (cface_ecpH (edge (face ecpH))); Rewrite cface1 in Hfu0.
Def: Hffu0 := (cface_ecpH (edge (face (face ecpH)))).
Rewrite: 2!cface1 in Hffu0.
Apply/set0P=> [[||[||[||x]]]] //; Try By Rewrite Sface.
By Move: (set0P Hbg x); Rewrite: -cface_icpH.
Qed.

End CompExtConfig.

Lemma cpmap0P : (monic3 negb negb id). Proof. By Case. Qed.

Fixpoint cpmap [cp : cprog] : pointed_map :=
  Cases cp of
    (Adds (CpR n) cp') => (ecpR n (cpmap cp'))
  | (Adds CpR' cp')    => (ecpR' (cpmap cp'))
  | (Adds CpY cp')     => (ecpY (cpmap cp'))
  | (Adds CpH cp')     => (ecpH (cpmap cp'))
  | (Adds CpU cp')     => (ecpU (cpmap cp'))
  | (Adds CpK cp')     => (ecpK (cpmap cp'))
  | (Adds CpA cp')     => (ecpA (cpmap cp'))
  | Seq0               => (PointedMap true :: (Hypermap cpmap0P))
  end.

Definition cfmap [cf : config] : pointed_map := (cpmap (cfprog cf)).
Definition cfring [cf : config] : (seq (cfmap cf)) := (rev (cpring (cfmap cf))).

Lemma cpmap_proper : (cp : cprog) (cubic_prog cp) ->
  (proper_cpring (cpmap cp)).
Proof.
Move=> cp; Rewrite: size_proper_cpring; Elim: cp => [|s cp Hrec] //=.
Case: s => // [n|||]; Move/Hrec=> Hrg.
  By Rewrite: size_cpring_ecpR.
  By Rewrite: size_cpring_ecpY ltnW.
  By Rewrite: size_cpring_ecpH. 
  By Rewrite: size_cpring_ecpU. 
Qed.

Lemma cfmap_long : (cp : cprog) (config_prog cp) ->
  (long_cpring (cpmap cp)).
Proof.
Move=> cp; Rewrite: size_long_cpring; Elim: cp => [|s cp Hrec] //=.
Case: s => // [n||]; Rewrite: ?size_cpring_ecpR ?size_cpring_ecpH //.
Case: cp Hrec => // [s cp] Hrec Hpc; Rewrite: size_cpring_ecpY ltnW ?ltnS; Auto.
Qed.

Lemma cpmap_plain : (cp : cprog) (cubic_prog cp) -> (plain (cpmap cp)).
Proof.
Elim=> [|s cp Hrec] //=; Case: s => // [||]; Move/Hrec=> HgE.
  By Apply: plain_ecpY.
  By Apply: plain_ecpH.
  By Apply: plain_ecpU.
Qed.

Lemma cpmap_cubic : (cp : cprog) (cubic_prog cp) -> 
  (quasicubic (rev (cpring (cpmap cp)))).
Proof.
Elim=> [|s cp Hrec] //=; Case: s => // [n|||]; Move/Hrec {Hrec}=> HgN.
  By Apply: cubic_ecpR.
  By Apply: cubic_ecpY.
  By Apply: cubic_ecpH.
  By Apply: cubic_ecpU.
Qed.

Lemma cpmap_connected : (cp : cprog) (cubic_prog cp) -> (connected (cpmap cp)).
Proof.
Elim=> [|s cp Hrec] //=; Case: s => // [||]; Move/Hrec {Hrec}=> Hcg.
  By Apply: connected_ecpY.
  By Apply: connected_ecpH.
  By Apply: connected_ecpU.
Qed.

Lemma cpmap_bridgeless : (cp : cprog) (cubic_prog cp) -> (bridgeless (cpmap cp)).
Proof.
Elim=> [|s cp Hrec] //=; Case: s => // [||]; Move=> Hcp.
  Apply: bridgeless_ecpY; Auto.
  Apply: bridgeless_ecpH; Auto; By Apply cpmap_proper.
  Apply: bridgeless_ecpU; Auto.
Qed.

Lemma cpmap_planar : (cp : cprog) (cubic_prog cp) -> (planar (cpmap cp)).
Proof.
Elim=> [|s cp Hrec] //=; Case: s => // [||]; Move=> Hcp;
  Move: (Hrec Hcp) (cpmap_plain Hcp) (cpmap_cubic Hcp) (cpmap_connected Hcp);
  Move=> Hpg HgE HgN Hcg.
  By Apply: planar_ecpY.
  By Apply: planar_ecpH.
  By Apply: planar_ecpU.
Qed.

Fixpoint cpker [cp : cprog] : (seq (cpmap cp)) :=
  <[cp'](seq (cpmap cp'))>Cases cp of
    (Adds (CpR _) cp') =>
      (cpker cp')
  | (Adds CpY cp') =>
      (maps (icpY (cpmap cp')) (cpker cp')) 
  | (Adds CpH cp') =>
     if (cpring (cpmap cp')) is (Adds _ (Adds x _)) then
       (maps (icpH (cpmap cp')) (Adds x (cpker cp')))
     else seq0
  | _ => seq0
  end.

Lemma cpmap_simple : (cp : cprog) (config_prog cp) ->
  (simple (cat (cpring (cpmap cp)) (cpker cp))).
Proof.
Elim=> [|s cp Hrec] //=; Case: s => // [n||].
    Move/Hrec=> Ucp; Rewrite: cpring_ecpR /rot -catA simple_catCA catA.
    By Rewrite cat_take_drop.
  Case Dcp: cp Hrec => // [s cp']; Case: {s cp'}Dcp => [] H; Move/H {H} => Hrec.
  Rewrite: cpring_ecpY cat_adds simple_adds; Pose g := (cpmap cp).
  Rewrite: [q](closed_connect (fbandF q) (cface_node_ecpY g)).
  Rewrite: -simple_adds -!cat1s -!catA simple_catCA !cat1s -cat_adds -maps_adds.
  Rewrite: -head_cpring -maps_cat simple_adds /fband.
  Rewrite: (eq_has (cface_ecpY 2!g)) (simple_maps (cface_icpY g)) has_maps Hrec.
  By Rewrite: /comp /= /setU1 /= has_set0.
Move=> Hcp; Move: {Hrec}(Hrec Hcp); Pose g := (cpmap cp).
Def: Hgp := (cpmap_proper (config_prog_cubic Hcp)).
Rewrite: (head_proper_cpring Hgp) (cpring_ecpH Hgp) -/g; Move=> Hrec.
Rewrite: cat_adds simple_adds [q](closed_connect (fbandF q) (cface_node_ecpH Hgp)).
Rewrite: -simple_adds -!cat1s -!catA simple_catCA !cat1s -!maps_adds -maps_cat.
Rewrite: -maps_adds simple_adds /fband (eq_has (cface_ecpH Hgp)) has_maps.
Rewrite: (simple_maps (cface_icpH g)) /comp /= /setU1 /= has_set0 /=.
By Rewrite: -!cat1s simple_catCA {1 cat}lock catA -lock simple_catCA.
Qed.

Lemma cpmap_cover : (cp : cprog) (config_prog cp) ->
  (fband (cat (cpring (cpmap cp)) (cpker cp))) =1 (cpmap cp).
Proof.
Elim=> [|s cp Hrec] //=; Case: s => // [n||].
    Move=> Hcp x; Apply: etrans (Hrec Hcp x).
    By Rewrite: cpring_ecpR !fband_cat fband_rot.
  Case Dcp: cp Hrec => [|s cp']; LeftBy Do 2 Clear; Do 3 Case=> //.
  Case: {s cp'}Dcp; Pose g := (cpmap cp); Move=> H; Move/H {H} => Hrec u.
  Rewrite: cpring_ecpY !cat_adds !fband_adds orbCA; Apply/orP.
  Case: (fband_icpY u) => [[x Hux] | Hu]; [Right | By Left; Rewrite Sface].
  Rewrite: Sface (same_cface (cface_node_ecpY g)) Sface -fband_adds -maps_cat.
  Rewrite: -maps_adds -cat_adds -head_cpring /fband (eq_has (same_cface Hux)).
  Rewrite: has_maps (eq_has 2!(comp (cface ?) ?) (cface_icpY g x)); Apply: Hrec.
Move=> Hcp; Move: {Hcp}(cpmap_proper (config_prog_cubic Hcp)) {Hrec}(Hrec Hcp).
Pose g := (cpmap cp); Move=> Hgp; Rewrite: (head_proper_cpring Hgp); Move=> Hrec u.
Rewrite: (cpring_ecpH Hgp) -/g -maps_adds !cat_adds.
Rewrite: !fband_adds Sface (same_cface (cface_node_ecpH Hgp)) Sface orbCA.
Rewrite: -maps_cat -fband_adds /setA -maps_adds; Apply/orP.
Case: (fband_icpH u) => [[x Hux] | Hu]; [Right | By Left; Rewrite Sface].
Rewrite: /fband (eq_has (same_cface Hux)).
Rewrite: has_maps (eq_has 2!(comp (cface ?) ?) (cface_icpH g x)) /= has_cat /=.
Rewrite: orbA orbCA -!orbA orbCA -has_cat; Exact (Hrec x).
Qed.

Fixpoint injcp [cp1 : cprog] :
   (cp2 : cprog) (cpmap cp2) -> (cpmap (catrev cp2 cp1)) :=
  [cp2; x]<[cp](cpmap (catrev cp2 cp))>Cases cp1 of
    Seq0 => x
  | (Adds s cp1') =>
      (injcp cp1' <[s'](cpmap (Adds s' cp2))> Cases s of
        CpY => (icpY (cpmap cp2) x)
      | CpH => (icpH (cpmap cp2) x)
      | CpU => (icpU (cpmap cp2) x)
      | CpK => (icpK (cpmap cp2) x)
      | _ => x
      end)
  end.

Lemma injcp_inj : (cp1, cp2 : cprog) (injective (injcp cp1 2!cp2)).
Proof.
Elim=>[|s cp1 Hrec] cp2 x y Exy //.
Case: s {Hrec Exy}(Hrec ? ? ? Exy) => //.
  Apply: (!icpY_inj).
  Apply: (!icpH_inj).
  Apply: (!icpU_inj).
  Apply: (!icpK_inj).
Qed.

Lemma sub_cface_injcp : (cp1, cp2 : cprog; x, y : (cpmap cp2))
  (cface x y) -> (cface (injcp cp1 x) (injcp cp1 y)).
Proof.
Elim=>[|s cp1 Hrec] cp2 x y Hxy //.
Case: s => /= *; Apply: Hrec => //. 
  By Apply: (etrans (cface_icpY ? ? ?) ?).
  By Apply: (etrans (cface_icpH ? ? ?) ?).
  By Apply: (etrans (cface_icpU ? ? ?) ?).
  By Apply: (etrans (cface_icpK ? ? ?) ?).
  By Apply: sub_cface_icpA.
Qed.

Lemma sub_adj_injcp : (cp1, cp2 : cprog; x, y : (cpmap cp2))
  (adj x y) -> (adj (injcp cp1 x) (injcp cp1 y)).
Proof.
Elim=>[|s cp1 Hrec] cp2 x y Hxy //.
Case: s => /= *; Apply: Hrec => //.
  By Apply: (etrans (adj_icpY ? ? ?) ?).
  By Apply: (etrans (adj_icpH ? ? ?) ?).
  By Apply: (etrans (adj_icpU ? ? ?) ?).
  By Apply: sub_adj_icpK.
  By Apply: sub_adj_icpA.
Qed.

Lemma cface_injcp : (cp1, cp2 : cprog; x, y : (cpmap cp2))
  (cubic_prog cp1) -> (cface (injcp cp1 x) (injcp cp1 y)) = (cface x y).
Proof.
Elim=>[|s cp1 Hrec] cp2 x y //=; Case: s => // [n|||] Hcp; Rewrite: Hrec //.
  By Apply: cface_icpY.
  By Apply: cface_icpH.
  By Apply: cface_icpU.
Qed.

Lemma edge_injcp : (cp1, cp2 : cprog; x : (cpmap cp2))
  (cubic_prog cp1) -> (edge (injcp cp1 x)) = (injcp cp1 (edge x)).
Proof. By Elim=>[|s cp1 Hrec] cp2 x //; Case: s => //= *; Rewrite: Hrec. Qed.

Lemma adj_injcp : (cp1, cp2 : cprog; x, y : (cpmap cp2))
  (cubic_prog cp1) -> (adj (injcp cp1 x) (injcp cp1 y)) = (adj x y).
Proof.
Elim=>[|s cp1 Hrec] cp2 x y //=; Case: s => // [n|||] Hcp; Rewrite: Hrec //.
  By Apply: adj_icpY.
  By Apply: adj_icpH.
  By Apply: adj_icpU.
Qed.

Lemma node_injcp : (cp1, cp2 : cprog; x : (cpmap cp2))
  (cubic_prog cp1) -> (negb (cpring (cpmap cp2) x)) ->
  (node (injcp cp1 x)) = (injcp cp1 (node x)).
Proof.
Elim=>[|[n||||||] cp1 Hrec] //= cp2 x Hcp1 Hx.
 By Rewrite: Hrec // /cpmap -/cpmap cpring_ecpR mem_rot.
 Rewrite: Hrec // -1?icpY_node //.
    Rewrite: mem_cpring in Hx.
    Rewrite: mem_seq2; Apply/orP; Case; Move/eqP=> Dx; Case/idP: Hx; Case Dx.
      Apply fconnect1.
    Apply connect0.
  Rewrite: /cpmap -/cpmap cpring_ecpY /= /setU1 /=.
  Rewrite: (mem_maps (icpY_inj 2!(cpmap cp2))).
  By Apply/idP=> [Hx']; Rewrite: (mem_behead Hx') in Hx.
 Rewrite: Hrec // -1?icpH_node //.
    Rewrite: mem_cpring in Hx.
    Rewrite: mem_seq3; Apply/or3P; Case; Move/eqP=> Dx; Case/idP: Hx; Case Dx.
        Apply fconnect1.
      Apply connect0.
    By Rewrite: cnode1r Eedge connect0.
  Rewrite: /cpmap -/cpmap /ecpH cpring_ecpN cpring_ecpY.
  Case Hgl: (long_cpring (ecpY (cpmap cp2))); RightDone.
  Rewrite: maps_drop !maps_adds -maps_comp.
  Rewrite: -{(comp (icpN (ecpY (cpmap cp2))) (icpY ?))}/(icpH (cpmap cp2)) /=.
  Rewrite: drop1 /setU1 /= behead_maps (mem_maps (icpH_inj 2!(cpmap cp2))).
  By Apply/idP => [Hx']; Case/idP: Hx; Do 2 Apply mem_behead.
Rewrite: Hrec // -1?icpU_node //.
  By Rewrite: head_cpring /= in Hx; Rewrite: mem_seq1; Case/norP: Hx.
Rewrite: /cpmap -/cpmap cpring_ecpU /= /setU1 /=.
By Rewrite: (mem_maps (icpU_inj 2!(cpmap cp2))).
Qed.
  
Lemma cnode_injcp : (cp1, cp2 : cprog; x, y : (cpmap cp2))
  (cubic_prog cp1) -> (negb (cpring (cpmap cp2) x)) ->
  (cnode (injcp cp1 x) (injcp cp1 y)) = (cnode x y).
Proof.
Move=> cp1 cp2 x y Hcp1 Hx; Apply/idP/idP; Move/iter_findex.
  Elim: {x}(findex node (injcp cp1 x) (injcp cp1 y)) {-2}x Hx => [|n Hrec] x Hx.
    Case/injcp_inj; Apply connect0.
  Rewrite: -iter_f node_injcp // cnode1; Apply: Hrec.
  By Rewrite: mem_cpring -cnode1r -mem_cpring.
Case; Elim: {x y}(findex node x y) {-3}x Hx => [|n Hrec] x Hx.
  Apply: connect0.
Rewrite: -iter_f cnode1 node_injcp //; Apply: Hrec.
By Rewrite: mem_cpring -cnode1r -mem_cpring.
Qed.

Fixpoint cprsize [cp : cprog] : nat :=
  Cases cp of
    Seq0 => (2)
  | (Adds CpY cp') => (S (cprsize cp'))
  | (Adds CpU cp') => (S (S (cprsize cp')))
  | (Adds CpK cp') => (S (pred (pred (cprsize cp'))))
  | (Adds CpA cp') => (sub2ifgt2 (cprsize cp'))
  | (Adds _ cp') => (cprsize cp')
  end.

Lemma size_ring_cpmap : (cp : cprog)
  (size (cpring (cpmap cp))) = (cprsize cp).
Proof.
Elim=>[|s cp1 Hrec] //; Case: s Hrec => [n||||||];
   Rewrite: /cprsize; Case; Rewrite: /cpmap -/cpmap.
  Apply: size_cpring_ecpR.
  Apply: size_cpring_ecpR.
  By Rewrite: /ecpY size_cpring_ecpN size_cpring_ecpU.
  Rewrite: /ecpH /ecpY !size_cpring_ecpN size_cpring_ecpU.
    By Rewrite head_cpring.
  Apply: size_cpring_ecpU.
  Apply: size_cpring_ecpK.
  Rewrite: cpring_ecpA size_long_cpring.
    By Case: (cpring (cpmap cp1)) => [|x [|y [|z p]]].
Qed.

Definition cpksize : cprog -> nat := (count [s]if s is CpH then true else false).

Lemma size_cpker : (cp : cprog) (config_prog cp) ->
  (size (cpker cp)) = (cpksize cp).
Proof.
Elim=> [|s cp Hrec] //=; Case: s => // [|].
  By Rewrite size_maps; Case: cp Hrec.
Move=> Hcp; Rewrite: (head_proper_cpring (cpmap_proper (config_prog_cubic Hcp))).
By Rewrite: /= size_maps Hrec.
Qed.

Inductive cpmask : Set := Cpmask : (mr, mk : bitseq) cpmask.

Definition proper_cpmask [cp : cprog; cm : cpmask] : bool :=
  let (mr, mk) = cm in (andb (size mr) =d (cprsize cp) (size mk) =d (cpksize cp)).

Definition cpsieve [cm : cpmask; cp : cprog] : (seq (cpmap cp)) :=
  let (mr, mk) = cm in (cat (sieve mr (cpring (cpmap cp))) (sieve mk (cpker cp))).

Definition cpmask1 [cp : cprog; i : nat] : cpmask :=
  (Cpmask (seqn (cprsize cp) false) (mkseq (set1 i) (cpksize cp))).

Lemma proper_cpmask1 : (cp : cprog; i : nat) (proper_cpmask cp (cpmask1 cp i)).
Proof. By Move=> *; Rewrite: /= size_seqn size_mkseq !set11. Qed.

Lemma cpsieve1 : (cp : cprog; i : nat) (ltn i (cpksize cp)) -> (config_prog cp) ->
  (cpsieve (cpmask1 cp i) cp) = (seq1 (sub (cpmap cp) (cpker cp) i)).
Proof.
Move=> cp i Hi Hcp /=; Def: x0 : (dart ?) := (cpmap cp); Move: Hi.
Rewrite: sieve_false cat0s -size_cpker ~{Hcp}// -{2 i}addn0 /mkseq.
Elim: (cpker cp) (0) i => // [x p Hrec] j [|i] /= Hi.
  Rewrite: add0n set11 -addn1; Congr Adds.
  Elim: p (0) {x Hrec Hi} => //= [x p Hrec] i.
  By Rewrite: addnS eqn_leq ltnNge leq_addr andbF -!addnS.
Rewrite: addSn eqn_leq ltnNge leq_addl /= -addnS; Auto.
Qed.

Fixpoint cpadj [cm : cpmask; cp : cprog] : cpmask :=
  Cases cp cm of
    (Adds (CpR n) cp') (Cpmask mr mk) =>
    let (mr', mk') = (cpadj (Cpmask (rotr n mr) mk) cp') in
    (Cpmask (rot n mr') mk')
  | (Adds CpY cp') (Cpmask (Adds b0 (Adds b1 (Adds b2 mr))) mk) =>
    if (cpadj (Cpmask (Adds b0 (Adds b2 mr)) mk) cp')
        is (Cpmask (Adds a0 (Adds a2 mr')) mk') then
      (Cpmask (Adds (orb a0 b1) (Adds (orb b0 b2) (Adds (orb a2 b1) mr'))) mk')
    else cm
  | (Adds CpH cp') (Cpmask (Adds b0 (Adds b1 mr)) (Adds b1' mk)) =>
    if (cpadj (Cpmask (Adds b0 (Adds b1' mr)) mk) cp')
       is (Cpmask (Adds a0 (Adds a1 mr')) mk') then
      (Cpmask
        (Adds (orb a0 b1)
          (Adds (or3b b0 b1' (head b0 mr))
            if mr' is (Adds a2 mr'') then (Adds (orb a2 b1) mr'') else mr'))
        (Adds (orb a1 b1) mk'))
    else cm
  | Seq0 (Cpmask (Adds b0 (Adds b1 Seq0)) Seq0) =>
    (Cpmask (seq2 b1 b0) seq0)
  | _ _ => cm (* can't happen *)
  end.

Lemma cpadj_proper : (cp : cprog; cm : cpmask)
  (proper_cpmask cp cm) -> (proper_cpmask cp (cpadj cm cp)).
Proof.
Elim=> [|s cp Hrec] [mr mk]; LeftBy Case: mr => [|b0 [|b1 [|b2 mr]]]; Case mk.
Case: s => //= [n||].
    Move=> Hcm0; Pose cm := (Cpmask (rotr n mr) mk).
    Step Hcm: (proper_cpmask cp cm) By Rewrite: /= size_rotr.
    By Case: (cpadj cm cp) (Hrec cm Hcm) => [mr' mk'] /=; Rewrite size_rot.
  Case: mr => [|b0 [|b1 [|b2 mr]]] //= Hcm.
  Pose cm := (Cpmask (Adds b0 (Adds b2 mr)) mk).
  By Case: (cpadj cm cp) (Hrec cm Hcm) => [[|a0 [|a2 mr']] mk'].
Case: mr mk => [|b0 [|b1 mr]] //= [|b1' mk] //= Hcm.
Pose cm := (Cpmask (Adds b0 (Adds b1' mr)) mk).
By Case: (cpadj cm cp) (Hrec cm Hcm) => [[|a0 [|a1 [|a2 mr']]] mk'].
Qed.

Lemma cpsieve_adj : (cp : cprog) (config_prog cp) ->
  (cm : cpmask) (proper_cpmask cp cm) ->
  (fband (cpsieve (cpadj cm cp) cp)) =1 [x](has (adj x) (cpsieve cm cp)).
Proof.
Elim=> // [s cp Hrec] Hcp [mr mk] /=; Case: s Hcp => // [n||] Hcp Hcm0.
    Pose cm := (Cpmask (rotr n mr) mk).
    Step Hcm: (proper_cpmask cp cm) By Rewrite: /= size_rotr.
    Move: (cpadj_proper Hcm) {Hrec}(Hrec Hcp cm Hcm).
    Case: (cpadj cm cp) => [mr' mk']; Move/andP=> [Ecm _] Hrec.
    Rewrite: /cpsieve /cpmap -/cpmap cpring_ecpR /cpker -/cpker.
    Move=> x; Rewrite: fband_cat has_cat /setU -(rot_rotr n mr).
    Move/andP: Hcm0=> [Ecm0 _]; Rewrite: -(size_rotr n) -size_ring_cpmap in Ecm0.
    Rewrite: (eq_has_r (mem_sieve_rot n (eqP Ecm0))) -has_cat -Hrec /= fband_cat.
    Congr orb; Apply: eq_has_r; Apply mem_sieve_rot.
    By Rewrite: size_ring_cpmap (eqP Ecm).
  Def: Urec := (cpmap_simple Hcp); Simpl in Hcp.
  Case Dcp: cp Hcp Hcm0 => [|s cp'].
    Case: mr mk => [|b0 [|b1 [|b2 [|b3 mr]]]] // [|a1 mk] // _ _.
    Case b0; Case b1; Case b2; Do 3 Case => //.
  Case: {s cp'}Dcp => [] Hcp; Def: Hcpq := (config_prog_cubic Hcp).
  Move: (cpmap_proper Hcpq) (cpmap_plain Hcpq) Urec {Hrec}(Hrec Hcp).  
  Pose g := (cpmap cp); Move=> Hgp HgE Urec Hrec Hcm0.
  Case: (andP Hcm0) => [Emr0 _]; Step Hmr0: (ltn (2) (size mr)).
    By Rewrite: (eqP Emr0) -size_ring_cpmap ltnS -size_proper_cpring.
  Case: mr Hmr0 Emr0 Hcm0 => [|b0 [|b1 [|b2 mr]]] // _ Emr0 Hcm0.
  Pose cm := (Cpmask (Adds b0 (Adds b2 mr)) mk).
  Def: Hcm := Hcm0; Rewrite: /= eqdSS add0n in Hcm.
  Move: (cpadj_proper 2!cm Hcm) {Hrec}(Hrec cm Hcm).
  Case: (cpadj cm cp) => [mr' mk']; Move/andP=> [Emr' _] Hrec.
  Step Hmr': (ltn (1) (size mr')).
    By Rewrite: (eqP Emr') -size_ring_cpmap -size_proper_cpring.
  Case: mr' Hmr' Emr' Hrec Urec => [|a0 [|a2 mr']] // _ Emr'.
  Rewrite: /cpsieve /cpmap -/cpmap /cpker -/cpker cpring_ecpY /cm -/g.
  Rewrite: (head_proper_cpring Hgp) /behead maps_adds.
  Move=> Hrec Urec u; Def: HnYF := (cface_node_ecpY g).
  Rewrite: cat_adds simple_adds [q](closed_connect (fbandF q) HnYF) in Urec.
  Rewrite: /fband !has_cat !has_sieve_adds (adjFr HnYF) Sface (same_cface HnYF).
  Rewrite: Sface.
  Case Hu: (cface u (ecpY (cpmap cp))).
    Rewrite: !(adjF Hu) !(adj_ecpY Hgp).
    Rewrite: !(eq_has (adjF Hu)) !(eq_has (adj_ecpY Hgp)) andbT.
    Case b0; LeftBy Rewrite: !orTb orbT {1}/seq2 maps_adds fband_adds connect0.
    Rewrite: andFb !orFb; Case b2.
      By Rewrite: orbT !orTb {2}/seq2 /seq1 !maps_adds !fband_adds connect0 !orbT.
    Rewrite: andFb !orFb -!has_sieve_adds -!has_cat (eq_has (same_cface Hu)).
    Apply/hasP/hasP=> [[v Hv Huv]]; ElimType False.
      Rewrite: -!maps_adds -!maps_sieve -maps_cat in Hv.
      By Case/mapsP: Hv Huv => [y _ []]; Rewrite: cface_ecpY.
    Move: Urec; Rewrite: -(fband_rot (1)) -(simple_rot (1)) -simple_adds.
    Rewrite: cat_adds rot1_adds -add_last_adds -!cat1s cat1s -catA -!cat_adds.
    Rewrite: seq2I -cats1 -catA cats1 -rot1_adds simple_cat has_rot.
    Case/and3P; Clear; Case/hasP; Exists v; RightDone.
    Rewrite: -cat_adds !mem_cat /setU in Hv *; Apply/orP.
    Case/orP: Hv; Move/mem_sieve; Auto.
  Case: (fband_icpY u) => [[x Hux] | Hu']; RightBy Rewrite: Sface Hu in Hu'.
  Rewrite: andbF orFb !(same_cface Hux) !(adjF Hux) !cface_icpY !adj_icpY.
  Rewrite: (Sadj (plain_ecpY g HgE)) (adj_ecpY Hgp).
  Rewrite: /seq2 /seq1 {3}/maps /fband {3}/has !cface_icpY orbF.
  Rewrite: -!maps_sieve !has_find !size_maps !find_maps -!has_find.
  Step Efu: (comp (cface u) (icpY ?)) =1 (cface x).
    By Move=> y; Rewrite: /comp (same_cface Hux) cface_icpY.
  Step Eau: (comp (adj u) (icpY ?)) =1 (adj x).
    By Move=> y; Rewrite: /comp (adjF Hux) adj_icpY.
  Rewrite: !~{Efu}(eq_has Efu) !~{Eau}(eq_has Eau).
  Move: {u Hu Hux Urec Hrec}(Hrec x).
  Rewrite: /fband !has_cat !has_sieve_adds.
  Case b1; RightBy Rewrite: !orbF.
  Case Hx0: (cface x (node (cpmap cp))); LeftBy Rewrite: /= !orbT.
  Case Hx2: (cface x (cpmap cp)); LeftBy Rewrite: /= !orbT.
  By Rewrite: !andbF.
Case: (andP Hcm0) (cpmap_simple Hcp) => [Emr Emk]; Simpl in Hcp.
Def: Hcpq := (config_prog_cubic Hcp).
Move: (cpmap_plain Hcpq) (cpmap_proper Hcpq) (cfmap_long Hcp).
Rewrite: /cpmap -/cpmap; Pose g := (cpmap cp); Move=> HgE Hgp Hgl.
Def: Hg0E := (plain_ecpH g HgE).
Step Hmr: (ltn (2) (size mr)).
  By Rewrite: (eqP Emr) -size_ring_cpmap -size_long_cpring.
Case: mr Hmr Emr Hcm0 => [|b0 [|b1 [|b2 mr]]] // _ Emr.
Case: mk Emk => [|b1' mk] // _ Hcm; Rewrite: /= add1n eqdSS in Hcm.
Pose cm := (Cpmask (Adds b0 (Adds b1' (Adds b2 mr))) mk).
Case/andP: Hcm (cpadj_proper 2!cm Hcm) {Hrec}(Hrec Hcp cm Hcm) => [Ecp _].
Case: (cpadj cm cp) => [mr' mk']; Move/andP=> [Emr' _]; Rewrite: ~/cm.
Rewrite: -(eqP Ecp) in Emr'; Case: mr' Emr' => [|a0 [|a1 [|a2 mr']]] // _.
Rewrite: /cpsieve /cpmap -/cpmap /cpker -/cpker cpring_ecpH // drop_behead.
Rewrite: (head_long_cpring Hgl) /iter /head /behead !maps_adds.
Move=> Hrec Urec u; Def: HnHF := (cface_node_ecpH Hgp).
Rewrite: !cat_adds simple_adds [q](closed_connect (fbandF q) HnHF) in Urec.
Rewrite: /fband !has_cat !has_sieve_adds (adjFr HnHF) Sface (same_cface HnHF).
Rewrite Sface.
Case Hu: (cface u (ecpH g)).
  Rewrite: !(adjF Hu) !(adj_ecpH Hgp).
  Rewrite: !(eq_has (adjF Hu)) !(eq_has (adj_ecpH Hgp)).
  Case b0; LeftBy Rewrite: !orbT orTb {1}/seq3 maps_adds fband_adds connect0.
  Rewrite: andFb !orFb; Case b2.
    Rewrite: !orbT orTb {2}/seq3 /seq2 /seq1 !maps_adds !fband_adds connect0.
    By Rewrite: !orbT.
  Rewrite: andFb !orFb; Case b1'.
    By Rewrite: !orbT orTb {3}/seq3 /seq2 !maps_adds !fband_adds connect0 !orbT.
  Rewrite: andFb !orFb -!has_sieve_adds -!has_cat (eq_has (same_cface Hu)).
  Apply/hasP/hasP=> [[v Hv Huv]]; ElimType False.
    Rewrite: -!maps_adds -!maps_sieve -maps_cat in Hv.
    By Case/mapsP: Hv Huv => [x _ []]; Rewrite: cface_ecpH.
  Step Urec':
       (simple (cat (maps (icpH g) (seq3 (node g) g (face (edge g))))
               (cat (Adds (ecpH g) (maps (icpH g) (drop (3) (cpring g))))
                    (maps (icpH g) (cpker cp))))).
    Apply: etrans Urec; Rewrite: -simple_adds; Apply simple_perm.
      Move=> w; Apply: eq_has_r {w} => [w].
      By Rewrite: /= /setU1 !mem_cat /setU /= /setU1; Repeat BoolCongr.
    By Rewrite: /= !size_cat /= !size_maps addnS.
  Rewrite: /cpker -/cpker simple_cat in Urec'; Case/and3P: Urec' {Urec}; Clear.
  Case/hasP; Exists v; RightDone.
  Rewrite: !mem_cat /setU in Hv *; Apply/orP.
  Case/orP: Hv; Move/mem_sieve; Auto.
Case: (fband_icpH u) => [[x Hux] | Hu']; RightBy Rewrite: Sface Hu in Hu'.
Rewrite: andbF orFb !(same_cface Hux) !(adjF Hux) !cface_icpH !adj_icpH.
Rewrite: (Sadj Hg0E) (adj_ecpH Hgp) /seq3 /seq2 /seq1 !maps_adds !fband_adds.
Rewrite: !cface_icpH {3}/maps /fband {3}/has !orbF.
Rewrite: -!maps_sieve !has_find !size_maps !find_maps -!has_find.
Step Efu: (comp (cface u) (icpH ?)) =1 (cface x).
  By Move=> y; Rewrite: /comp (same_cface Hux) cface_icpH.
Step Eau: (comp (adj u) (icpH ?)) =1 (adj x).
  By Move=> y; Rewrite: /comp (adjF Hux) adj_icpH.
Rewrite: !~{Efu}(eq_has Efu) !~{Eau}(eq_has Eau).
Move: {u Hu Hux Urec Hrec}(Hrec x).
Rewrite: /fband !has_cat !has_sieve_adds.
Case b1.
  Case Hx0: (cface x (node g)); LeftBy Rewrite: /= !orbT.
  Case Hx1': (cface x g); LeftBy Rewrite: /= !orbT.
  Case Hx2: (cface x (face (edge g))); LeftBy Rewrite: /= !orbT.
  By Rewrite: !andbF /=; Move=> H; Rewrite: ~H -!orbA; Repeat BoolCongr.
Rewrite: /= !orbF -!orbA -!(orbCA (andb a1 (cface x g))).
By Rewrite: -!(orbCA (andb b1' (adj x g))).
Qed.

Unset Implicit Arguments.
