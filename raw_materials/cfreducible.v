(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require tacticext.
Require boolprop.
Require funs.
Require dataset.
Require natprop.
Require seq.
Require paths.
Require finset.
Require connect.
Require hypermap.
Require geometry.
Require color.
Require chromogram.
Require coloring.
Require kempe.
Require cfmap.
Require cfcolor.
Require cfcontract.
Require ctree.
Require kempetree.

Set Implicit Arguments.

(* We only use C-reductibility; the source data has been completed *)
(* with an arbitrary contraction. *)

Section CfReducible.

Variable cf : config.

Definition check_reducible : bool :=
  if (contract_ctree cf) is (Some cct) then
    (ctree_disjoint (kempe_tree (cfprog cf)) cct)
  else false.

Definition cfreducible : Prop := (c_reducible (cfring cf) (cfcontract cf)).

Lemma check_reducible_valid : check_reducible -> cfreducible.
Proof.
Rewrite: /check_reducible /cfreducible; Move: (contract_ctreeP cf).
Move: (cfcontract cf) (contract_ctree cf) => cc.
Case=> // [cct] [Hcc Hkcc] Hkg; Split; LeftDone.
Move=> et Het; Case: Het (ctree_mem_disjoint Hkg (Hkcc ? Het)) => [k _ Det].
Step Eet: (size (behead et)) = (pred (cprsize (cfprog cf))).
  Rewrite: size_behead Det size_trace size_maps.
  By Rewrite: /cfring rev_rev -size_ring_cpmap.
Move/(kempe_treeP Eet) {Eet Hkg Hkcc}; Rewrite: -/(cfmap cf).
Step []: (rot (1) et) = (ctrace (behead et)).
  Step Het: (sumt et) = Color0 By Rewrite Det; Apply: sumt_trace.
  Case Det': et (introT eqP Het) => [|e et'] /=.
    Move: (congr size Det'); Rewrite: Det size_trace size_maps /cfring rev_rev.
    By Rewrite: head_cpring.
  By Rewrite: -eq_addc0 rot1_adds /ctrace; Case/eqcP.
Move{k Det}=> Het P HP HPet; Pose P' := [et'](P (rotr (1) et')).
Step HP': (kempe_closed P').
  Move=> et' HP'et'; Case: (HP ? HP'et') => [HPet'h [w Het'w HwPet']].
  Split; LeftBy Move=> h; Rewrite: /P' /permt -maps_rotr; Apply: HPet'h.
  Exists (gram_rot w); LeftBy Rewrite: -(rot_rotr (1) et') match_gram_rot.
  Move=> et''; Rewrite: -{1 et''}(rot_rotr (1) et'') match_gram_rot; Apply: HwPet'.
Rewrite: -(rotr_rot (1) et) in HPet.
Case: {et Het HP' HPet}(Het ? HP' HPet) => [et [k Hk Det] HP'et].
Exists (rotr (1) et); RightDone; Exists k; LeftDone.
By Rewrite: /cfring rev_rev Det maps_rot trace_rot rotr_rot.
Qed.

End CfReducible.

(* This predicate hides the (expensive) reducibility evaluation. *)

Definition cf000 : config := (Config 0 0 H).

Definition reducible_in_range [j1, j2 : nat; cfs : configseq] : Prop :=
  (i : nat) (leq j1 i) -> (ltn i j2) -> (cfreducible (sub cf000 cfs i)).

Lemma check_reducible_in_range : (j1, j2 : nat; cfs : (seq configData))
  (Hcfs : (i : nat) let n = (minus j2 j1) in
          (leq n i) \/ (check_reducible (sub cf000 (take n (drop j1 cfs)) i)))
  (reducible_in_range j1 j2 cfs).
Proof.
Move=> j1 j2 cfs Hcfs i Hij1 Hij2; Pose n := (subn j2 j1); Pose i' := (subn i j1).
Step Hj12 : (leq j1 j2) By Apply ltnW; Apply: leq_trans Hij2.
Step Hi'n : (ltn i' n) By Rewrite: /i' -(leq_subS Hij1) leq_sub_add /n leq_add_sub.
Case: {Hcfs}(Hcfs i'); Rewrite: subnI -/n; LeftBy Rewrite: leqNgt Hi'n.
Rewrite: sub_take // sub_drop /i' leq_add_sub //.
By Apply: (!check_reducible_valid).
Qed.

Tactic Definition CheckReducible :=
  Apply check_reducible_in_range; Simpl;
  Repeat (Case; [Right; By Compute | Try By Left]).

Lemma cat_reducible_range : (j1, j2 : nat; cfs : (seq configData))
  (reducible_in_range j1 j2 cfs) ->
  (j3 : nat) (reducible_in_range j2 j3 cfs) ->
  (reducible_in_range j1 j3 cfs).
Proof. Move=> j1 j2 cfs Hj12 j3 Hj23 i Hij1 Hij3; Case (ltnP i j2); Auto. Qed.

Grammar tactic simple_tactic : tactic :=
  catred_tac ["CatReducible" catred_body($tac)] -> [$tac]
with catred_body : tactic :=
  catred_body_cat [constr:constr0($hyp) catred_body($tac)] ->
  [Apply (cat_reducible_range $hyp); $tac]
| catred_body_exact [constr:constr0($hyp)] ->
  [Exact $hyp].

Unset Implicit Arguments.

