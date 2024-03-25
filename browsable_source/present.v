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
Require coloring.
Require birkhoff.
Require embed.
Require quiz.
Require quiztree.
Require part.
Require redpart.
Require znat.
Require discharge.
Require hubcap.
Require cfmap.
Require cfcontract.
Require cfreducible.
Require configurations.

Set Implicit Arguments.

(* We bring together almost all the elements of graph theory that have been     *)
(* developped so far, to build up the shell that will run all the canned        *)
(* unavoidability proof scripts.                                                *)

(* Presentations are implemented directly as Coq scripts. This file contains    *)
(* the lemmas and special tactics that allow to handle concisely the four       *)
(* types of steps (split, symmetry, reducibility and hubcap), as well as the    *)
(* general setup for a particular hub size (such as generating the quiz tree    *)
(* and the discharge rules).                                                    *)

(* We need to provide additional staging for the quiz fork computation: Coq's   *)
(* reduction algorithm goes berserk when the full config list appears as an     *)
(* explicit parameter of a dependent predicate (!).                             *)

Definition reducibility : Prop :=
  (reducible_in_range (0) (size the_configs) the_configs).

(* Resources: configuration matching and rule forks.                            *)

Inductive the_quiz_tree_value : quiz_tree -> Prop :=
  TheQuizTreeValue : (the_quiz_tree_value (cfquiz_tree the_configs)).

Record the_quiz_tree_only : Set := TheQuizTree {
  the_quiz_tree_only_tree :> quiz_tree;
  the_quiz_tree_only_value : (the_quiz_tree_value the_quiz_tree_only_tree)
}.

(* The actual quiz tree is computed near the end of this file, because undo     *)
(* slows down considerably with such a large term in the context.               *)

Definition valid_hub [g : hypermap; x : g] : Prop :=
  (and (minimal_counter_example g) (posz (dscore x))).

Definition excluded_arity [n : nat] : Prop :=
  (g : hypermap; x : g) (valid_hub x) -> (n =d (arity x)) = false.

Definition successful [p : part] : Prop :=
  (g : hypermap; x : g) (valid_hub x) -> (negb (exact_fitp x p)).

Definition forced_part [p0, p : part] : Prop :=
  (g : hypermap; x : g) (valid_hub x) -> (exact_fitp x p0) -> (exact_fitp x p).

Definition succeeds_in [p0, p : part] : Prop :=
  (forced_part p0 p) -> (successful p).

(* Presentation. *)
Lemma exclude_arity : (n : nat)
  (succeeds_in (pcons_ n) (pcons_ n)) -> (excluded_arity n).
Proof.
Move=> n Hp0 g x Hx; Move: {}Hx => [Hg _]; Apply/eqP=> [Hxn].
By Case/idPn: (exact_fitp_pcons_ Hg x); Rewrite: -~Hxn; Apply: Hp0 => //; Move.
Qed.

Section Succeed.

(* Tactic parameters come first. *)

(* Parameters for Pcase and Similar. *)
Variables i : subpart_loc; j, k : nat; mir, lo : bool.

(* Parameter for Reducible & Hubcap. *)
Variable qt : the_quiz_tree_only.

(* Parameters for Hubcap. *)
Variables rf : (n : nat)(drule_fork n); hc : hubcap.

(* Implicit parameter and explicit assumption for Similar. *)
Variable ps : part.
Hypothesis Hps : (successful ps).

(* Implicit goal parameters. *)
Variables p0, p : part.

(* Pcase Ln_m: i[j] <= k. or Pcase Ln_m: i[j] > k. *)
Lemma succeed_by_split :
  let pl = (split_part i j k lo p) in
  let pr = (split_part i j k (negb lo) p) in
  let p0l = if (good_split i j k p0) then (split_part i j k lo p0) else pl in
  (good_split i j k p) ->
  (succeeds_in p0l pl) ->
  ((successful p0l) -> (succeeds_in p0 pr)) ->
  (succeeds_in p0 p).
Proof.
Move=> pl pr p0l Hpijk Hp0lpl Hp0pr Hp0p.
Step Hpl: (successful pl).
  Apply Hp0lpl; Rewrite: /p0l /pl; Case Hp0s: (good_split i j k p0) => [] g x //.
  Move=> Hx; Move: {}Hx => [Hg _]; Rewrite: !(fitp_split Hg) //.
  By Case/andP=> *; Apply/andP; Auto.
Step Hpr: (successful pr).
  Apply: Hp0pr; Rewrite: /pr ?size_split_part //;
   Move=> g x Hx; Move: Hx {Hpl}(Hpl ? ? Hx) {Hp0p}(Hp0p ? ? Hx) => [Hg _].
    Rewrite: /p0l; Case Hp0s: (good_split i j k p0) => //.
    Rewrite: /pl !(fitp_split Hg) //.
    By Move=> H Hp0p; Apply/andP=> [[Hkx Hxp0]]; Case/andP: H; Auto.
  Rewrite: /pl !(fitp_split Hg) // -(addTb lo) -addbA.
  By Move=> H Hp0p Hp0x; Rewrite: (Hp0p Hp0x) !andbT in H *.
Move=> g x Hx; Move: Hx (Hpl ? ? Hx) (Hpr ? ? Hx) => [Hg _].
Rewrite: /pl /pr !(fitp_split Hg) // -(addTb lo) -addbA.
By Move=> H H'; Apply/idP=> [Hxp]; Case/idP: H'; Rewrite: Hxp !andbT in H *.
Qed.

(* Similar to Ln_m[j]. or Similar to *Ln_m[j]. *)
Lemma succeed_by_similarity :
  let p1 = if mir then (mirror_part p) else p in let p2 = (rot_part j p1) in
   (size_part ps) = (size_part p2) /\ (cmp_part p2 ps) = Psubset ->
  (succeeds_in p0 p). 
Proof.
Move=> p1 p2 [Eps2 Hps2] H {H} g x Hx; Apply/idP=> [Hxp].
Pose g' := if mir then (mirror g) else g.
Step [x1 Hx1 Hxp1]: (EX x1 : g' | (valid_hub x1) & (exact_fitp x1 p1)).
  Move: {}Hx => [Hg Hxs].
  Rewrite: /g' /p1; Case mir; [Exists x | By Exists x].
    Split; LeftBy Apply minimal_counter_example_mirror.
    By Rewrite: (dscore_mirror Hg).
  By Rewrite: -(fitp_mirror Hg) mirror_mirror_part //.
Step [x2 Hx2 Hxp2]: (EX x2 : g' | (valid_hub x2) & (exact_fitp x2 p2)).
  Case: (ltnP (size_part p1) j) => [Hj].
    Exists x1; LeftDone; Move: Hxp1; Rewrite: /p2 /exact_fitp size_rot_part.
    Apply: etrans; Congr andb; Rewrite: -{2 p1}(cat_take_drop_part j) /rot_part.
    Move: (ltnW Hj); Rewrite: -eqn_sub0 -size_drop_part !fitp_cat andbC.
    By Case (drop_part j p1).
  Case: Hx1 => [Hg' Hx1]; Exists (iter j face x1); RightBy Rewrite: /p2 -fitp_rot.
  By Split; Auto; Rewrite: -(dscore_cface 2!x1) // fconnect_iter.
Case/andP: Hxp2 => [Ep2 Hxp2]; Case/idP: (Hps Hx2); Rewrite: /exact_fitp.
By Rewrite: Eps2 Ep2 (fitp_cmp Hxp2 ps) Hps2.
Qed.

(* Implicit assumption for Reducible and Similar. *)
Hypothesis Hred : reducibility.

Lemma no_fit_the_redpart : (g : hypermap) (minimal_counter_example g) ->
  (x : g; p' : part) (redpart qt p') -> (negb (exact_fitp x p')).
Proof.
Move=> g Hg x p' Hp'; Apply: (no_fit_redpart Hg) p' Hp' x  => [x].
Case: {}qt => [qt' Dqt'] /=; Case: {qt'}Dqt'.
Move: {}Hred; Rewrite: /reducibility; Move Dcfs: {}the_configs => cfs Hcfs.
Apply/idP; Case/(qzt_fit_cfquiz Hg 4!?) => [cf Hcf [qz Hgqz [Hgc [u Hu]]]].
Cut (g' : hypermap) (minimal_counter_example g') -> ~(EX y : g' | (fitqz y qz)).
  By Move=> H; Case: Hgqz; Apply: H {H}; Try Apply minimal_counter_example_mirror.
Move{g Hg x Hgqz}=> gm Hgm [x Hxqz].
Step Hcc: (cfreducible cf).
  Move: (Hred (leq0n (index cf cfs))); Rewrite: Dcfs index_mem sub_index; Auto.
Case (not_embed_reducible Hgm Hgc (quiz_preembedding Hgm Hgc Hu Hxqz) Hcc).
Qed.

(* Reducible. *)
Lemma succeed_by_reducibility : (redpart qt p) -> (succeeds_in p0 p).
Proof. By Move=> Hp H {H} g x [Hg Hxn]; Apply: no_fit_the_redpart. Qed.

(* Hubcap T[j1,j1'] <= b1 & ... *)
Lemma succeed_by_hubcap :
  let n = (size_part p) in
  (andb (hubcap_cover n hc) (hubcap_fit (redpart qt) (rf n) p hc)) ->
  (succeeds_in p0 p).
Proof.
Move=> n Hhc H {H} g x [Hg Hx].
By Apply: (hubcap_fit_bound Hg (no_fit_the_redpart Hg)) Hhc.
Qed.

End Succeed.

Implicits succeed_by_split [5 6 7 11 12].
Implicits succeed_by_similarity [3 5 6 9 10].
Implicits succeed_by_reducibility [2 3 7 8].
Implicits succeed_by_hubcap [4 5 9 10].

(* Actual resources.                         *)

Definition the_quiz_tree : the_quiz_tree_only :=
  Eval Compute in (TheQuizTree TheQuizTreeValue).

Definition the_drule_fork_template : (n : nat) (drule_fork n).
Do 12 (Case; LeftBy Apply: (DruleFork (DruleForkValues ?))).
Move=> n; Abstract Apply: (DruleFork (DruleForkValues ?)).
Defined.

Definition the_drule_fork : (n : nat) (drule_fork n) :=
  Eval Compute in the_drule_fork_template.

(* Tactic extensions for the presentations. *)

Tactic Definition Reducible :=
  Apply (succeed_by_reducibility the_quiz_tree); [Assumption | By Compute].

Tactic Definition Presentation := Apply exclude_arity; Simpl.

Grammar tactic simple_tactic : tactic :=
  hubcap_tactic
    ["Hubcap" constr:hubcap($h)] ->
  [Apply (succeed_by_hubcap the_quiz_tree the_drule_fork $h);
    [Assumption | By Compute]]
| similar_tactic
    ["Similar" "to" mirroring($m) identarg($id) "[" nat:number($n) "]" ] ->
  [Apply (succeed_by_similarity $n $m $id); Compute; Do 2 Split]
| pcase_tactic
    ["Pcase" pcase_move($movet) ":" constr:subpart_loc($i) "[" nat:number($j1) "]"
        pcase_comp($lo) nat:number($k) ]->
  let (APPLIST $_ $j) = [$j1] in
  [Apply (succeed_by_split $i $j $k $lo); [Split | Simpl | $movet]]
with mirroring : constr :=
  some_mirror_tac [ "*" ] -> [true]
| simple_sym_part [  ] -> [false]
with pcase_move : tactic :=
  some_pcase_move [ identarg($id) ] -> [Move=> /= $id]
| pcase_move_clear [ ] -> [Move=> _ /=]
with pcase_comp : constr :=
  pcase_le ["<="] -> [true]
| pcase_gt [">"] -> [false].

Syntax constr level 10:
  pp_successful [(successful $qa $p)] ->
  ["successful " $qa " " <<(Pretty part $p)>>:L]
| pp_succeeds_in [(succeeds_in $qa $p0 $p)] ->
  [[<v 1> "succeeds_in " $qa [1 0]
     <<(Pretty part $p0)>>:L  [1 0]
     <<(Pretty part $p)>>:L]].

Unset Implicit Arguments.
