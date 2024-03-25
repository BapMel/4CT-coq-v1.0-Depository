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
Require coloring.
Require quiz.
Require cfmap.
Require cfquiz.

Set Implicit Arguments.

(* Compile a sequencs of (reducible) configurations into a set of quizzes,  *)
(* and store them in a tree structure according to the arities of the three *)
(* center regions. Rotations and reflections are also stored, so that the   *)
(* reducibility search can do a single lookup per triangle in the searched  *)
(* part (see file redpart.v).                                               *)
(* The middle nodes of the tree have four branches, for each of the arities *)
(* 5, 6, 7 and 8; the top node also has four branches, but with a different *)
(* interpretation: the first is a subtree for arities less than 9, and the  *)
(* other three for arities 9, 10, and 11 (we don't need to store those      *)
(* lower in the tree, since only the most central region of our             *)
(* configurations can have more than 8 sides). Also, since such a large     *)
(* region can only match the hub, we don't store the rotations of its quiz. *)
(*   The quiz fork and trees are traversed in the inner loop of the         *)
(* unavoidability computation, so, like parts, their representation has     *)
(* been compressed, with the quiz triples integrated in the list structure, *)
(* and the tree structure feeding directly in the list structure.           *)

Inductive quiz_tree : Set :=
  QztNil : quiz_tree
| QztLeaf : (q1, q2, q3 : question) quiz_tree -> quiz_tree
| QztNode : (t5, t6, t7, t8 : quiz_tree) quiz_tree
| QztHubNode : (t58, t9, t10, t11 : quiz_tree) quiz_tree.

Syntax constr level 10 :
  pp_qzt_top_node [(Pretty $_ (QztNode $t5 $t6 $t7 $t8))] ->
  ["Qtree [" [<hv 0> (PPQZT <<(QztNode $t5 $t6 $t7 $t8)>>) "]" ]]
| pp_qzt_top_hub_node [(Pretty $_ (QztHubNode $t58 $t9 $t10 $t11))] ->
  ["Qtree [" [<hv 0> (PPQZT <<(QztHubNode $t58 $t9 $t10 $t11)>>) "]" ]]
| pp_qzt_top_leaf [(Pretty $_ (QztLeaf $q1 $q2 $q3 $t))] -> 
  ["Qleaf [" [<hv 0> (PPQZT <<(QztLeaf $q1 $q2 $q3 $t)>> 0 0 0) "]"]]
| pp_qzt_default [<<(PPQZT $qt ($LIST $qa))>>] ->
  [(SubQuizTree ($LIST $qa)) <<(Pretty quiz_tree $qt)>>]
| pp_qzt_node [<<(PPQZT <<(QztNode $t5 $t6 $t7 $t8)>> ($LIST $qa))>>] ->
  ["5:[" [<hv 0> (PPQZT $t5 5 ($LIST $qa))] "]" [1 0] 
   "6:[" [<hv 0> (PPQZT $t6 6 ($LIST $qa))] "]" [1 0] 
   "7:[" [<hv 0> (PPQZT $t7 7 ($LIST $qa))] "]" [1 0] 
   "8:[" [<hv 0> (PPQZT $t8 8 ($LIST $qa))] "]"]
| pp_qzt_hub_node [<<(PPQZT <<(QztHubNode $t58 $t9 $t10 $t11)>>)>>] ->
  [ (PPQZT $t58) [1 0] 
   "9:[" [<hv 0> (PPQZT $t9 9)] "]" [1 0] 
   "10:[" [<hv 0> (PPQZT $t10 10)] "]" [1 0] 
   "11:[" [<hv 0> (PPQZT $t11 11)] "]"]
| pp_qzt_leaf_fill [<<(PPQZT <<(QztLeaf $q1 $q2 $q3 $t)>> ($LIST $qa))>>] ->
  [(PPQZT <<(QztLeaf $q1 $q2 $q3 $t)>> ($LIST $qa) 0 0 0)]
| pp_qzt_leaf
    [<<(PPQZT <<(QztLeaf $q1 $q2 $q3 $t)>> $qa3 $qa2 $qa1 ($LIST $_))>>] -> 
  [ [<hv 1> " {" $qa1 (PPQZTQ $q1) [1 0]
            "& " $qa2 (PPQZTQ $q2) [1 0]
            "& " $qa3 (PPQZTQ $q3) "}"]
    [1 0] (PPQZT $t $qa3 $qa2 $qa1)]
| pp_qzt_nil [<<(PPQZT <<QztNil>> ($LIST $_))>>] ->
  [ ]
| pp_qzt_question [<<(PPQZTQ $q)>>] ->
  ["-R->" <<(Pretty question $q)>>]
| pp_qzt_question0 [<<(PPQZTQ <<Qask0>>)>>] ->
  [ ].

(* Not-nil test.                                                            *)

Definition qzt_proper [qt' : quiz_tree] : bool :=
  if qt' is QztNil then false else true.

(* Update/store operations.                                                 *)

Fixpoint qzt_put1 [qa : qarity; qr : quiz_tree -> quiz_tree; t : quiz_tree]
                    : quiz_tree :=
  Cases t qa of
    (QztNode t5 t6 t7 t8) Qa5 => (QztNode (qr t5) t6 t7 t8)
  | (QztNode t5 t6 t7 t8) Qa6 => (QztNode t5 (qr t6) t7 t8)
  | (QztNode t5 t6 t7 t8) Qa7 => (QztNode t5 t6 (qr t7) t8)
  | (QztNode t5 t6 t7 t8) Qa8 => (QztNode t5 t6 t7 (qr t8))
  | (QztHubNode t58 t9 t10 t11) Qa9 => (QztHubNode t58 (qr t9) t10 t11)
  | (QztHubNode t58 t9 t10 t11) Qa10 => (QztHubNode t58 t9 (qr t10) t11)
  | (QztHubNode t58 t9 t10 t11) Qa11 => (QztHubNode t58 t9 t10 (qr t11))
  | (QztHubNode t58 t9 t10 t11) _ => (QztHubNode (qzt_put1 qa qr t58) t9 t10 t11)
  | _ _ => t
  end.

Definition qzt_put3 [qa1, qa2, qa3 : qarity; q1, q2, q3 : question]
                    : quiz_tree -> quiz_tree :=
  (qzt_put1 qa1 (qzt_put1 qa2 (qzt_put1 qa3 (QztLeaf q1 q2 q3)))).

Definition qzt_put3rot [qa1, qa2, qa3 : qarity; q1, q2, q3 : question] :
                       quiz_tree -> quiz_tree :=
  [t](qzt_put3 qa1 qa2 qa3 q1 q2 q3
        (qzt_put3 qa2 qa3 qa1 q2 q3 q1
          (qzt_put3 qa3 qa1 qa2 q3 q1 q2
             t))).

Definition qzt_put [qa1, qa2, qa3 : qarity; q1, q2, q3 : question] :
                   quiz_tree -> quiz_tree :=
  if (ltn (8) qa1) then (qzt_put3 qa1 qa2 qa3 q1 q2 q3) else
  (qzt_put3rot qa1 qa2 qa3 q1 q2 q3).

Definition qzt_empty : quiz_tree :=
  let mkn = [t](QztNode t t t t) in
  let n2 = (mkn (mkn QztNil)) in (QztHubNode (mkn n2) n2 n2 n2).

Definition normq [q : question] : question :=
  Cases q of
    (Qask1 qa)       => (QaskLR qa Qask0 Qask0)
  | (QaskL qa ql)    => (QaskLR qa ql Qask0)
  | (QaskR qa qr)    => (QaskLR qa Qask0 qr)
  | _                => q
  end.

Definition store_qz [qz : quiz] : quiz_tree -> quiz_tree :=
  Cases qz of
    (Quiz (QaskR qa1 q1) (QaskR qa2 q2)) =>
       Cases (normq q1) (normq q2) of
         (QaskLR qa1r q1l q1r) (QaskLR qa2r q2l q2r) =>
            if (ltn qa1r qa2r) then (qzt_put qa1 qa2 qa1r q1l q2 q1r)
            else (qzt_put qa1 qa2r qa2 q1 q2r q2l)
       | (QaskLR qa1r q1l q1r) _ =>
           (qzt_put qa1 qa2 qa1r q1l q2 q1r)
       | _ (QaskLR qa2r q2l q2r) =>
           (qzt_put qa1 qa2r qa2 q1 q2r q2l)
       | _ _ => [t]t
       end
  | _ => [t]t
  end.

Definition store_cf_qz [cf : config; t : quiz_tree] : quiz_tree :=
  let qz = (cfquiz cf) in
  (store_qz qz if (cfsym cf) then t else (store_qz (flipqz qz) t)).

Definition cfquiz_tree : configseq -> quiz_tree :=
  (foldr store_cf_qz qzt_empty).

(* Sanity checks; both computations should return the same result *)
(* (3361 for the full config list).                               *)

Fixpoint qzt_size [t : quiz_tree] : nat :=
  Cases t of
    (QztLeaf _ _ _ t') =>
       (S (qzt_size t'))
  | (QztNode t5 t6 t7 t8) =>
       (plus (qzt_size t5) (plus (qzt_size t6)
         (plus (qzt_size t7) (qzt_size t8))))
  | (QztHubNode t58 t9 t10 t11) =>
       (plus (qzt_size t58) (plus (qzt_size t9)
         (plus (qzt_size t10) (qzt_size t11))))
  | _ => (0)
  end.

Definition cf_main_arity [cf : config] : nat :=
  if (cfquiz cf) is (Quiz (QaskR qa _) _) then (qa :: nat) else (0).

Definition cf_qzt_size1 [cf : config] : nat :=
  let nperm = if (leq (cf_main_arity cf) (8)) then (3) else (1) in
  if (cfsym cf) then nperm else (double nperm).

Definition cf_qzt_size : configseq -> nat :=
  (foldr [cf](plus (cf_qzt_size1 cf)) (0)).

Definition configs_compiled [cfs : configseq] : Prop :=
  (qzt_size (cfquiz_tree cfs)) = (cf_qzt_size cfs).

(* end of sanity checks. *)

Fixpoint qzt_get1 [qa : qarity; t : quiz_tree] : quiz_tree :=
  Cases t qa of
    (QztNode t' _ _ _) Qa5 => t'
  | (QztNode _ t' _ _) Qa6 => t'
  | (QztNode _ _ t' _) Qa7 => t'
  | (QztNode _ _ _ t') Qa8 => t'
  | (QztHubNode _ t' _ _) Qa9 => t'
  | (QztHubNode _ _ t' _) Qa10 => t'
  | (QztHubNode _ _ _ t') Qa11 => t'
  | (QztHubNode t' _ _ _) _ => (qzt_get1 qa t')
  | _ _ => QztNil
  end.

Definition qzt_get2 [qa2, qa3 : qarity; t : quiz_tree] : quiz_tree :=
  (qzt_get1 qa3 (qzt_get1 qa2 t)).

Definition qzt_get3 [qa1, qa2, qa3 : qarity; t : quiz_tree] : quiz_tree :=
  (qzt_get2 qa2 qa3 (qzt_get1 qa1 t)).

Section FitQuizTree.

Variables cfs : configseq; g : hypermap.
Hypothesis Hg : (plain_cubic g).
Local De2 := (plain_eq Hg).
Local Dn3 := (cubic_eq Hg).

Lemma fit_normq : (x : g; q : question) (fitq x (normq q)) = (fitq x q).
Proof. By Move=> x q; Case: q => *; Rewrite: /fitq /= ?cats0. Qed.

Variable x1 : g.
Syntactic Definition x2 := (node x1).
Syntactic Definition x3 := (node x2).
Local ax1 : qarity := (qarity_of_nat (arity x1)).
Local ax2 : qarity := (qarity_of_nat (arity x2)).
Local ax3 : qarity := (qarity_of_nat (arity x3)).

Syntactic Definition eqa := [qa; y] (qa :: nat) =d (arity y).
Definition qzt_fita : bool := (and3b (eqa ax1 x1) (eqa ax2 x2) (eqa ax3 x3)).

Fixpoint qzt_fitl [t : quiz_tree] : bool :=
  Cases t of
    (QztLeaf q1 q2 q3 t') =>
    (orb (and3b (fitq (qstepR x1) q1) (fitq (qstepR x2) q2) (fitq (qstepR x3) q3))
         (qzt_fitl t'))
  | _ => false
  end.

Definition qzt_fit [t : quiz_tree] : bool :=
  (andb qzt_fita (qzt_fitl (qzt_get3 ax1 ax2 ax3 t))). 

Syntactic Definition quiz3 := [qa1; qa2; qa3; q1; q2; q3]
  (Quiz (QaskR qa1 (QaskLR qa3 q1 q3)) (QaskR qa2 q2)).

Lemma qzt_get_put1 : (qa, qa' : qarity; qr : quiz_tree -> quiz_tree; t : quiz_tree)
    qa = qa' /\ (qr (qzt_get1 qa t)) = (qzt_get1 qa (qzt_put1 qa' qr t)) 
 \/ (qzt_get1 qa t) = (qzt_get1 qa (qzt_put1 qa' qr t)).
Proof. Move=> qa qa' qr; Elim; Auto; Case qa'; Auto; Case qa; Auto. Qed.

Syntactic Definition Hqgp1 := qzt_get_put1.
Lemma qzt_fit_put3 : (qa1, qa2, qa3 : qarity; q1, q2, q3 : question; t : quiz_tree)
  (qzt_fit (qzt_put3 qa1 qa2 qa3 q1 q2 q3 t)) ->
   (fitqz (edge x2) (quiz3 qa1 qa2 qa3 q1 q2 q3)) \/ (qzt_fit t).
Proof.
Move=> qa1 qa2 qa3 q1 q2 q3 t; Case/andP=> [Hax]; Rewrite: /qzt_fit Hax.
Rewrite: /fitqz /= /eqd /= eqseqE -arity_face Enode /qstepR De2 /qstepL Dn3 -!catA.
Rewrite: /= 2!fitq_cat maps_adds eqseq_adds; Case/and3P: Hax; Do 3 Case/eqP.
Rewrite: /qzt_get3 /qzt_get2 /qzt_put3; Pose qr := (QztLeaf q1 q2 q3).
Case: (Hqgp1 ax1 qa1 (qzt_put1 qa2 (qzt_put1 qa3 qr)) t) => [[[][]]|[]]; Auto.
Case: (Hqgp1 ax2 qa2 (qzt_put1 qa3 qr) (qzt_get1 ax1 t)) => [[[][]]|[]]; Auto.
Case: (Hqgp1 ax3 qa3 qr (qzt_get1 ax2 (qzt_get1 ax1 t))) => [[[][]]|[]]; Auto.
Rewrite: !set11 /= {1 andb}lock andbC -lock; Case/orP; Auto.
Qed.

Lemma fitqz_rot : (y : g; qa1, qa2, qa3 : qarity; q1, q2, q3 : question)
  (fitqz y (quiz3 qa1 qa2 qa3 q1 q2 q3))
    = (fitqz (edge (face y)) (quiz3 qa3 qa1 qa2 q3 q1 q2)).
Proof.
Move=> y qa1 qa2 qa3 q1 q2 q3; Rewrite: /fitqz /= /eqd /= !eqseqE -!catA.
Rewrite: !fitq_cat !maps_adds !eqseq_adds /qstepL /qstepR !De2 Eface.
Rewrite: -{1 (node (edge y))}Enode !arity_face -{1 2 (edge y)}Eedge De2 Dn3.
Rewrite: -{8 9 y}De2 Eedge.
Case: ((qa1::nat) =d (arity y)) => /=; RightBy Rewrite: !andbF.
Congr andb; Rewrite: andbC -!andbA.
By Case ((qa2::nat) =d (arity (edge y))); RightBy Rewrite: /= !andbF.
Qed.

Lemma qzt_fit_put : (qa1, qa2, qa3 : qarity; q1, q2, q3 : question; t : quiz_tree)
  (qzt_fit (qzt_put qa1 qa2 qa3 q1 q2 q3 t)) ->
  (EX y : g | (fitqz y (quiz3 qa1 qa2 qa3 q1 q2 q3))) \/ (qzt_fit t).
Proof.
Move=> qa1 qa2 qa3 q1 q2 q3 t; Rewrite: /qzt_put /qzt_put3rot.
Case (ltn (8) qa1); LeftBy Case/qzt_fit_put3; Auto; Left; Exists (edge x2).
Case/qzt_fit_put3; LeftBy Left; Exists (edge x2).
Case/qzt_fit_put3; LeftBy Rewrite: fitqz_rot Enode; Left; Exists (edge x1).
Case/qzt_fit_put3; Auto.
By Rewrite: 2!fitqz_rot -{x1}Dn3 !Enode; Left; Exists (edge x3).
Qed.

Lemma fitqz_swap : (y : g; qa1, qa2, qa3 : qarity; q1, q2, q3 : question)
  (fitqz y (quiz3 qa1 qa2 qa3 q1 q2 q3))
    = (fitqz (face y) (Quiz (QaskR qa1 q1) (QaskR qa3 (QaskLR qa2 q3 q2)))).
Proof.
Move=> y qa1 qa2 qa3 q1 q2 q3; Rewrite: /fitqz /= /eqd /= !eqseqE -!catA.
Rewrite: !fitq_cat !maps_adds !eqseq_adds fitq_cat.
Rewrite: /qstepR /qstepL !De2 -{1 (node (edge y))}Enode !arity_face Eface.
By Rewrite: -{1 2 (edge y)}Eedge De2 Dn3 -{10 11 y}De2 Eedge; Repeat BoolCongr.
Qed.

Lemma qzt_fit_store : (qz : quiz; t : quiz_tree)
  (qzt_fit (store_qz qz t)) ->
  ((isQuizR qz) /\ (EX y : g | (fitqz y qz))) \/ (qzt_fit t).
Proof.
Move=> [q1 q2] t; Case: q1; Auto; Case: q2; Auto; Move=> qa2 q2 qa1 q1.
Move=> Hx; Pose qz := (Quiz (QaskR qa1 q1) (QaskR qa2 q2)).
Pose G := (EX y : g | (fitqz y qz)) \/ (qzt_fit t).
Cut G; LeftBy Move=> [H | H]; [Left; Split | Right].
Step HxG1: (qa1r : qarity; q1l, q1r : question)
             (normq q1) = (QaskLR qa1r q1l q1r) ->
             (qzt_fit (qzt_put qa1 qa2 qa1r q1l q2 q1r t)) -> G.
  Move=> qa1r q1l q1r Dq1' H; Case: {H}(qzt_fit_put H); RightBy Right.
  Move=> [y Hy]; Left; Exists y; Move: Hy; Rewrite: -Dq1' /fitqz /eqd /= !eqseqE.
  By Rewrite: fitq_cat fit_normq -fitq_cat.
Step HxG2: (qa2r : qarity; q2l, q2r : question)
             (normq q2) = (QaskLR qa2r q2l q2r) ->
             (qzt_fit (qzt_put qa1 qa2r qa2 q1 q2r q2l t)) -> G.
  Move=> qa2r q2l q2r Dq2' H; Case: {H}(qzt_fit_put H); RightBy Right.
  Move=> [y Hy]; Left; Exists (face y); Apply: (etrans ? Hy).
  Rewrite: fitqz_swap -Dq2' /fitqz /eqd /= !eqseqE !fitq_cat !maps_adds.
  By Rewrite: !eqseq_adds !andbA; Congr andb; Symmetry;  Apply: fit_normq.
Move: Hx; Simpl; Case: {-1}(normq q1) (erefl (normq q1));
  Case: {-1}(normq q2) (erefl (normq q2)); Try (By Right); EAuto.
Move=> qa2r q2l q2r Dq2 qa1r q1l q1r Dq1; Case (ltn qa1r qa2r); EAuto.
Qed.

Lemma qzt_fit_store_cf : (cf : config; t : quiz_tree)
  (qzt_fit (store_cf_qz cf t)) ->
  let qz = (cfquiz cf) in
  (or (and (isQuizR qz)
           (EX y : g | (fitqz y qz)) \/ (EX y : (mirror g) | (fitqz y qz)))
      (qzt_fit t)).
Proof.
Move=> cf t; Rewrite: /store_cf_qz /=; Def: qz := (cfquiz cf).
Case (cfsym cf); Repeat Case/qzt_fit_store; Auto;
  Move=> [Hqz Hgqz]; Left; Try By Split; Auto.
Step Hqz': (isQuizR qz) By Case: (qz) Hqz => [q1 q2]; Case q1; Case q2.
Split; Auto; Right; Case: Hgqz => [y Hy]; Rewrite: fitqz_flip //= in Hy.
By Exists (face y).
Qed.

Lemma qzt_fit_cfquiz : (cfs : configseq) (qzt_fit (cfquiz_tree cfs)) ->
   (EX cf | (cfs cf) & (EX qz |
      (EX y : g | (fitqz y qz)) \/ (EX y : (mirror g) | (fitqz y qz))
   &  (embeddable (cfring cf)) /\ (EX u | (valid_quiz (cfring cf) u qz)))).

Proof.
Elim=> [|cf cfs' Hrec] /=.
  By Rewrite: /qzt_fit andbC; Case: {}ax1 => //; Case: {}ax2 => //; Case ax3.
Case/qzt_fit_store_cf.
  Move=> [Hqz Hgqz]; Exists cf; [Apply: setU11 | Exists (cfquiz cf); Auto].
  By Split; [Apply embeddable_cfquiz | Apply valid_cfquiz].
By Case/Hrec {Hrec} => [cf' Hcf' Hx]; Exists cf'; LeftBy Apply setU1r.
Qed.

Definition qzt_truncate [t : quiz_tree] : quiz_tree :=
  if t is (QztHubNode t58 _ _ _) then
    if t58 is (QztNode _ _ _ _) then t58 else t
  else t.

Lemma qzt_get1_truncate : (qa : qarity; t : quiz_tree)
  let t' = (qzt_get1 qa (qzt_truncate t)) in
  (qzt_proper t') -> t' = (qzt_get1 qa t).
Proof. By Do 3 Case=> //. Qed.

End FitQuizTree.

(*  global sanity check, using the functions define above
Require configurations.

Eval Compute in (qzt_size (cfquiz_tree the_configs)).
Eval Compute in (cf_qzt_size the_configs).
Goal (configs_compiled the_configs). Split. Save the_configs_compiled.
*)


Unset Implicit Arguments.
