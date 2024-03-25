(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require tacticext.
Require boolprop.
Require funs.
Require dataset.
Require natprop.
Require seq.
Require color.
Require ctree.
Require dyck.

Set Implicit Arguments.

(* Creation of an initial (full) coloring tree, and its correctness theorem. *)
(* This tree is constructed by making successively tables of its non-empty   *)
(* leaves, then subtrees of height 1, 2, etc until h - 2, where h is the     *)
(* perimeter length (aka the ring size). Subtrees of odd traces are pruned   *)
(* at this stage, and the final tree (of height h - 1) is assembled from the *)
(* three pruned subtrees of height h - 2.                                    *)
(*   The tables are simply lists of tree pairs. The #n23th pair contains the *)
(* two subtrees that can occur after a trace where Color2 and Color3 occur a *)
(* total of n23 times; the first component of the tuple occurs at traces     *)
(* whose color sum is even ((color_bit0 (trace_sum et)) = false), the second *)
(* at odd-sum traces.                                                        *)

Lemma ctreeDataP : (comparable ctree).
Proof. Rewrite: /comparable; Decide Equality. Qed.
Definition ctree_data : dataSet := Eval Compute in (compareData ctreeDataP).
Canonical Structure ctree_data.

Lemma ctreePairDataP : (comparable ctree_pair).
Proof. Rewrite: /comparable; Decide Equality; Apply: ctreeDataP. Qed.
Definition ctreePairData : dataSet := Eval Compute in (compareData ctreePairDataP).
Canonical Structure ctreePairData.

Definition ctree_table : Set := (seq ctreePairData).

Syntactic Definition ctz := ctree_empty_pair.
Definition ctree_table_sub [tab : ctree_table; n23 : nat; b0 : bool] : ctree :=
  (ctree_pair_sub (sub ctz tab n23) b0).

(* First, leaf construction.                                                 *)

Fixpoint ctree_add_dyck [m, n : nat] : ctree -> ctree :=
  if n is (S n') then [t](iter_n (S m) [m'](ctree_add_dyck (S m') n') t)
  else Ctree_leaf.

Fixpoint ctree_leaf_table_from [lf : ctree; n, h : nat] : ctree_table :=
  Cases h of
    (0) => seq0
  | (1) => (seq1 (Ctree_pair lf lf))
  | (S (S h')) =>  (Adds (Ctree_pair lf lf)
                   (Adds (Ctree_pair Ctree_empty lf)
                   (ctree_leaf_table_from (ctree_add_dyck (2) n lf) (S n) h')))
  end.

Definition ctree_leaf_table [h : nat] : ctree_table :=
  let leaf1 = (Ctree_leaf Ctree_empty) in
  (Adds (Ctree_pair Ctree_empty leaf1) (ctree_leaf_table_from leaf1 (0) h)).

(* Pairs are merged pairwise to build higher trees.                          *)
(* Ctree_node instead of ctree_cons would be correct here, but hard to prove.*)

Definition ctree_merge_pair [tu, tu' : ctree_pair] : ctree_pair :=
  let (t0, t1) = tu in let (t2, t3) = tu' in
  (Ctree_pair (ctree_cons t1 t2 t3) (ctree_cons t0 t3 t2)).

Definition ctree_merge_table [tab : ctree_table] : ctree_table :=
  if tab is (Adds line tab') then (pairmap ctree_merge_pair line tab') else tab.

(* Pruning odd permutations.                                                 *)

Fixpoint ctree_prune_1 [t : ctree] : ctree :=
  if t is (Ctree_node t1 t2 t3) then
    (ctree_cons (ctree_prune_1 t1) t2 Ctree_empty)
  else t.

Fixpoint ctree_prune_2 [t : ctree] : ctree :=
  if t is (Ctree_node t1 t2 t3) then
    (ctree_cons Ctree_empty (ctree_prune_2 t2) t3)
  else t.

Fixpoint ctree_prune_3 [t : ctree] : ctree :=
  if t is (Ctree_node t1 t2 t3) then
    (ctree_cons t1 Ctree_empty (ctree_prune_3 t3))
  else t.

(* Putting everything together.                                              *)

Definition ctree_init_tree [h : nat] : ctree :=
  if (iter (pred h) ctree_merge_table (ctree_leaf_table h))
    is (Adds (Ctree_pair t0 t1) (Adds (Ctree_pair t2 t3) _)) then
      (ctree_cons (ctree_prune_1 t1) (ctree_prune_2 t2) (ctree_prune_3 t3))
  else Ctree_empty.

(* Leaf correctness. *)

Lemma ctree_add_dyck_leaf_of : (m, n, d : nat)
  (ctree_add_dyck m n (ctree_leaf_of d))
     = (ctree_leaf_of (addn (gen_dyck (S m) (addn m (double n))) d)).
Proof.
Move=> m n; Elim: n m => [|n Hrecn] m /=.
  By Rewrite: addn0 gen_dyck_all_close.
Elim: m => [|m Hrecm] d; Rewrite: doubleS /=; LeftBy Rewrite: addn0 Hrecn.
By Rewrite: Hrecm Hrecn doubleS addnA addnI !addnS.
Qed.

Lemma ctree_leaf_table_size : (h : nat)
   (size (ctree_leaf_table h)) = (S h).
Proof.
Move=> h; Rewrite: /ctree_leaf_table_from /=; Congr S.
Rewrite: -(odd_double_half h) addnC; Move: (Ctree_leaf Ctree_empty) (0).
By Elim: (half h) => [|h2 Hrec] t n; [Case (odd h) | Rewrite: doubleS /= Hrec].
Qed.

Lemma ctree_leaf_table_sub : (h, n23 : nat; Hn23 : (leq n23 h); b0 : bool)
  let c = (ccons (odd n23) b0) in
  let cet = (add_last seq0 (addc c (sumt seq0))) in
  let c23 = (addn n23 (count_cbit1 cet)) in
  (ctree_table_sub (ctree_leaf_table h) n23 b0)
    = (if (cet Color0) then Ctree_empty else (ctree_leaf_of (dyck c23))).
Proof.
Move=> h n23; Rewrite: /ctree_leaf_table -{1 2 4 n23}odd_double_half.
Move: (odd n23) (half n23) => b1 m; Rewrite (addnC b1); Move=> Hh b0.
Rewrite: /= addc0 cbit1_ccons /setU1 orbF addn0 -addnA -{2 m}addn0.
Pose t1 := (Ctree_leaf Ctree_empty).
Rewrite: -{1 t1}/(ctree_leaf_of (dyck (double (0)))).
Rewrite: -{t1}/(ctree_leaf_of (dyck (double (1)))) ~{t1}.
Elim: m (0) h Hh => [|m Hrec] n.
  By Rewrite: /= !add0n addnC; Case: b1; [Move=> [|[|h]] // | Idtac]; Case b0.
Move=> [|[|h]] Hh //.
By Rewrite: addSnnS -(Hrec (S n) h Hh) /dyck /= ctree_add_dyck_leaf_of !addn0.
Qed.

(* Global correctness; we run through the construction twice, once to check *)
(* that subtrees are proper, and once to check the counts.                  *)

Lemma ctree_init_tree_proper : (h : nat)
  (ctree_proper h (ctree_init_tree h)).
Proof.
Move=> h; Case Dh: h => [|h'] //=.
Rewrite: /ctree_init_tree; Def Dltab : ltab := (ctree_leaf_table (S h')); Simpl.
Def Dtab: tab := (iter h' ctree_merge_table ltab).
Step [Hlen Hsub]: (addn h' (size tab)) = (S h)
        /\ (n23 : nat; Hn23 : (ltn n23 (size tab)); b0 : bool)
           (ctree_proper h' (ctree_table_sub tab n23 b0)).
  Move: (leq_addl (1) h'); Rewrite: ~{tab}Dtab {1}/addn /= -Dh.
  Elim: (h') => [|n Hrec] Hn.
    Rewrite: /= ~{ltab}Dltab -Dh ctree_leaf_table_size; Split; LeftDone.
    Move {Hn} => n23 Hn23 b0; Rewrite (ctree_leaf_table_sub 1!h Hn23).
    Def: c := (ccons (odd n23) b0); Rewrite: /= addc0 /setU1.
    Case: (c =d Color0) => //=; Apply ctree_leaf_of_proper.
  Def Dctp' : ctp' := (ctree_proper (S n)); Simpl.
  Case: (iter n ctree_merge_table ltab) {Hrec}(Hrec (leqW Hn)) => [|pt0 tab].
    By Move=> [Dn _]; Move: (ltnW Hn); Rewrite: leqNgt -Dn /=  addn0 leqnn.
  Move=> [Dn Htab]; Rewrite: /= addSnnS size_pairmap /=; Split; LeftDone.
  Move=> n23 Hn23 b0; Move: {Htab Dn}(Htab ? (ltnW Hn23)) (Htab (S n23) Hn23).
  Rewrite: /ctree_table_sub [x : ctree_pair](sub_pairmap x x) //=.
  Case: {pt0 Hn23}(sub ctz (Adds pt0 tab) n23) => [t0 t1].
  Case: {n23 tab}(sub ctz tab n23) => [t2 t3].
  Do 2 (Move=> Ht; Move: {Ht}(Ht false) (Ht true) => /=; Do 2 Intro).
  By Case: b0; Rewrite: /= Dctp'; Apply ctree_cons_proper.
Step Dsz: (size tab) = (2) By Apply (!addn_injl h'); Rewrite: Hlen Dh addnC.
Case: tab {Dtab Hlen} Dsz Hsub => [|[t0 t1] [|[t2 t3] tab']] //=.
Move=> _ Hsub; Def: Hsub1 := (Hsub (1) (erefl ?)).
Move: {Hsub Hsub1}(Hsub (0) (erefl ?) true) (Hsub1 false) (Hsub1 true).
Rewrite: /ctree_table_sub /= ~{t0 tab' h Dh ltab Dltab}.
Move=> Ht1 Ht2 Ht3; Apply ctree_cons_proper;
  [ Move: t1 Ht1 {t2 Ht2 t3 Ht3}
  | Move: {t1 Ht1} t2 Ht2 {t3 Ht3}
  | Move: {t1 Ht1 t2 Ht2} t3 Ht3 ];
  Elim: h' => [|h Hrec] [t1 t2 t3|lf|] //= [Hne Ht1 Ht2 Ht3];
  Apply ctree_cons_proper; Auto; Split.
Qed.

Lemma ctree_sub_init_tree : (h : nat; et : colseq)
  let et_ok =
    (andb (andb (size et) =d h (negb (ctrace et Color0))) (even_trace et))
  in (ctree_sub (ctree_init_tree h) et)
       = (if et_ok then (dyck (count_cbit1 (ctrace et))) else (0)).
Proof.
Move=> h; Case Dh: h => [|h']; [By Case | Rewrite: /ctree_init_tree /pred -Dh].
Def Dltab : ltab := (ctree_leaf_table h).
Def Dtab: tab := (iter h' ctree_merge_table ltab).
Step [Hlen Hsub]: (addn h' (size tab)) = (S h)
  /\ (n23 : nat; En23 : (ltn n23 (size tab)); b0 : bool; et : colseq)
     let c = (ccons (odd n23) b0) in
     let cet = (add_last et (addc c (sumt et))) in
     let c23 = (addn n23 (count_cbit1 cet)) in
     let et_ok = (andb (size et) =d h' (negb (cet Color0))) in
     (ctree_sub (ctree_table_sub tab n23 b0) et)
       = (if et_ok then (dyck c23) else (0)).
  Move: (leq_addl (1) h'); Rewrite: ~{tab}Dtab {1}/addn /= -Dh.
  Elim: {}h' => [|n Hrec] Hn /=.
    Rewrite: ~{ltab}Dltab ctree_leaf_table_size; Split; LeftDone.
    Move=> /= n23 Hn23 b0; Rewrite: ~{Hn}(ctree_leaf_table_sub 1!h Hn23).
    Def: c := (ccons (odd n23) b0).
    Move=> [|e et]; Rewrite: /= /setU1 addc0; Case: (c =d Color0) => //;
      Apply: ctree_sub_leaf_of.
  Case: (iter n ctree_merge_table ltab) {Hrec}(Hrec (leqW Hn)) => [|pt tab].
    By Move=> [Dn _]; Move: (ltnW Hn); Rewrite: leqNgt -Dn /=  addn0 leqnn.
  Rewrite: /= -addSnnS /= size_pairmap; Move=> [Dn Htab]; Split; LeftDone.
  Move=> n23 Hn23 b0; Move: {Htab Dn}(Htab ? (ltnW Hn23)) (Htab (S n23) Hn23).
  Rewrite: /ctree_table_sub [x : ctree_pair](sub_pairmap x x) //=.
  Case: {pt Hn23}(sub ctz (Adds pt tab) n23) => [t0 t1].
  Case: {tab}(sub ctz tab n23) => [t2 t3].
  Move=> Hsub; Move: {Hsub}(Hsub false) (Hsub true) => /= Ht0 Ht1.
  Move=> Hsub; Move: {Hsub}(Hsub false) (Hsub true) => /= Ht2 Ht3.
  Move=> [|e et]; LeftBy Case b0; Rewrite: ctree_sub_cons.
  Rewrite: /= {2}/addn addcA -[c](ccons_cbits (addc c e)) /setU1.
  Rewrite: eqdSS cbit0_addc cbit0_ccons cbit1_addc cbit1_ccons.
  Case: e; Rewrite: /= ?addbT ?addbF -1?addSnnS;
    By Case: b0; Rewrite: /= ctree_sub_cons /= ?andbF.
Step Dsz: (size tab) = (2) By Apply (!addn_injl h'); Rewrite: Hlen Dh addnC.
Case: tab Dsz Hsub {Dtab Hlen} => [|[t0 t1] [|[t2 t3] tab']] //=.
Move=> _ Hsub {ltab Dltab}; Def: Hsub1 := (Hsub (1) (erefl ?)).
Move: {Hsub Hsub1}(Hsub (0) (erefl ?) true) (Hsub1 false) (Hsub1 true).
Rewrite: /ctree_table_sub ~{t0 tab'}/= ~{h}Dh.
Move=> Ht1 Ht2 Ht3 et; Rewrite: ctree_sub_cons /=.
Move: {1}(even_trace et) (erefl (even_trace et)).
Case: et => [|e et] tec; Rewrite: // /ctrace add_last_adds /= eqdSS;
  Case: e => /=; [ By Rewrite andbF
    | Move: {}t1 (Ht1 et) | Move: {}t2 (Ht2 et) | Move: {}t3 (Ht3 et)];
  Move {t1 Ht1 t2 Ht2 t3 Ht3} => t Ht Etec;
  By (Transitivity (if tec then (ctree_sub t et) else (0));
  [ Rewrite: ~{h' tec Ht}Etec; Elim: et t => [|e et Hrec] [t1 t2 t3|lf|];
    Rewrite: /= ?if_same // ctree_sub_cons //;
    Case: e; Rewrite: /= ?if_same
  | Rewrite: -Etec andb_sym; Case tec]).
Qed.

Unset Implicit Arguments.
