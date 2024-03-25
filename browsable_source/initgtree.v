(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require tacticext.
Require boolprop.
Require funs.
Require dataset.
Require natprop.
Require seq.
Require color.
Require chromogram.
Require gtree.
Require dyck.

Set Implicit Arguments.

(* Creation of the initial (full) chromogram tree. We reuse pairs to create  *)
(* the 2D table of trees indexed by (depth, bit0).                           *)

Section InitialGtree.

Lemma gtreeDataP : (comparable gtree).
Proof. Rewrite: /comparable; Decide Equality. Qed.
Lemma gtreePairDataP : (comparable gtree_pair).
Proof. Rewrite: /comparable; Decide Equality; Apply: gtreeDataP. Qed.
Definition gtreePairData : dataSet := Eval Compute in (compareData gtreePairDataP).
Canonical Structure gtreePairData.

Definition gtree_table : Set := (seq gtreePairData).

Definition init_gtree_h1 : gtree_table :=
  (seq3 (Gtree_pair Gtree_leaf01 Gtree_leaf0)
        (Gtree_pair Gtree_leaf13 Gtree_leaf12)
        (Gtree_pair Gtree_leaf23 Gtree_leaf23)).

Definition gtree_merge_pairs [pt0, pt1, pt2 : gtree_pair] : gtree_pair :=
  let (t0, t0') = pt0 in let (t1, t1') = pt1 in let (t2, t3) = pt2 in 
  (Gtree_pair (Gtree_node t0 t1' t2 t3) (Gtree_node t0' t1 t3 t2)).

Fixpoint gtree_merge_line
    [pt0, pt1, pt2 : gtree_pair; lpt : gtree_table; d : nat] : gtree_table :=
  let rest =
    Cases d lpt of
      (0) _ =>
        (seq0::gtree_table)
    | (S d') Seq0 =>
        (seq2 (gtree_merge_pairs empty_gtree_pair pt0 pt1)
              (gtree_merge_pairs empty_gtree_pair empty_gtree_pair pt0))
    | (S d') (Adds pt lpt') =>
        (gtree_merge_line pt pt0 pt1 lpt' d')
    end in
  (Adds (gtree_merge_pairs pt0 pt1 pt2) rest).

Fixpoint gtree_init_table [d, h' : nat] : gtree_table :=
  Cases h' of
    (0) => init_gtree_h1
  | (S h'') =>
      let tab = (gtree_init_table (S d) h'') in
      if tab is (Adds pt1 (Adds pt0 lpt)) then
        (gtree_merge_line pt0 pt1 empty_gtree_pair lpt d)
      else tab
  end.

Definition gtree_init_tree [h : nat] : gtree :=
  Cases h (gtree_init_table (0) (pred h)) of
    (S _) (Adds (Gtree_pair t _) _) => t
  | _ _ => Gtree_empty
  end.

Definition init_gtree_spec [h : nat; w : chromogram] : bool :=
  (andb (size w) =d h (gram_balanced (0) false (cgram (0) false w))).

Lemma match_count_balanced : (h : nat; et : colseq)
  (match_count (init_gtree_spec h) Bstack0 et)
    = (if (andb (size et) =d h (negb (ctrace et Color0)))
       then (dyck (count_cbit1 (ctrace et))) else (0)).
Proof.
Move=> h et; Rewrite: /init_gtree_spec /ctrace /dyck; Pose sb := (seq0::bitseq).
Rewrite: -{Bstack0}/(stack_of_bitseq sb) -{-4 (0)}/(size sb) -(add0c (sumt et)).
Step Hc1: (cbit1 Color0) = (odd (size sb)) By Done.
Def Dsbs: sbs := (foldr addb false).
Step Hc0: (cbit0 Color0) = (addb false (sbs sb)) By Rewrite Dsbs.
Elim: et h {-4}Color0 sb {}false Hc0 Hc1.
  Move=> [|h] c // [|b lb] b0 /=.
    By Rewrite: Dsbs /= addbF; Case; Case c.
  By Case; Case: {lb}(size lb) => /=; Case: c => //; Case b0.
Move=> e et Hrec h c lb b0; Rewrite: add_last_adds /= addcA; Case: h => [|h].
  Case De: e (match_count_0) => [|||] Em0 Enn /=; Auto;
    Rewrite: Em0 /addn //=; Case (stack_of_bitseq lb); Auto.
Move=> Hc0 Hc1; Move: {Hrec}(Hrec h (addc e c)).
Rewrite: cbit0_addc cbit1_addc (addcC e c) ~Hc0 ~Hc1 ~{sbs}Dsbs /=.
Def: cet := (add_last et (addc (addc c e) (sumt et))); Rewrite: /setU1 eqdSS.
Move: {c cet}((size et) =d h) (cet Color0) (count_cbit1 cet) => b_h bc0 n23.
Move=> Hrec; Move: (Hrec (Adds (cbit0 e) lb) b0) Hrec.
Rewrite: /eqd /= 2!addbA (addbC b0).
Case De: e => [|||] /= Hrec0 Hrec; First [
  By Rewrite andbC
| By Apply Hrec
| By Rewrite: ~Hrec0 //; Case: lb Hrec => [|b lb''] /=; [
    Clear; Case: {3}n23 => *; Rewrite: /= ?addn0
  | Rewrite: ?negb_elim 1?addbA -1?(addbC b); Case: b => /=;
    Move=> H; Try Rewrite: ~H ?negb_elim //;
    Case: (andb b_h (negb bc0))]].
Qed.

Fixpoint gtree_table_sub [tab : gtree_table] : nat -> bool -> gtree :=
  [n]Cases tab n of
    Seq0 _ => [_]Gtree_empty
  | (Adds pt _) (0) => (gtree_pair_sub pt)
  | (Adds _ tab') (S n') => (gtree_table_sub tab' n')
  end.
Syntactic Definition tsub := gtree_table_sub.

Lemma gtree_mem_init_tree : (h : nat; w : chromogram)
  (gtree_mem (gtree_init_tree h) w) = (init_gtree_spec h w).
Proof.
Move=> [|h] w; [By Rewrite gtree_mem_empty; Case w | Simpl].
Transitivity (gtree_mem (tsub (gtree_init_table (0) h) (0) false) w).
  By Case (gtree_init_table (0) h).
Move: (leqnn (0)); Rewrite: /init_gtree_spec.
Def: d := {2 3}(0); Move: (0) {}false w.
Apply (proj2 (ltn (if d is (0) then (0) else (1)) (size (gtree_init_table d h)))).
Elim: h d => [|h Hrec] d /=.
  By Split; [Case d | Move=> [|[|[|d']]] [|] [|s [|s' w']] //; Case s].
Case: {Hrec}(Hrec (S d)); Move: (gtree_init_table (S d) h).
Move=> [|pt1 [|pt0 lpt]] // _ Hsub.
Split; LeftBy Case: d {Hsub} => [|[|d]]; Case lpt.
Move=> dw bw w Hd; Transitivity (gtree_mem
  [elt := (Adds empty_gtree_pair (Adds pt1 (Adds pt0 lpt)))]
   (Gtree_node (tsub elt (S (S dw)) bw) (tsub elt (S dw) (negb bw))
              (tsub elt dw bw) (tsub elt dw (negb bw))) w).
  Elim: dw d Hd pt0 pt1 {}empty_gtree_pair lpt {Hsub}.
    Move=> d Hd [t0 t0'] [t1 t1'] [t2 t3] lpt; Rewrite: /gtree_merge_line /=.
    By Case d; Case: bw => /=.
  Move=> dw Hrec [|d] Hd // pt0 pt1 pt2 [|pt lpt]; RightBy Apply: (Hrec d).
  Case: dw {Hrec Hd} => [|dw]; LeftBy Case: pt0 pt1 bw => [t1 t1'] [t2 t3] [|].
  Case: dw => [|dw]; LeftBy Case: pt0 bw => [t2 t3] [|].
  By Case: w bw => [|[|||] w] [|]; Rewrite: /= ?gtree_mem_empty.
Case: w => [|[|||] w] //=; First [
  Exact (Hsub (S dw) ? w Hd) | Exact (Hsub ? ? w (leqW Hd))
| Case: dw Hd => [|dw] Hd; [
    Rewrite andbF; Case bw; Exact (gtree_mem_empty w)
  | Exact (Hsub ? ? w (leqW (leqW Hd)))]].
Qed.

End InitialGtree.

Unset Implicit Arguments.

