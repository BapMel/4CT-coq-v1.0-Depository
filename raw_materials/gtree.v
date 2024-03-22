(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require tacticext.
Require boolprop.
Require funs.
Require dataset.
Require natprop.
Require seq.
Require color.
Require chromogram.

Set Implicit Arguments.

(* Sets of chromograms are stored as 4-way trees, much like the edge traces. *)
(* In a way, gram trees are simpler than coloring trees because they don't   *)
(* store matching counts; however, to save space the last two layers have    *)
(* been collapsed, so that there are eight different kinds of leaves (three  *)
(* could suffice, but we would need to track context kinds in the inner loop *)
(* of the restrict procedure). The only real operations on gram trees are    *)
(* initialization and restriction, so this file is mostly boilerplate.       *)

Inductive gtree : Set :=
  Gtree_node  : (t0, t1, t2, t3 : gtree) gtree
| Gtree_leaf0 : gtree
| Gtree_leaf1 : gtree
| Gtree_leaf2 : gtree
| Gtree_leaf3 : gtree
| Gtree_leaf01 : gtree
| Gtree_leaf12 : gtree
| Gtree_leaf13 : gtree
| Gtree_leaf23 : gtree
| Gtree_empty  : gtree.

(* The following classifiers are effective. *)

Definition gtree_empty [t : gtree] : bool :=
  if t is Gtree_empty then true else false.

Lemma fold_gtree_empty : (A : Set; ve, vne : A; t : gtree)
  (if t is Gtree_empty then ve else vne)
     = (if (gtree_empty t) then ve else vne).
Proof. By Move=> A ve vne; Case. Qed.

Lemma gtree_emptyP : (t : gtree) (reflect t = Gtree_empty (gtree_empty t)).
Proof. Move=> t; Case t; Constructor; Done. Qed.

Definition gtree_empty_empty := [t; H](gtree_emptyP t H).
Opaque gtree_empty_empty.

(* Only the membership function needs to be defined on trees; enumerating *)
(* matches can be deifned based solely on the characteristic function.    *)

Fixpoint gtree_mem [t : gtree; w : chromogram] : bool :=
  Cases t w of
    (Gtree_node t0 t1 t2 t3) (Adds s w') => 
      (gtree_mem (!gram_symbol_rec [_]? t0 t1 t2 t3 s) w')
  | Gtree_leaf0  (Adds Gpush Seq0) => true
  | Gtree_leaf1  (Adds Gskip Seq0) => true 
  | Gtree_leaf2  (Adds Gpop0 Seq0) => true 
  | Gtree_leaf3  (Adds Gpop1 Seq0) => true 
  | Gtree_leaf01 (Adds Gpush Seq0) => true
  | Gtree_leaf01 (Adds Gskip Seq0) => true
  | Gtree_leaf12 (Adds Gskip Seq0) => true
  | Gtree_leaf12 (Adds Gpop0 Seq0) => true
  | Gtree_leaf13 (Adds Gskip Seq0) => true
  | Gtree_leaf13 (Adds Gpop1 Seq0) => true
  | Gtree_leaf23 (Adds Gpop0 Seq0) => true
  | Gtree_leaf23 (Adds Gpop1 Seq0) => true
  | _ _ => false
  end.

(* Functions that check for / count matches for arbitrary predicates. *)
(* Could move to bare chromograms, or to a separate ``match'' file.   *)

Definition spec_ctree : Set := colseq -> bool.

Fixpoint has_match [bs : bit_stack; ct : spec_ctree; w : chromogram] : bool :=
  let sct = [e;et](ct (Adds e et)) in
  Cases w of 
    Seq0 => (ct seq0)
  | (Adds Gpush w') => (orb (has_match (Bpush0 bs) (sct Color2) w')
                            (has_match (Bpush1 bs) (sct Color3) w'))
  | (Adds Gskip w') => (has_match bs (sct Color1) w')
  | (Adds Gpop0 w') =>
      Cases bs of
        (Bpush0 bs') => (has_match bs' (sct Color2) w')
      | (Bpush1 bs') => (has_match bs' (sct Color3) w')
      | _ => false
      end
  | (Adds Gpop1 w') =>
      Cases bs of
        (Bpush0 bs') => (has_match bs' (sct Color3) w')
      | (Bpush1 bs') => (has_match bs' (sct Color2) w')
      | _ => false
      end
  end.

Lemma has_matchP : (bs : bit_stack; ct : spec_ctree; w : chromogram)
  (reflect (EX et | (ct et) & (matchpg bs et w)) (has_match bs ct w)).
Proof.
Move=> bs ct w; Elim: w bs ct => [|s w Hrec] bs ct.
  Simpl; Case Hct: (ct seq0); Constructor; LeftBy Exists (seq0::colseq).
  By Move=> [[|c et] Hct' Het] //; Case/idP: Hct.
Case: s; Rewrite: /= -/colseq.
  Case: (Hrec (Bpush0 bs) [et](ct (Adds Color2 et))) => [Hc02 | Hn02].
      By Left; Case: Hc02 => [et Hct Hm]; Exists (Adds Color2 et).
    Case: (Hrec (Bpush1 bs) [et](ct (Adds Color3 et))) => [Hc13 | Hn13].
      By Left; Case: Hc13 => [et Hct Hm]; Exists (Adds Color3 et).
    By Right; Move=> [[|[|||] et] Hct Het] //;
      [Apply Hn02 | Apply Hn13]; Exists et.
  Case: (Hrec bs [et](ct (Adds Color1 et))) => [Hc1 | Hn1].
      By Left; Case: Hc1 => [et Hct Hm]; Exists (Adds Color1 et).
    By Right; Move=> [[|[|||] et] Hct Het] //; Apply Hn1; Exists et.
  Case: bs => [|bs|bs].
      By Right; Move=> [[|[|||] et] Hct Het].
    Case: (Hrec bs [et](ct (Adds Color2 et))) => [Hc2 | Hn2].
        By Left; Case: Hc2 => [et Hct Hm]; Exists (Adds Color2 et).
      By Right; Move=> [[|[|||] et] Hct Het] //; Apply Hn2; Exists et.
    Case: (Hrec bs [et](ct (Adds Color3 et))) => [Hc3 | Hn3].
        By Left; Case: Hc3 => [et Hct Hm]; Exists (Adds Color3 et).
      By Right; Move=> [[|[|||] et] Hct Het] //; Apply Hn3; Exists et.
  Case: bs => [|bs|bs].
      By Right; Move=> [[|[|||] et] Hct Het].
    Case: (Hrec bs [et](ct (Adds Color3 et))) => [Hc3 | Hn3].
        By Left; Case: Hc3 => [et Hct Hm]; Exists (Adds Color3 et).
      By Right; Move=> [[|[|||] et] Hct Het] //; Apply Hn3; Exists et.
    Case: (Hrec bs [et](ct (Adds Color2 et))) => [Hc2 | Hn2].
        By Left; Case: Hc2 => [et Hct Hm]; Exists (Adds Color2 et).
      By Right; Move=> [[|[|||] et] Hct Het] //; Apply Hn2; Exists et.
Qed.

Syntactic Definition xmatchP := has_matchP | 3.

Definition spec_gtree : Set := chromogram -> bool.

Fixpoint match_count [st : spec_gtree; bs : bit_stack; et : colseq] : nat :=
  let sub_st = [s : gram_symbol; w : chromogram](st (Adds s w)) in
  Cases et of
    Seq0 => if (st seq0) then (1) else (0)
  | (Adds Color0 _) => (0)
  | (Adds Color1 et') =>
       (match_count (sub_st Gskip) bs et')
  | (Adds Color2 et') =>
       let sub_pop = Cases bs of
         Bstack0 => (0)
       | (Bpush0 bs') => (match_count (sub_st Gpop0) bs' et')
       | (Bpush1 bs') => (match_count (sub_st Gpop1) bs' et')
       end in
       (addn (match_count (sub_st Gpush) (Bpush0 bs) et') sub_pop)
  | (Adds Color3 et') =>
       let sub_pop = Cases bs of
         Bstack0 => (0)
       | (Bpush0 bs') => (match_count (sub_st Gpop1) bs' et')
       | (Bpush1 bs') => (match_count (sub_st Gpop0) bs' et')
       end in
       (addn (match_count (sub_st Gpush) (Bpush1 bs) et') sub_pop)
  end.

Definition gtree_sub [t : gtree] : bit_stack -> colseq -> nat :=
  (match_count (gtree_mem t)).

Lemma match_countP : (st : spec_gtree; bs : bit_stack; et : colseq)
  (reflect (EX w | (st w) & (matchpg bs et w))
     (negb (0) =d (match_count st bs et))).
Proof.
Move=> st bs et; Elim: et st bs.
  Move=> st bs; Simpl; Case Hst: (st seq0); Constructor.
    By Exists (seq0::chromogram).
  By Move=> [[|s w] Hwt Hwe]; Rewrite: ?Hst in Hwt.
Step Eneq0addn: (n, n' : nat)
    let neq0 = [m](negb (0) =d m) in
    (neq0 (addn n n')) = (orb (neq0 n) (neq0 n')).
  Move=> [|n] [|n']; Rewrite: -?addnSnnS; Done.
Move=> [|||] et Hrec st bs; Rewrite: /= ?eq0E ?eqnE ?Eneq0addn -/chromogram;
  [Idtac
  | Case: {Hrec}(Hrec [w](st (Adds Gskip w)) bs) => [Hw | Hnw]
  | Case: (Hrec [w](st (Adds Gpush w)) (Bpush0 bs)) => [Hw | Hnw]
  | Case: (Hrec [w](st (Adds Gpush w)) (Bpush1 bs)) => [Hw | Hnw]];
First [ Constructor
      | Case: bs Hnw => [|bs|bs] Hnw; First [ Constructor
      | Case: (Hrec [w](st (Adds Gpop0 w)) bs) => [Hw | Hnw']; Constructor
      | Case: (Hrec [w](st (Adds Gpop1 w)) bs) => [Hw | Hnw']; Constructor]];
First [ Rename Hw into Hw; Case: Hw => [w Hwe Hwt];
        First [ By Exists (Adds Gpush w) | By Exists (Adds Gskip w)
              | By Exists (Adds Gpop0 w) | By Exists (Adds Gpop1 w)]
      | Move=> [[|[|||] w] Hwe Hwt];
First [ Done | By Apply Hnw; Exists w | By Apply Hnw'; Exists w]].
Qed.

Syntactic Definition nmatchP := match_countP | 3.

(* The gtree_empty4 function serves two purposes :                          *)
(*   - it allows contraction of empty trees, and reuse of unmodified trees  *)
(*   - it interlocks the tree computation, so that trees do NOT contain     *)
(*     thunks.                                                              *)
(* The latter point implies that the function must NOT short-circuit tests  *)

Definition gtree_empty_and [t : gtree; b : bool] : bool :=
  Cases t b of
    _ false => false
  | Gtree_empty true => true
  | _ _ => false
  end.

Lemma gtree_empty_and_spec : (t : gtree; b : bool)
  (gtree_empty_and t b) = (andb (gtree_empty t) b).
Proof. By Move=> t [|]; Case t. Qed.

Definition gtree_empty4 [t : gtree] : bool :=
  if t is (Gtree_node t0 t1 t2 t3) then
    (gtree_empty_and t0 (gtree_empty_and t1
       (gtree_empty_and t2 (gtree_empty t3))))
  else false.

Inductive are_4_Gtree_empty : (t0, t1, t2, t3 : gtree) Prop :=
  Gtree_empty4 : 
    (are_4_Gtree_empty Gtree_empty Gtree_empty Gtree_empty Gtree_empty).

Lemma gtree_empty4P : (t0, t1, t2, t3 : gtree)
  (reflect (are_4_Gtree_empty t0 t1 t2 t3)
           (gtree_empty4 (Gtree_node t0 t1 t2 t3))).
Proof.
Move=> t0 t1 t2 t3; Rewrite: /gtree_empty4 3!gtree_empty_and_spec.
Apply introP; LeftBy Move: t0 t1 t2 t3; Do 4 Case=> //.
By Move=> H H'; Case: H' H.
Qed.

(* The restriction operation returns a partition of a gram tree into a pair *)
(* of gram trees.                                                           *)

Inductive gtree_pair : Set :=
  Gtree_pair : (t0, t1 : gtree) gtree_pair.

Definition empty_gtree_pair : gtree_pair :=
  (Gtree_pair Gtree_empty Gtree_empty).

Definition gtree_pair_sub [pt : gtree_pair; b : bool] : gtree :=
  let (t0, t1) = pt in if b is false then t0 else t1.

Definition sgtree_partition [st, st', st'' : spec_gtree] : Prop :=
  (w : chromogram) (if (st w) then eqb else orb (st' w) (st'' w)) = false.
  
Definition gtree_pair_partition [t : gtree; pt : gtree_pair] : Prop :=
  let (t0, t1) = pt in
  (sgtree_partition (gtree_mem t) (gtree_mem t0) (gtree_mem t1)).

Lemma match_count_0 : (st : spec_gtree; Hst : (w : chromogram) ~(st w))
   (bs : bit_stack; et : colseq) (match_count st bs et) = (0).
Proof.
Move=> st Hst bs et; Move: st bs {Hst}[w](introF idP (Hst w)).
Elim: et => [|c et Hrec] st bs Hst; LeftBy Rewrite: /= Hst.
By Case c; Rewrite: /= ?Hrec //; Case: bs => *; Rewrite: /= ?Hrec.
Qed.

Lemma gtree_mem_empty : (w : chromogram)
  (gtree_mem Gtree_empty w) = false.
Proof. By Case. Qed.

Lemma gtree_sub_empty : (bs : bit_stack; et : colseq)
  (gtree_sub Gtree_empty bs et) = (0).
Proof. Exact (match_count_0 [w](elimF idP (gtree_mem_empty w))). Qed.

Lemma gtree_sub_node_0 : (bs : bit_stack; t0, t1, t2, t3 : gtree; et : colseq)
  (pred (size et)) = (0) -> (gtree_sub (Gtree_node t0 t1 t2 t3) bs et) = (0).
Proof.
Move=> bs t0 t1 t2 t3 [|e [|e' et]] // _; Rewrite: /gtree_sub /=.
Step Htf: (t : ?) (if t is Gtree_empty then false else false) = false By Case.
Rewrite: ~{Htf}(Htf t0) (Htf t1) (Htf t2) (Htf t3).
By Case: e => //; Trivial; Case: bs.
Qed.

Lemma match_count_eq : (st, st' : spec_gtree)
   (st =1 st') -> (match_count st) =2 (match_count st').
Proof.
Rewrite: /eqfun; Move=> st st' Est bs et; Elim: et st st' Est bs.
  By Move=> st st' Est; Rewrite: /= Est.
Move=> [|||] et Hrec st st' Est bs //=; Auto;
  Rewrite: -(Hrec [w](st' (Adds Gpush w))); Auto;
  Apply (!congr nat); Case: bs => /=; Auto.
Qed.

Lemma match_count_partition : (st, st', st'' : spec_gtree)
                            (Hw : (sgtree_partition st st' st''))
                            (bs : bit_stack; et : colseq)
  (match_count st bs et)
     = (addn (match_count st' bs et) (match_count st'' bs et)).
Proof.
Move=> st st' st'' Hw bs et; Elim: et st st' st'' Hw bs.
  Move=> st st' st'' Hw bs; Move: {Hw}(Hw seq0) => /=.
  By Case (st seq0); Case (st' seq0); Case (st'' seq0).
Rewrite: /sgtree_partition; Move=> [|||] et Hrec st st' st'' Hw bs /=; Auto;
  Symmetry; Rewrite: addnC addnCA -addnA addnA;
  (Rewrite: -(Hrec [w](st (Adds Gpush w)));  [Apply (!congr nat) | Auto]);
  Rewrite: addnC; Symmetry; Case: bs; Auto.
Qed.

Definition gtree_cons_pairs [t : gtree; pt0, pt1, pt2, pt3 : gtree_pair] :=
  let (t'0, t''0) = pt0 in let (t'1, t''1) = pt1 in
  let (t'2, t''2) = pt2 in let (t'3, t''3) = pt3 in
  (([t', t''] if (gtree_empty4 t') then (Gtree_pair t'0 t) else
   if (gtree_empty4 t'') then (Gtree_pair t t''0) else (Gtree_pair t' t''))
   (Gtree_node t'0 t'1 t'2 t'3) (Gtree_node t''0 t''1 t''2 t''3)).

Lemma gtree_cons_pairs_partition : (t0, t1, t2, t3 : gtree)
                                   (pt0, pt1, pt2, pt3 : gtree_pair)
  (Ht0 : (gtree_pair_partition t0 pt0); Ht1 : (gtree_pair_partition t1 pt1))
  (Ht2 : (gtree_pair_partition t2 pt2); Ht3 : (gtree_pair_partition t3 pt3))
  let t = (Gtree_node t0 t1 t2 t3) in
  let pt = (gtree_cons_pairs t pt0 pt1 pt2 pt3) in
  (gtree_pair_partition t pt).
Proof.
Move=> t0 t1 t2 t3 [t'0 t''0] [t'1 t''1] [t'2 t''2] [t'3 t''3].
Unfold gtree_cons_pairs.
Case: (gtree_empty4P t'0  t'1 t'2 t'3) => [[] | Hne'].
  Move=> /= *; Def: st := (gtree_mem (Gtree_node t0 t1 t2 t3)).
  By Intro w; Rewrite: gtree_mem_empty; Case (st w).
Case: (gtree_empty4P t''0  t''1 t''2 t''3) => [[] | Hne''].
  Move=> /= *; Def: st := (gtree_mem (Gtree_node t0 t1 t2 t3)).
  By Move=> w; Rewrite: gtree_mem_empty; Case (st w).
By Rewrite: /= /sgtree_partition; Move=> Ht0 Ht1 Ht2 Ht3 [|[|||] w] /=.
Qed.

Lemma gtree_mem0_cons_pairs : (t0, t1, t2, t3 : gtree)
                              (pt0, pt1, pt2, pt3 : gtree_pair)
  (Ht0 : (gtree_pair_partition t0 pt0); Ht1 : (gtree_pair_partition t1 pt1))
  (Ht2 : (gtree_pair_partition t2 pt2); Ht3 : (gtree_pair_partition t3 pt3))
  let sub0 = [pt](gtree_pair_sub pt false) in
  let t' = (Gtree_node (sub0 pt0) (sub0 pt1) (sub0 pt2) (sub0 pt3)) in
  let pt' = (gtree_cons_pairs (Gtree_node t0 t1 t2 t3) pt0 pt1 pt2 pt3) in
  (w : chromogram) (gtree_mem (sub0 pt') w) = (gtree_mem t' w).
Proof.
Move=> t0 t1 t2 t3 [t'0 t''0] [t'1 t''1] [t'2 t''2] [t'3 t''3].
Rewrite: /gtree_cons_pairs.
Case: (gtree_empty4P t'0  t'1 t'2 t'3) => [[] | Hne'].
  By Move=> Ht0 Ht1 Ht2 Ht3 [|[|||] [|s w]].
Case: (gtree_empty4P t''0  t''1 t''2 t''3) => [[] | Hne''] //.
Move=> Ht0 Ht1 Ht2 Ht3 [|[|||] w] //=.
  Case: (gtree_mem t0 w) (gtree_mem t'0 w) (Ht0 w) => [|] [|]; Case w; Auto.
  Case: (gtree_mem t1 w) (gtree_mem t'1 w) (Ht1 w) => [|] [|]; Case w; Auto.
  Case: (gtree_mem t2 w) (gtree_mem t'2 w) (Ht2 w) => [|] [|]; Case w; Auto.
  Case: (gtree_mem t3 w) (gtree_mem t'3 w) (Ht3 w) => [|] [|]; Case w; Auto.
Qed.

Unset Implicit Arguments.
