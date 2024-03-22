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
Require ctree.

Set Implicit Arguments.

(* This is the second phase of a D-reducibility step : adjusting the       *)
(* coloring set match counts to fit the new set of chromograms, thereby    *)
(* removing the colorings whose counts fall to zero.                       *)
(* The restriction function uses a depth counter to determine when to      *)
(* decrement counts.                                                       *)

Section CtreeRestriction.

Inductive ctree_restriction : Set :=
  Ctr_none : ctree_restriction
| Ctr_some : (bs : bit_stack; t : gtree)
             ctree_restriction -> ctree_restriction.

Definition ctr_cons [bs : bit_stack; t : gtree; r : ctree_restriction]
                  : ctree_restriction :=
  if (gtree_empty t) then r else (Ctr_some bs t r).

Fixpoint ctr_sub [r : ctree_restriction] : colseq -> nat :=
  [et]if r is (Ctr_some bs t r') then
    (addn (gtree_sub t bs et) (ctr_sub r' et))
   else (0).

Lemma ctr_sub_cons : (bs : bit_stack; t : gtree; r : ctree_restriction)
                     (et : colseq)
  (ctr_sub (ctr_cons bs t r) et) = (addn (gtree_sub t bs et) (ctr_sub r et)).
Proof.
Move=> bs t r et; Rewrite: /ctr_cons; Case Ht: (gtree_empty t) => //=.
By Rewrite: (gtree_empty_empty Ht) gtree_sub_empty.
Qed.

Section CtrSplit.

Variables A : Set; continue : (r1, r2, r3 : ctree_restriction) A.

Fixpoint ctr_split [r1, r2, r3, r : ctree_restriction] : A :=
  Cases r of
    Ctr_none => (continue r1 r2 r3)
  | (Ctr_some bs (Gtree_node t0 t1 t2 t3) r') =>
      let addr = [bs;t;r'](if t is Gtree_empty then r' else (Ctr_some bs t r')) in
      let r1' = (addr bs t1 r1) in
      let dorec = [r2', r3']Cases t0 of
        Gtree_empty => (ctr_split (addr bs t1 r1) r2' r3' r')
      | _ => let r2'' = (Ctr_some (Bpush0 bs) t0 r2') in
             let r3'' = (Ctr_some (Bpush1 bs) t0 r3') in
             (ctr_split (addr bs t1 r1) r2'' r3'' r')
      end in
      Cases bs of
        Bstack0 => (dorec r2 r3)
      | (Bpush0 bs') => (dorec (addr bs' t2 r2) (addr bs' t3 r3))
      | (Bpush1 bs') => (dorec (addr bs' t3 r2) (addr bs' t2 r3))
      end
  | (Ctr_some _ _ r') => (ctr_split r1 r2 r3 r')
  end.

Lemma ctr_split_some : (bs : bit_stack; t0, t1, t2, t3 : gtree)
                       (r1, r2, r3, r : ctree_restriction)
  let cons_pop = [t,t';r']Cases bs of
      Bstack0 => r'
   | (Bpush0 bs') => (ctr_cons bs' t r')
   | (Bpush1 bs') => (ctr_cons bs' t' r')
   end in
  (ctr_split r1 r2 r3 (Ctr_some bs (Gtree_node t0 t1 t2 t3) r))
    = (ctr_split (ctr_cons bs t1 r1)
                 (ctr_cons (Bpush0 bs) t0 (cons_pop t2 t3 r2))
                 (ctr_cons (Bpush1 bs) t0 (cons_pop t3 t2 r3)) r).
Proof.
Move=> [|bs|bs] t0 t1 t2 t3 r1 r2 r3 r;
  By Rewrite: /= !fold_gtree_empty /ctr_cons; Case (gtree_empty t0).
Qed.

End CtrSplit.

Local csplit [r : ctree_restriction; e : color] : ctree_restriction :=
  (ctr_split [t1,t2,t3](!color_rec [_]?Ctr_none t1 t2 t3 e)
            Ctr_none Ctr_none Ctr_none r).

Lemma ctr_split_eq : (A : Set; rk : (r1, r2, r3 : ctree_restriction) A)
                     (r : ctree_restriction)
  (ctr_split rk Ctr_none Ctr_none Ctr_none r)
    = (rk (csplit r Color1) (csplit r Color2) (csplit r Color3)).
Proof.
Move=> A rk r; Rewrite: /csplit.
Move: {1 3 5 7}Ctr_none {2 5 8 11}Ctr_none {3 7 11 15}Ctr_none.
Elim: r => [|bs t r Hrec] r1 r2 r3 //.
By Case: t; First [Move=> t0 t1 t2 t3; Rewrite: !ctr_split_some Hrec | Simpl].
Qed.

Lemma ctr_sub_csplit : (r : ctree_restriction; e : color; et : colseq)
  (ctr_sub (csplit r e) et)
     = (if (size et) is (0) then (0) else (ctr_sub r (Adds e et))).
Proof.
Move=> r e et; Case Det: {2}et => [|e' et']; Simpl.
  Rewrite: ~{et}Det; Elim: {r e}(csplit r e) => //= [bs t r Hrec].
  By Rewrite: Hrec addn0; Case t.
Apply: (etrans ? (add0n ?)).
Step []: (ctr_sub (csplit Ctr_none e) et) = (0) By Case e.
Rewrite: /csplit /=; Move: {2 4}Ctr_none {3 6}Ctr_none {4 8}Ctr_none.
Elim: r => [|bs t r Hrec] r1 r2 r3; LeftBy Rewrite: /= addn0.
Step Htlf: (Ht : (s, s' : ?; w : ?) ~(gtree_mem t (Adds s (Adds s' w))))
    (gtree_sub t bs (Adds e et)) = (0).
  Move{Hrec}=> Ht; Rewrite: ~Det /gtree_sub; Move: (gtree_mem t) Ht => st Hst.
  Case: e => //; Case: e' => //=;
    Do 3 (Rewrite: ?match_count_0 //; Case: bs => [|bs|bs] //=).
Case: t Htlf; First [
  Move=> t0 t1 t2 t3 _; Rewrite: ctr_split_some ~Hrec
| By Move=> Htlf; Rewrite: /= ~Hrec ~Htlf //; Case].
Rewrite: /= addnA -2!(addnC (ctr_sub r (Adds e et))); Congr addn; Rewrite addnC.
Def: Hmceta := [t](match_count_eq 1![w](gtree_mem t w) (frefl (gtree_mem t))).
By Case: e; Rewrite: //= ctr_sub_cons; First [
  By Rewrite: /gtree_sub /= Hmceta
| Case: bs => *; Rewrite: ?ctr_sub_cons /gtree_sub /=;
  Rewrite: !Hmceta ?addnI ?addnA ?addn0].
Qed.

Fixpoint ctree_decr [lf : ctree; n : nat] : ctree :=
  Cases n lf of (S n') (Ctree_leaf lf') => (ctree_decr lf' n') | _ _ => lf end.

Lemma ctree_val_decr : (m, n : nat)
  (ctree_decr (ctree_leaf_of m) n) = (ctree_leaf_of (subn m n)).
Proof. By Move=> m n; Elim: n m => [|n Hrec] [|m]; Try Exact (Hrec m). Qed.

Lemma ctree_no_decr : (t : ctree; n : nat)
  (ctree_leaf t) = false -> (ctree_decr t n) = t.
Proof. By Move=> [t1 t2 t3|lf|] [|n]. Qed.

Section CtrDecr.

Variables A : Set; cont : (lf1, lf2, lf3 : ctree) A.

Local dlf [lf : ctree; klf : ctree -> A] : A :=
  if lf is (Ctree_leaf lf') then (klf lf') else (klf lf).

Definition ctr_decr := Eval Compute in Fix ctr_decr {
  ctr_decr [lf1, lf2, lf3 : ctree; r : ctree_restriction] : A :=
  Cases r of
    Ctr_none =>
    (cont lf1 lf2 lf3)
  | (Ctr_some bs t r') =>
    let dlf1 = (dlf lf1) in let dlf2 = (dlf lf2) in let dlf3 = (dlf lf3) in
    let lfk = [lf1', lf2', lf3'](ctr_decr lf1' lf2' lf3' r') in
    Cases t bs of
      Gtree_leaf0 _ => (dlf2 [lf2'](dlf3 [lf3'](lfk lf1 lf2' lf3')))
    | Gtree_leaf1 _ => (dlf1 [lf1'](lfk lf1' lf2 lf3))
    | Gtree_leaf2 (Bpush0 _) => (dlf2 [lf2'](lfk lf1 lf2' lf3))
    | Gtree_leaf2 (Bpush1 _) => (dlf3 [lf3'](lfk lf1 lf2 lf3'))
    | Gtree_leaf3 (Bpush0 _) => (dlf3 [lf3'](lfk lf1 lf2 lf3'))
    | Gtree_leaf3 (Bpush1 _) => (dlf2 [lf2'](lfk lf1 lf2' lf3))
    | Gtree_leaf01 _ => (dlf1 [lf1'](dlf2 [lf2'](dlf3 (lfk lf1' lf2'))))
    | Gtree_leaf12 Bstack0 => (dlf1 [lf1'](lfk lf1' lf2 lf3))
    | Gtree_leaf12 (Bpush0 _) => (dlf1 [lf1'](dlf2 [lf2'](lfk lf1' lf2' lf3)))
    | Gtree_leaf12 (Bpush1 _) => (dlf1 [lf1'](dlf3 [lf3'](lfk lf1' lf2 lf3')))
    | Gtree_leaf13 Bstack0 => (dlf1 [lf1'](lfk lf1' lf2 lf3))
    | Gtree_leaf13 (Bpush0 _) => (dlf1 [lf1'](dlf3 [lf3'](lfk lf1' lf2 lf3')))
    | Gtree_leaf13 (Bpush1 _) => (dlf1 [lf1'](dlf2 [lf2'](lfk lf1' lf2' lf3)))
    | Gtree_leaf23 (Bpush0 _) => (dlf2 [lf2'](dlf3 [lf3'](lfk lf1 lf2' lf3')))
    | Gtree_leaf23 (Bpush1 _) => (dlf2 [lf2'](dlf3 [lf3'](lfk lf1 lf2' lf3')))
    | _ _ => (lfk lf1 lf2 lf3)
    end
  end}.

Definition ctr_e_decr [bs : bit_stack; t : gtree; e : color]
                    : ctree -> ctree :=
  [lf](ctree_decr lf (gtree_sub t bs (seq1 e))).

Lemma ctr_decr_some : (lf1, lf2, lf3 : ctree)
                      (bs : bit_stack; t : gtree; r : ctree_restriction)
  let cde = (ctr_e_decr bs t) in
  (ctr_decr lf1 lf2 lf3 (Ctr_some bs t r))
    = (ctr_decr (cde Color1 lf1) (cde Color2 lf2) (cde Color3 lf3) r).
Proof.
Move=> lf1 lf2 lf3 bs t r; Case: t; By First [
  Move=> t0 t1 t2 t3; Rewrite: /ctr_e_decr !gtree_sub_node_0
| Case: lf1 => //; Case: bs => // *; Case: lf2; Case: lf3].
Qed.

End CtrDecr.

Local cdecr [e : color]
    : (lf1, lf2, lf3 : ctree) ctree_restriction -> ctree :=
  (ctr_decr [ct1,ct2,ct3](!color_rec [_]? Ctree_empty ct1 ct2 ct3 e)).

Lemma ctr_decr_eq : (A : Set; lfk : (lf1, lf2, lf3 : ctree) A)
                    (lf1, lf2, lf3 : ctree; r : ctree_restriction)
  let cdecr_r = [e](cdecr e lf1 lf2 lf3 r) in
  (ctr_decr lfk lf1 lf2 lf3 r)
    = (lfk (cdecr_r Color1) (cdecr_r Color2) (cdecr_r Color3)).
Proof.
Move=> A lfk lf1 lf2 lf3 r; Elim: r lf1 lf2 lf3; Rewrite: // /cdecr.
By Move=> bs t r Hrec *; Rewrite: !ctr_decr_some Hrec.
Qed.

Lemma ctree_proper_leaf_of_val : (lf : ctree)
  (ctree_proper (0) lf) -> lf = (ctree_leaf_of (ctree_sub lf seq0)).
Proof. By Elim=> // [lf Hrec] Hlf; Exact (congr Ctree_leaf (Hrec Hlf)). Qed.

Lemma cdecr_leaf : (e : color; lf1, lf2, lf3 : ctree; r : ctree_restriction)
  let t = (ctree_cons lf1 lf2 lf3) in let et = (seq1 e) in
  (Ht : (ctree_proper (1) t))
  (cdecr e lf1 lf2 lf3 r)
    = (ctree_leaf_of (subn (ctree_sub t et) (ctr_sub r et))).
Proof.
Move=> e lf1 lf2 lf3 r; Move.
Elim: r lf1 lf2 lf3 => [|bs t r Hrec] lf1 lf2 lf3 Ht;
 Move: {Ht} [c](ctree_proper_leaf_of_val (ctree_proper_sel c Ht)) => Hlf.
  By Rewrite: /= subn0 ctree_sub_cons; Case: e (Hlf e); Rewrite ctree_sel_cons.
Rewrite: /cdecr !ctr_decr_some -/(cdecr e) ~Hrec.
  Simpl; Congr ctree_leaf_of; Move: {Hlf}(Hlf e).
  Def: m := (ctree_sub (ctree_sel (ctree_cons lf1 lf2 lf3) e) seq0).
  Rewrite: ctree_sel_cons 2!ctree_sub_cons.
  Case: e => //= [] Dlf;
    By Rewrite: /ctr_e_decr Dlf ctree_val_decr !ctree_sub_leaf_of -subn_sub.
Apply ctree_cons_proper;
 [Move: (Hlf Color1) | Move: (Hlf Color2) | Move: (Hlf Color3)];
 Rewrite: ctree_sel_cons /=; Move=> Dlf;
 Rewrite: /ctr_e_decr Dlf ctree_val_decr; Apply ctree_leaf_of_proper.
Qed.

Definition ctree_cons_pairs [pt1, pt2, pt3 : ctree_pair] : ctree_pair :=
  let (t1, t1') = pt1 in let (t2, t2') = pt2 in let (t3, t3') = pt3 in
  (([t, t']Cases (ctree_empty_node t) (ctree_empty_node t') of
     true  true  => (Ctree_pair Ctree_empty Ctree_empty)
   | true  false => (Ctree_pair Ctree_empty t')
   | false true  => (Ctree_pair t  Ctree_empty)
   | false false => (Ctree_pair t  t')
   end) (Ctree_node t1 t2 t3) (Ctree_node t1' t2' t3')).

Lemma ctree_cons_pairs_spec : (t1, t1', t2, t2', t3, t3' : ctree)
  let Cp = Ctree_pair in
  (ctree_cons_pairs (Cp t1 t1') (Cp t2 t2') (Cp t3 t3'))
    = (Cp (ctree_cons t1 t2 t3) (ctree_cons t1' t2' t3')).
Proof.
Move=> t1 t1' t2 t2' t3 t3'; Rewrite: 2!ctree_cons_spec /=.
By Do 2 (Apply cases_of_if; Move=> Ee; Rewrite: ~Ee).
Qed.

Definition sctree_partition [st, st', st'' : colseq -> bool] : Prop :=
  (et : colseq)(if (st et) then eqb else orb (st' et) (st'' et)) = false.

Definition ctree_partition [t : ctree; pt : ctree_pair] : Prop :=
  let (t', t'') = pt in
  (sctree_partition (ctree_mem t) (ctree_mem t') (ctree_mem t'')).

Lemma ctree_cons_pairs_partition : (t1, t2, t3 : ctree)
                                   (pt1, pt2, pt3 : ctree_pair)
  (Ht1 : (ctree_partition t1 pt1))
  (Ht2 : (ctree_partition t2 pt2))
  (Ht3 : (ctree_partition t3 pt3))
  (ctree_partition (Ctree_node t1 t2 t3) (ctree_cons_pairs pt1 pt2 pt3)).
Proof.
Move=> t1 t2 t3 [t1' t1''] [t2' t2''] [t3' t3''].
Rewrite: ctree_cons_pairs_spec /= /ctree_mem; Move=> Ht1 Ht2 Ht3 et.
By Rewrite: 2!ctree_sub_cons; Case: et => [|[|||] et]; Simpl.
Qed.

Lemma ctree_sub0_cons_pairs : (pt1, pt2, pt3 : ctree_pair; et : colseq)
  let cp0 = [pt](ctree_pair_sub pt false) in
  (ctree_sub (cp0 (ctree_cons_pairs pt1 pt2 pt3)) et)
    = (ctree_sub (Ctree_node (cp0 pt1) (cp0 pt2) (cp0 pt3)) et).
Proof.
Move=> [t1 t1'] [t2 t2'] [t3 t3'] et.
By Rewrite: ctree_cons_pairs_spec /= ctree_sub_cons; Case et.
Qed.

Definition ctree_leaf_pair [lf1, lf2, lf3, lf1', lf2', lf3' : ctree]
                         : ctree_pair :=
  (([lf']Cases lf' of
    (Ctree_node Ctree_empty Ctree_empty Ctree_empty) =>
       (Ctree_pair lf1' (ctree_cons lf1 lf2 lf3))
  | (Ctree_node Ctree_empty Ctree_empty _) =>
       (Ctree_pair lf' (ctree_cons lf1 lf2 lf1'))
  | (Ctree_node Ctree_empty _ Ctree_empty) =>
       (Ctree_pair lf' (ctree_cons lf1 lf1' lf3))
  | (Ctree_node Ctree_empty _ _) =>
       (Ctree_pair lf' (ctree_cons lf1 lf1' lf1'))
  | (Ctree_node _ Ctree_empty Ctree_empty) =>
       (Ctree_pair lf' (ctree_cons lf2' lf2 lf3))
  | (Ctree_node _ Ctree_empty _) =>
       (Ctree_pair lf' (ctree_cons lf2' lf2 lf2'))
  | (Ctree_node _ _ Ctree_empty) =>
       (Ctree_pair lf' (ctree_cons lf3' lf3' lf3))
  | _ => 
       (Ctree_pair lf' Ctree_empty)
  end)
  (Ctree_node lf1' lf2' lf3')).

Lemma ctree_leaf_pair_spec : (lf1, lf2, lf3, lf1', lf2', lf3' : ctree)
  let if_e = [lf,lf']if (ctree_empty lf') then lf else Ctree_empty in
  let t' = (ctree_cons lf1' lf2' lf3') in
  let t'' = (ctree_cons (if_e lf1 lf1') (if_e lf2 lf2') (if_e lf3 lf3')) in
  (ctree_leaf_pair lf1 lf2 lf3 lf1' lf2' lf3') = (Ctree_pair t' t'').
Proof.
By Move=> lf1 lf2 lf3 lf1' lf2' lf3'; Case lf1'; Case lf2'; Case lf3'.
Qed.

Fixpoint ctree_restrict [h : nat] : ctree -> ctree_restriction -> ctree_pair :=
  [t; r]Cases r h t of
    Ctr_none _ _ => (Ctree_pair t Ctree_empty)
  | _ (S h') (Ctree_node t1 t2 t3) =>
      let rh' = (ctree_restrict h') in
      let rk =
        [r1,r2,r3](ctree_cons_pairs (rh' t1 r1) (rh' t2 r2) (rh' t3 r3)) in
      (ctr_split rk Ctr_none Ctr_none Ctr_none r)
  | _ (0) (Ctree_node lf1 lf2 lf3) =>
      (ctr_decr (ctree_leaf_pair lf1 lf2 lf3) lf1 lf2 lf3 r)
  | _ _ _ => ctree_empty_pair
  end.

Lemma ctree_restrict_correct : (h : nat; t : ctree; r : ctree_restriction)
  (Ht : (ctree_proper (S h) t))
  let pt = (ctree_restrict h t r) in
     ((b : bool) (ctree_proper (S h) (ctree_pair_sub pt b)))
  /\ (ctree_partition t pt)
  /\ ((et : colseq)
      (ctree_sub (ctree_pair_sub pt false) et)
         = (subn (ctree_sub t et) (ctr_sub r et))).
Proof.
Elim=> [|h' Hrec].
  Move=> t r Ht; Def Dpt: pt := (ctree_restrict (0) t r).
  Case Dt: t Ht Dpt => [lf1 lf2 lf3|lf|] Ht //.
    Case Dr: r => [|bs gt r']; [Simpl | Rewrite: /ctree_restrict -~{bs gt r'}Dr].
      Move=> Dpt; Rewrite: ~Dpt; Repeat Split.
          By Case.
        By Intro et; Rewrite: -Dt /=; Case (ctree_mem t et).
      Move=> et; Exact (esym (subn0 ?)).
    Rewrite: ctr_decr_eq ctree_leaf_pair_spec.
    Def: Dlf := [e](ctree_proper_leaf_of_val (ctree_proper_sel e Ht)).
    Def: Et := (ctree_cons_spec lf1 lf2 lf3); Case: {}Ht => [Htne _ _ _].
    Rewrite: ~Htne /= in Et; Rewrite: -Et in Ht.
    Rewrite: ![e](cdecr_leaf e r Ht) !ctree_sub_cons /=.
    Move: {Dlf} (Dlf Color1) (Dlf Color2) (Dlf Color3) => /=.
    Def: n1 := (ctree_sub lf1 seq0); Def: n2 := (ctree_sub lf2 seq0).
    Def: n3 := (ctree_sub lf3 seq0); Move=> Dlf1 Dlf2 Dlf3.
    Move=> Dpt; Rewrite: ~{pt}Dpt; Split.
      Case=> /=; RightBy Apply ctree_cons_proper; Apply ctree_leaf_of_proper.
      Step Hife: (b : bool; n : nat)
          (ctree_proper (0) if b then (ctree_leaf_of n) else Ctree_empty).
        By Case; LeftBy Exact ctree_leaf_of_proper.
      Rewrite: Dlf1 Dlf2 Dlf3; Apply ctree_cons_proper; Apply Hife.
    Split; Move=> et.
      Rewrite: !ctree_mem_cons /= /ctree_mem.
      Case: et => [|[|||] et] //=.
        Rewrite: ~Dlf1; Case: n1 => [|n1] //.
          Def: m1 := (subn (S n1) (ctr_sub r (seq1 Color1))).
          By Rewrite: 2!ctree_sub_leaf_of; Case: et; Case: m1.
        Rewrite: ~Dlf2; Case: n2 => [|n2] //.
          Def: m2 := (subn (S n2) (ctr_sub r (seq1 Color2))).
          By Rewrite: 2!ctree_sub_leaf_of; Case: et; Case: m2.
        Rewrite: ~Dlf3; Case: n3 => [|n3] //.
          Def: m3 := (subn (S n3) (ctr_sub r (seq1 Color3))).
          By Rewrite: 2!ctree_sub_leaf_of; Case: et; Case: m3.
    Rewrite: /= ctree_sub_cons /=; Case: et => [|[|||] et] //=;
      By Rewrite: ?Dlf1 ?Dlf2 ?Dlf3 !ctree_sub_leaf_of; Case et.
  Move=> Dpt; Step Ept: pt = ctree_empty_pair By Case: r Dpt.
  By Rewrite: Ept /=; Split; [Case | Split].
Move=> [t1 t2 t3|lf|] r Ht //.
  Move Dpt: (ctree_restrict (S h') (Ctree_node t1 t2 t3) r) => /= pt.
  Case Dr: r Dpt => [|bs gt r']; [Simpl | Rewrite: -~{bs gt r'}Dr].
    Case {pt}; Split; LeftBy Case.
    Split; Move=> et; LeftBy Case (ctree_mem (Ctree_node t1 t2 t3) et).
    Exact (esym (subn0 ?)).
  Rewrite ctr_split_eq.
  Def: Hrece := [e](Hrec ? (csplit r e) (ctree_proper_sel e Ht)).
  Move: {Hrec Hrece} (Hrece Color1) (Hrece Color2) (Hrece Color3) => /=.
  Case: (ctree_restrict h' t1 (csplit r Color1)) => [t1' t1''].
  Case: (ctree_restrict h' t2 (csplit r Color2)) => [t2' t2''].
  Case: (ctree_restrict h' t3 (csplit r Color3)) => [t3' t3''].
  Move=> [Hpt1 [Ht1' Et1']] [Hpt2 [Ht2' Et2']] [Hpt3 [Ht3' Et3']] [] {pt}; Split.
    Rewrite ctree_cons_pairs_spec; Move=> b0.
    By Case: b0 (Hpt1 b0) (Hpt2 b0) (Hpt3 b0) (ctree_cons_proper) => /=; Auto.
  Clear Hpt1 Hpt2 Hpt3; Split; LeftBy Apply ctree_cons_pairs_partition.
  Clear Ht1' Ht2' Ht3'; Move=> et; Rewrite ctree_sub0_cons_pairs.
  Case: et => [|e et] //=; Move: {Et1' Et2' Et3'}(Et1' et) (Et2' et) (Et3' et).
  Rewrite: !ctr_sub_csplit /=; Case: et => [|e' et'] /= Et1' Et2' Et3';
    Case: e {Ht}(ctree_proper_sel e Ht) => //=.
    By Rewrite Et1'; Case t1.
    By Rewrite Et2'; Case t2.
    By Rewrite Et3'; Case t3.
Step []: ctree_empty_pair = (ctree_restrict (S h') Ctree_empty r) By Case r.
Split; [Case | Split]; Split.
Qed.

End CtreeRestriction.

Unset Implicit Arguments.
