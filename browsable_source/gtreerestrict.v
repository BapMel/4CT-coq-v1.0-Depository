(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require tacticext.
Require boolprop.
Require funs.
Require dataset.
Require natprop.
Require seq.
Require color.
Require ctree.
Require chromogram.
Require gtree.

Set Implicit Arguments.

(* This is the first phase of a D-reducibility step : restricting the      *)
(* chromogram set to fit a given set of colorings. The result of this step *)
(* is a pair of trees, containing respectively the deleted and remaining   *)
(* chromograms.                                                            *)
(*   To keep the two versions straight it is desireable to iterate at most *)
(* once over each subtree; since a chromogram can be matched in several    *)
(* ways, this means that the recursive procedure must restrict with a LIST *)
(* of trees (that list has at most 32 trees in it, and not more than 8     *)
(* for the most part); this is the type gtree_restrictor given below.      *)

Section GtreeRestrict.

Inductive gtree_restriction : Set :=
  Gtr_none : gtree_restriction
| Gtr_some : (bs : bit_stack; t : ctree)
             gtree_restriction -> gtree_restriction.

(* A restriction set ``represents'' a set of matching chromograms *)


Fixpoint gtr_mem [r : gtree_restriction] : chromogram -> bool :=
  [w]if r is (Gtr_some bs t r') then
     (orb (has_match bs (ctree_mem t) w) (gtr_mem r' w))
  else false.

Definition gtr_cons [bs : bit_stack; t : ctree; r : gtree_restriction]
                  : gtree_restriction :=
  if (ctree_empty t) then r else (Gtr_some bs t r).

Lemma gtr_mem_cons : (bs : bit_stack; t : ctree; r : gtree_restriction)
                     (w : chromogram)
  (gtr_mem (gtr_cons bs t r) w)
     = (orb (has_match bs (ctree_mem t) w) (gtr_mem r w)).
Proof.
Move=> bs t r w; Rewrite: /gtr_cons; Case Ht: (ctree_empty t) => //.
By Rewrite: (ctree_empty_eq Ht) /= [P](introF (has_matchP bs P w)) //; Case.
Qed.

Section GtrSplit.

Variable A : Set; continue : (r0, r1, r2, r3 : gtree_restriction) A.

Fixpoint gtr_split [r0, r1, r2, r3, r : gtree_restriction] : A :=
  Cases r of
    Gtr_none =>
      (continue r0 r1 r2 r3)
  | (Gtr_some bs (Ctree_node t1 t2 t3) r') =>
      let r02 = (Gtr_some (Bpush0 bs) t2 r0) in
      let r03 = (Gtr_some (Bpush1 bs) t3 r0) in
      let r023 = (Gtr_some (Bpush0 bs) t2 r03) in
      let r1' = Cases t1 of Ctree_empty => r1 | _ => (Gtr_some bs t1 r1) end in
      let r2' = [bs';t'](Gtr_some bs' t' r2) in
      let r3' = [bs';t'](Gtr_some bs' t' r3) in
      Cases t2 t3 bs of
        Ctree_empty Ctree_empty _ => (gtr_split r0 r1' r2 r3 r')
      | Ctree_empty _ Bstack0 =>    (gtr_split r03 r1' r2 r3 r')
      | Ctree_empty _ (Bpush0 bs') => (gtr_split r03 r1' r2 (r3' bs' t3) r')
      | Ctree_empty _ (Bpush1 bs') => (gtr_split r03 r1' (r2' bs' t3) r3 r')
      | _ Ctree_empty Bstack0 =>    (gtr_split r02 r1' r2 r3 r')
      | _ Ctree_empty (Bpush0 bs') => (gtr_split r02 r1' (r2' bs' t2) r3 r')
      | _ Ctree_empty (Bpush1 bs') => (gtr_split r02 r1' r2 (r3' bs' t2) r')
      | _ _ Bstack0 =>    (gtr_split r023 r1' r2 r3 r')
      | _ _ (Bpush0 bs') => (gtr_split r023 r1' (r2' bs' t2) (r3' bs' t3) r')
      | _ _ (Bpush1 bs') => (gtr_split r023 r1' (r2' bs' t3) (r3' bs' t2) r')
      end
  | (Gtr_some _ _ r') =>
      (gtr_split r0 r1 r2 r3 r')
  end.

Lemma gtr_split_some : (bs : bit_stack; t1, t2, t3 : ctree)
                       (r0, r1, r2, r3, r : gtree_restriction)
 let cons_pop = [t, t'; r']Cases bs of
                  Bstack0 => r'
                | (Bpush0 bs') => (gtr_cons bs' t r')
                | (Bpush1 bs') => (gtr_cons bs' t' r')
                end in
 (gtr_split r0 r1 r2 r3 (Gtr_some bs (Ctree_node t1 t2 t3) r))
   = (gtr_split (gtr_cons (Bpush0 bs) t2 (gtr_cons (Bpush1 bs) t3 r0))
                (gtr_cons bs t1 r1) (cons_pop t2 t3 r2) (cons_pop t3 t2 r3) r).
Proof.
Move=> bs t1 t2 t3 r0 r1 r2 r3 r; Rewrite: /= !fold_ctree_empty.
Case: bs =>[|bs|bs]; Rewrite: ?fold_ctree_empty /gtr_cons;
  By Case: (ctree_empty t2); Case: (ctree_empty t3).
Qed.

End GtrSplit.

Local gsplit [r : gtree_restriction; s : gram_symbol] : gtree_restriction :=
  (gtr_split [gt0,gt1,gt2,gt3](!gram_symbol_rec [_]? gt0 gt1 gt2 gt3 s)
             Gtr_none Gtr_none Gtr_none Gtr_none r).

Lemma gtr_split_eq : (A : Set; rk : (r0, r1, r2, r3 : gtree_restriction) A;
                      r : gtree_restriction)
  (gtr_split rk Gtr_none Gtr_none Gtr_none Gtr_none r) =
    (rk (gsplit r Gpush) (gsplit r Gskip) (gsplit r Gpop0) (gsplit r Gpop1)).
Proof.
Move=> A rk r; Rewrite: /gsplit; Def: rn := Gtr_none.
Elim: r rn {2 4 6 8 10}rn {3 6 9 12 15}rn {4 8 12 16 20}rn => //.
Move=> bs [t1 t2 t3|lf|] r Hrec *; Rewrite: ?gtr_split_some; Apply: Hrec.
Qed.

Lemma gtr_mem_gsplit : (r : gtree_restriction; s : gram_symbol; w : chromogram)
  (gtr_mem r (Adds s w)) = (gtr_mem (gsplit r s) w).
Proof.
Move=> r s w; Rewrite: /gsplit; Def Drn: rn := Gtr_none.
Apply: (etrans (esym (orFb ?)) ?).
Step [ ]: (gtr_mem (!gram_symbol_rec [_]? rn rn rn rn s) w) = false.
  By Rewrite Drn; Case s.
Elim: r rn {2 4}rn {3 6}rn {4 8}rn {Drn}; LeftBy Move=> *; Rewrite: /= orbF.
Move=> bs [t1 t2 t3|lf|] r Hrec r0 r1 r2 r3.
    Rewrite: gtr_split_some -~Hrec; Case: s;
    Rewrite: /= ?gtr_mem_cons orbA {-2 -3 orb}lock orbC -?orbA -!lock //;
    By Case: bs => *; Rewrite: ?gtr_mem_cons.
  Rewrite: {(Adds s)}lock /= -lock.
  Rewrite [P;w'](introF (has_matchP bs P w')); LeftBy Simpl; Apply Hrec.
  By Do 2 Case.
Def Dsw: sw := (Adds s w); Rewrite: /= [P](introF (has_matchP bs P sw)) Dsw //.
By Do 2 Case.
Qed.

Fixpoint gtr_match0 [r : gtree_restriction] : bool :=
  Cases r of
    Gtr_none => false
  | (Gtr_some _ (Ctree_node _ (Ctree_leaf _) _) _) => true
  | (Gtr_some _ (Ctree_node _ _ (Ctree_leaf _)) _) => true
  | (Gtr_some _ _ r') => (gtr_match0 r')
  end.

Lemma gtr_match0_spec : (r : gtree_restriction)
  (gtr_match0 r) = (gtr_mem r (seq1 Gpush)).
Proof.
Simpl; Elim=> [|bs t r Hrec] //=.
By Case: t => //= [t1 t2 t3]; Rewrite: -~Hrec; Case: t2 => //; Case: t3.
Qed.

Fixpoint gtr_match1 [r : gtree_restriction] : bool :=
  Cases r of
    Gtr_none => false
  | (Gtr_some _ (Ctree_node (Ctree_leaf _) _ _) _) => true
  | (Gtr_some _ _ r') => (gtr_match1 r')
  end.

Lemma gtr_match1_spec : (r : gtree_restriction)
  (gtr_match1 r) = (gtr_mem r (seq1 Gskip)).
Proof.
Simpl; Elim=> [|bs t r Hrec] //=.
By Case: t => //= [t1 t2 t3]; Rewrite: -~Hrec; Case: t1.
Qed.

Fixpoint gtr_match2 [r : gtree_restriction] : bool :=
  Cases r of
    Gtr_none => false
  | (Gtr_some (Bpush0 _) (Ctree_node _ (Ctree_leaf _) _) _) => true
  | (Gtr_some (Bpush1 _) (Ctree_node _ _ (Ctree_leaf _)) _) => true
  | (Gtr_some _ _ r') => (gtr_match2 r')
  end.

Lemma gtr_match2_spec : (r : gtree_restriction)
  (gtr_match2 r) = (gtr_mem r (seq1 Gpop0)).
Proof.
Simpl; Elim=> [|bs t r Hrec] //=.
By Case: t => /=; Case: bs => [|bs|bs] // t1 t2 t3;
  Rewrite: -~Hrec; [Case: t2 | Case: t3].
Qed.

Fixpoint gtr_match3 [r : gtree_restriction] : bool :=
  Cases r of
    Gtr_none => false
  | (Gtr_some (Bpush0 _) (Ctree_node _ _ (Ctree_leaf _)) _) => true
  | (Gtr_some (Bpush1 _) (Ctree_node _ (Ctree_leaf _) _) _) => true
  | (Gtr_some _ _ r') => (gtr_match3 r')
  end.

Lemma gtr_match3_spec : (r : gtree_restriction)
  (gtr_match3 r) = (gtr_mem r (seq1 Gpop1)).
Proof.
Simpl; Elim=> [|bs t r Hrec] //=.
By Case: t => /=; Case: bs => [|bs|bs] // t1 t2 t3;
  Rewrite: -~Hrec; [Case t3 | Case t2].
Qed.

Definition gtp_0_e : gtree_pair := (Gtree_pair Gtree_leaf0 Gtree_empty).
Definition gtp_1_e : gtree_pair := (Gtree_pair Gtree_leaf1 Gtree_empty).
Definition gtp_2_e : gtree_pair := (Gtree_pair Gtree_leaf2 Gtree_empty).
Definition gtp_3_e : gtree_pair := (Gtree_pair Gtree_leaf3 Gtree_empty).
Definition gtp_01_e : gtree_pair := (Gtree_pair Gtree_leaf01 Gtree_empty).
Definition gtp_12_e : gtree_pair := (Gtree_pair Gtree_leaf12 Gtree_empty).
Definition gtp_13_e : gtree_pair := (Gtree_pair Gtree_leaf13 Gtree_empty).
Definition gtp_23_e : gtree_pair := (Gtree_pair Gtree_leaf23 Gtree_empty).

Definition gtp_e_0 : gtree_pair := (Gtree_pair Gtree_empty Gtree_leaf0).
Definition gtp_e_1 : gtree_pair := (Gtree_pair Gtree_empty Gtree_leaf1).
Definition gtp_e_2 : gtree_pair := (Gtree_pair Gtree_empty Gtree_leaf2).
Definition gtp_e_3 : gtree_pair := (Gtree_pair Gtree_empty Gtree_leaf3).
Definition gtp_e_01 : gtree_pair := (Gtree_pair Gtree_empty Gtree_leaf01).
Definition gtp_e_12 : gtree_pair := (Gtree_pair Gtree_empty Gtree_leaf12).
Definition gtp_e_13 : gtree_pair := (Gtree_pair Gtree_empty Gtree_leaf13).
Definition gtp_e_23 : gtree_pair := (Gtree_pair Gtree_empty Gtree_leaf23).

Definition gtp_0_1 : gtree_pair := (Gtree_pair Gtree_leaf0 Gtree_leaf1).
Definition gtp_1_0 : gtree_pair := (Gtree_pair Gtree_leaf1 Gtree_leaf0).
Definition gtp_1_2 : gtree_pair := (Gtree_pair Gtree_leaf1 Gtree_leaf2).
Definition gtp_2_1 : gtree_pair := (Gtree_pair Gtree_leaf2 Gtree_leaf1).
Definition gtp_1_3 : gtree_pair := (Gtree_pair Gtree_leaf1 Gtree_leaf3).
Definition gtp_3_1 : gtree_pair := (Gtree_pair Gtree_leaf3 Gtree_leaf1).
Definition gtp_2_3 : gtree_pair := (Gtree_pair Gtree_leaf2 Gtree_leaf3).
Definition gtp_3_2 : gtree_pair := (Gtree_pair Gtree_leaf3 Gtree_leaf2).

Lemma gtree_partition_left : (t : gtree)
  (gtree_pair_partition t (Gtree_pair t Gtree_empty)).
Proof. By Move=> t w; Rewrite gtree_mem_empty; Case (gtree_mem t w). Qed.

Lemma gtree_partition_right : (t : gtree)
  (gtree_pair_partition t (Gtree_pair Gtree_empty t)).
Proof. By Move=> t w; Rewrite gtree_mem_empty; Case (gtree_mem t w). Qed.

Fixpoint gtree_restrict [t : gtree] : gtree_restriction -> gtree_pair :=
  [r]Cases r t of
    Gtr_none  _ =>
      (Gtree_pair Gtree_empty t)
  | _ (Gtree_node t0 t1 t2 t3) =>
       let cont = [r0,r1,r2,r3]
         (gtree_cons_pairs t (gtree_restrict t0 r0) (gtree_restrict t1 r1)
                           (gtree_restrict t2 r2) (gtree_restrict t3 r3)) in
       (gtr_split cont Gtr_none Gtr_none Gtr_none Gtr_none r)
  | _ Gtree_leaf0  => if (gtr_match0 r) then gtp_0_e else gtp_e_0
  | _ Gtree_leaf1  => if (gtr_match1 r) then gtp_1_e else gtp_e_1
  | _ Gtree_leaf2  => if (gtr_match2 r) then gtp_2_e else gtp_e_2
  | _ Gtree_leaf3  => if (gtr_match3 r) then gtp_3_e else gtp_e_3
  | _ Gtree_leaf01 => if (gtr_match0 r)
                        then if (gtr_match1 r) then gtp_01_e else gtp_0_1
                        else if (gtr_match1 r) then gtp_1_0 else gtp_e_01
  | _ Gtree_leaf12 => if (gtr_match1 r)
                        then if (gtr_match2 r) then gtp_12_e else gtp_1_2
                        else if (gtr_match2 r) then gtp_2_1 else gtp_e_12
  | _ Gtree_leaf13 => if (gtr_match1 r)
                        then if (gtr_match3 r) then gtp_13_e else gtp_1_3
                        else if (gtr_match3 r) then gtp_3_1 else gtp_e_13
  | _ Gtree_leaf23 => if (gtr_match2 r)
                        then if (gtr_match3 r) then gtp_23_e else gtp_2_3
                        else if (gtr_match3 r) then gtp_3_2 else gtp_e_23
  | _ Gtree_empty => empty_gtree_pair
  end.

Local gtpl := gtree_partition_left.
Local gtpr := gtree_partition_right.

Theorem gtree_restrict_partition : (t : gtree; r : gtree_restriction)
  (gtree_pair_partition t (gtree_restrict t r)).
Proof.
Move=> t r; Elim: t r => [t0 Hrec0 t1 Hrec1 t2 Hrec2 t3 Hrec3|||||||||] r /=;
  Simpl; Case Dr: r => [|bs ct r']; Try Apply: gtpr; Rewrite: -~{r' ct bs}Dr.
  By Rewrite: gtr_split_eq; Apply gtree_cons_pairs_partition.
  Case (gtr_match0 r); [Apply: gtpl | Apply: gtpr].
  Case (gtr_match1 r); [Apply: gtpl | Apply: gtpr].
  Case (gtr_match2 r); [Apply: gtpl | Apply: gtpr].
  Case (gtr_match3 r); [Apply: gtpl | Apply: gtpr].
  By Case: (gtr_match0 r) (gtr_match1 r) => [|] [|] [|[|||] [|s' w']].
  By Case: (gtr_match1 r) (gtr_match2 r) => [|] [|] [|[|||] [|s' w']].
  By Case: (gtr_match1 r) (gtr_match3 r) => [|] [|] [|[|||] [|s' w']].
  By Case: (gtr_match2 r) (gtr_match3 r) => [|] [|] [|[|||] [|s' w']].
Qed.

Theorem gtree_mem0_restrict : (t : gtree; r : gtree_restriction)
  let t' = (gtree_pair_sub (gtree_restrict t r) false) in
  (w : chromogram) (gtree_mem t' w) = (andb (gtree_mem t w) (gtr_mem r w)).
Proof.
Move=> t r; Move.
Elim: t r => [t0 Hrec0 t1 Hrec1 t2 Hrec2 t3 Hrec3|||||||||] r w /=;
  Case Dr: r => [|bs ct r'];
  First [By Rewrite: /= gtree_mem_empty ?andbF | Rewrite: -~{bs ct r'}Dr].
  Rewrite: gtr_split_eq gtree_mem0_cons_pairs;
      Try Apply gtree_restrict_partition.
    By Case: w => [|s w]; Rewrite: // (gtr_mem_gsplit r); Case: s => /=.
  Case Hr: (gtr_match0 r) w => [|] [|[|||] [|s' w']];
    By Rewrite: // -gtr_match0_spec Hr.
  Case Hr: (gtr_match1 r) w => [|] [|[|||] [|s' w']];
    By Rewrite: // -gtr_match1_spec Hr.
  Case Hr: (gtr_match2 r) w => [|] [|[|||] [|s' w']];
    By Rewrite: // -gtr_match2_spec Hr.
  Case Hr: (gtr_match3 r) w => [|] [|[|||] [|s' w']];
    By Rewrite: // -gtr_match3_spec Hr.
  Case Hr: (gtr_match0 r); Case Hr': (gtr_match1 r) w => [|] [|[|||] [|s' w']];
    By Rewrite: // -?gtr_match0_spec -?gtr_match1_spec ?Hr ?Hr'.
  Case Hr: (gtr_match1 r); Case Hr': (gtr_match2 r) w => [|] [|[|||] [|s' w']];
    By Rewrite: // -?gtr_match1_spec -?gtr_match2_spec ?Hr ?Hr'.
  Case Hr: (gtr_match1 r); Case Hr': (gtr_match3 r) w => [|] [|[|||] [|s' w']];
    By Rewrite: // -?gtr_match1_spec -?gtr_match3_spec ?Hr ?Hr'.
  Case Hr: (gtr_match2 r); Case Hr': (gtr_match3 r) w => [|] [|[|||] [|s' w']];
    By Rewrite: // -?gtr_match2_spec -?gtr_match3_spec ?Hr ?Hr'.
Qed.

End GtreeRestrict.

Unset Implicit Arguments.

