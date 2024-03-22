(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require tacticext.
Require boolprop.
Require funs.
Require dataset.
Require natprop.
Require seq.
Require color.

Set Implicit Arguments.

(* Chromograms are words representing congruence classes of regions wrt. *)
(* Kempe inversions for a single edge color (and color permutation).     *)
(* The relevant topological information for each class consists of a set *)
(* of non-intersecting chords linking perimeter edges, and the parity of *)
(* the number of links for each chord. The word representation of these  *)
(* chords is a Dyck word augmented with spaces (for perimeter edges that *)
(* are not linked because they are colored with the inversion color) and *)
(* parities (on closing brackets), each chord being represented with a   *)
(* matching bracket pair.                                                *)
(*   The relationship between chromograms and graphs will be developped  *)
(* elsewhere. Here we develop correctness of the words, and the matching *)
(* relation between (completed) edge traces and chromograms. We also     *)
(* define the relation on incomplete edge traces and chromograms with    *)
(* the last symbol removed; this is the form actually used for the       *)
(* correctness proof of the reducibility check.                          *)

Inductive gram_symbol : Set :=
  Gpush : gram_symbol
| Gskip : gram_symbol
| Gpop0 : gram_symbol
| Gpop1 : gram_symbol.

Definition eqgs [s1, s2 : gram_symbol] : bool :=
  Cases s1 s2 of
    Gpush Gpush => true
  | Gskip Gskip => true
  | Gpop0 Gpop0 => true
  | Gpop1 Gpop1 => true
  | _ _ => false
  end.

Lemma eqgsP : (reflect_eq eqgs).
Proof. By Do 2 Case; Constructor. Qed.

Canonical Structure gramSymbolData := (DataSet eqgsP).

Definition chromogram : Set := (seq gramSymbolData).

Fixpoint gram_balanced [d : nat; b0 : bool; w : chromogram] : bool :=
  Cases w d of
    Seq0 (0) => (negb b0)
  | (Adds Gpush w') _ => (gram_balanced (S d) b0 w')
  | (Adds Gskip w') _ => (gram_balanced d (negb b0) w')
  | (Adds Gpop0 w') (S d') => (gram_balanced d' b0 w')
  | (Adds Gpop1 w') (S d') => (gram_balanced d' (negb b0) w')
  | _ _ => false
  end.

Fixpoint matchg [lb : bitseq; et : colseq; w : chromogram] : bool :=
  Cases w et lb of
    Seq0 Seq0 Seq0 => true
  | (Adds s w') (Adds e et') _ =>
    Cases e s lb of
      Color1 Gskip _ => (matchg lb et' w')
    | Color2 Gpush _ => (matchg (Adds false lb) et' w')
    | Color2 Gpop0 (Adds false lb') => (matchg lb' et' w')
    | Color2 Gpop1 (Adds true lb') => (matchg lb' et' w')
    | Color3 Gpush _ => (matchg (Adds true lb) et' w')
    | Color3 Gpop0 (Adds true lb') => (matchg lb' et' w')
    | Color3 Gpop1 (Adds false lb') => (matchg lb' et' w')
    | _ _ _ => false
    end
  | _ _ _ => false
  end.

Definition kempe_closed [P : colseq -> Prop] : Prop :=
  (et : colseq; Het : (P et))
    (and (g : edge_perm) (P (permt g et))
      (EX w | (matchg seq0 et w)
            & (et' : colseq) (matchg seq0 et' w) -> (P et'))).

Definition kempe_coclosure [P : colseq -> Prop; et : colseq] : Prop :=
  (P' : colseq -> Prop)
  (kempe_closed P') -> (P' et) -> (EX et' | (P et') & (P' et')).

Lemma matchg_size : (et : colseq; lb : bitseq; w : chromogram)
  (matchg lb et w) -> (size w) = (size et).
Proof.
Elim=> [|e et Hrec] lb [|s w] Hm //=; Congr S; Case: s Hm.
  By Case: e (Hrec (Adds (cbit0 e) lb) w).
  By Case: e (Hrec lb w).
  By Case: e lb (Hrec (behead lb) w); Do 3 Case=> //.
  By Case: e lb (Hrec (behead lb) w); Do 3 Case=> //.
Qed.

Lemma matchg_memc0 : (et : colseq; lb : bitseq; w : chromogram)
  (matchg lb et w) -> (et Color0) = false.
Proof.
Elim=> [|e et Hrec] lb [|s w] //=; Case: s.
  By Case: e (Hrec (Adds (cbit0 e) lb) w).
  By Case: e (Hrec lb w).
  By Case: e lb (Hrec (behead lb) w); Do 3 Case=> //.
  By Case: e lb (Hrec (behead lb) w); Do 3 Case=> //.
Qed.

Section BalanceLemmas.

Local sumb : bitseq -> bool := (foldr addb false).

Lemma matchg_balanced : (et : colseq; w : chromogram)
  (Hm : (matchg seq0 et w))
     (cbit1 (sumt et)) = false
  /\ (gram_balanced (0) (cbit0 (sumt et)) w).
Proof.
Move=> et; Rewrite: -[c](addFb (cbit0 c)) -[c](addFb (cbit1 c)). 
Pose sb := (seq0::bitseq); Rewrite: -{3 false}/(sumb sb).
Rewrite: -{1 false}/(odd (0)) -{(0)}/(size sb).
Elim: et sb => [|e et Hrec] lb [|s w] //; LeftBy Case lb.
Rewrite: /= cbit0_addc cbit1_addc 2!addbA -addTb.
Rewrite: -(addbC (cbit0 e)) -(addbC (cbit1 e)) !addbA.
Case: s {Hrec}(Hrec (Adds (cbit0 e) lb) w) (Hrec lb w) (Hrec (behead lb) w);
  Case: e => //=; Auto; Case: lb => [|[|] lb] //=; Rewrite: ?negb_elim //; Auto.
Qed.

Lemma balanced_inj : (w : chromogram; n1, n2 : nat; b1, b2 : bool)
  (gram_balanced n1 b1 w) -> (gram_balanced n2 b2 w) -> 
  n1 = n2 /\ b1 = b2.
Proof.
By Elim=> [|[|||] w Hrec] [|n1] [|n2] [|] [|] //= Hw1 Hw2;
   Case: (Hrec ? ? ? ? Hw1 Hw2) => [Dn Db];
   Rewrite: ?Dn ?(eq_add_S ? ? Dn).
Qed.

Lemma balanced_sumt0 : (w : chromogram; et : colseq)
  (gram_balanced (0) false w) -> (matchg seq0 et w) -> (sumt et) = Color0.
Proof.
Move=> w et Hwf; Move/matchg_balanced=> [Hst1 Hwt].
Rewrite: -(ccons_cbits (sumt et)) Hst1.
By Case: (balanced_inj Hwf Hwt) => [_ []].
Qed.

Lemma match_etrace : (et : colseq; w : chromogram)
  (matchg seq0 (etrace et) w) = (matchg seq0 et w).
Proof.
Move=> et; Rewrite: /etrace /etrace_perm; Pose sb := (seq0::bitseq).
Case (even_trace et); LeftBy Rewrite permt_id.
Rewrite: -{2 sb}/(maps negb sb).
Elim: et sb =>  [|e et Hrec] lb [|s w] //; LeftBy Case lb.
By Case: e; Case: s => //=; First [Rewrite Hrec | Case: lb => //; Case=> //=].
Qed.

(* Algorithmic predicates, for chromogram paths. *)

Inductive bit_stack : Set :=
  Bstack0 : bit_stack
| Bpush0 :  bit_stack -> bit_stack
| Bpush1 :  bit_stack -> bit_stack.

Fixpoint bitseq_of_stack [bs : bit_stack] : bitseq :=
  Cases bs of
    Bstack0 => seq0
  | (Bpush0 bs') => (Adds false (bitseq_of_stack bs'))
  | (Bpush1 bs') => (Adds true (bitseq_of_stack bs'))
  end.

Definition stack_of_bitseq : bitseq -> bit_stack :=
  (foldr [b : bool](if b then Bpush1 else Bpush0) Bstack0).

Fixpoint cgram [d : nat; b0 : bool; w : chromogram] : chromogram :=
  Cases w of
    Seq0 => (seq1 if d then Gskip else [_]if b0 then Gpop1 else Gpop0)
  | (Adds s w') =>
      (Adds s Cases s of
         Gpush => (cgram (S d) b0 w')
       | Gskip => (cgram d (negb b0) w')
       | Gpop0 => (cgram (pred d) b0 w')
       | Gpop1 => (cgram (pred d) (negb b0) w')
      end)
  end.

Fixpoint matchpg [bs : bit_stack; et : colseq; w : chromogram]
                     : bool :=
  Cases w et of
    Seq0 Seq0 => true
  | (Adds s w') (Adds e et') =>
    Cases e s bs of
      Color1 Gskip _ => (matchpg bs et' w')
    | Color2 Gpush _ => (matchpg (Bpush0 bs) et' w')
    | Color2 Gpop0 (Bpush0 bs') => (matchpg bs' et' w')
    | Color2 Gpop1 (Bpush1 bs') => (matchpg bs' et' w')
    | Color3 Gpop0 (Bpush1 bs') => (matchpg bs' et' w')
    | Color3 Gpush _ => (matchpg (Bpush1 bs) et' w')
    | Color3 Gpop1 (Bpush0 bs') => (matchpg bs' et' w')
    | _ _ _ => false
    end
  | _ _ => false
  end.

Lemma matchg_cgram : (cw : chromogram; et : colseq)
  (matchg seq0 (ctrace et) cw)
     -> cw = (cgram (0) false (take (pred (size cw)) cw)).
Proof.
Move=> cw et Hm; Case (matchg_balanced Hm); Clear; Rewrite: sumt_ctrace /=.
Case: cw Hm (0) {}false => [|s w] /=; LeftBy Case et.
Clear; Elim: w s => [|s' w Hrec] s d b0; LeftBy Case: s b0 d; Do 3 Case => //.
By Case: s => //= [] Hw; Congr Adds; Apply: Hrec; Case: d Hw; Case b0.
Qed.

Lemma matchg_pg : (et : colseq; w : chromogram)
  (Hw : (gram_balanced (0) false (cgram (0) false w)))
  (matchg seq0 (ctrace et) (cgram (0) false w)) = (matchpg Bstack0 et w).
Proof.
Move=> et; Rewrite: /ctrace -(add0c (sumt et)); Pose sb := (seq0::bitseq).
Rewrite: -{Color0}/(ccons (odd (0)) (sumb sb)) -(addFb (sumb sb)).
Rewrite: -{(0)}/(size sb) -{(Bstack0)}/(stack_of_bitseq sb).
Elim: et sb {}false => [|e et Hrec] lb b.
  Case=> [|s w] /=; LeftBy Do 2 Case: b lb => [|] [|b lb] //.
  Clear; Def: d := (size lb).
  By Case: (addc (ccons (odd d) (addb b (sumb lb))) Color0);
     Case: s => //; Case: w => //; Case: lb => //; Case.
Case=> [|s w]; Rewrite: ?add_last_adds /=.
  By Case: lb => [|b' [|b'' lb]] // _; Case: e => //; Case: et {Hrec} => //;
     Case b; Case b'.
Case: s; Try (Case: lb; LeftDone; Case=> [|] lb /=);
  Case: e (Hrec (Adds (cbit0 e) lb)) => [] //= Hrec' Hm;
  Rewrite: -?(Hrec ? ? ? Hm) -?(Hrec' ? ? Hm) ~{Hrec Hrec' Hm};
  By Case (sumt et); Case (odd (size lb)); Case b; Case (sumb lb).
Qed.

Lemma matchpg_etrace : (et : colseq; w : chromogram)
  (matchpg Bstack0 (etrace et) w) = (matchpg Bstack0 et w).
Proof.
Move=> et; Rewrite: /etrace /etrace_perm; Pose sb := (seq0::bitseq).
Case: (even_trace et) => /=; LeftBy Rewrite permt_id.
Rewrite: -{Bstack0}/(stack_of_bitseq sb) -{1 sb}/(maps negb sb).
Elim: et sb => [|e et Hrec] lb [|s w] //.
By Case: e (Hrec (Adds (cbit0 e) lb) w); Case: s => //=;
   Case: lb => //; Case=> /=.
Qed.

Lemma matchpg_size : (et : colseq; bs : bit_stack; w : chromogram)
  (matchpg bs et w) -> (size w) = (size et).
Proof.
Elim=> [|e et Hrec] bs [|s w] Hm //=; Congr S; Case: s Hm.
  By Case: e (Hrec (if (cbit0 e) then Bpush1 else Bpush0 bs) w).
  By Case: e (Hrec bs w).
  By Case: e bs => [|||] [|bs|bs] Hm; Try Exact (Hrec ? ? Hm).
  By Case: e bs => [|||] [|bs|bs] Hm; Try Exact (Hrec ? ? Hm).
Qed.

Lemma matchpg_flip : (et : colseq)
  (matchpg Bstack0 (permt Eperm132 et)) =1 (matchpg Bstack0 et).
Proof.
Pose sb := (seq0::bitseq); Rewrite: -{Bstack0}/(stack_of_bitseq sb).
Rewrite: -{1 sb}/(maps negb sb) /eqfun.
Move=> et; Elim: et sb => [|e et Hrec] lb [|s w] //.
By Case: e (Hrec (Adds (cbit0 e) lb) w); Case: s => //=;
   Case: lb => //; Case=> /=.
Qed.

End BalanceLemmas.

Unset Implicit Arguments.
