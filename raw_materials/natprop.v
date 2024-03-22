(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require tacticext.
Require boolprop.
Require funs.
Require dataset.
Require Export Arith.

(*   A "reflected" version of Arith, with an emphasis on boolean predicates *)
(* and rewriting; this includes a canonical dataSet for nat, as well as     *)
(* reflected predicates, leq and ltn for comparison (ltn m n) is actually a *)
(* syntactic definition for the expansion of (leq (S m) n)),  hidden by the *)
(* pretty-printer. This has one serious advantage : reduction happen in the *)
(* same way in leq and ltn, and one drawback: rewrites that match leq will  *)
(* also match ltn.                                                          *)
(*   Also leq and ltn are defined so that they do NOT Simpl'ify; instead,   *)
(* rewrite rules are provided for cases where it is useful to do such       *)
(* simplifications (also, leq may be Unfold'ed to get reduction to true or  *)
(* false, should that be needed). This makes the manipulation of assertions *)
(* much more stable, while still allowing conversion for trivial uses.      *)
(*   Stable versions of plus and minus, addn and subn, respectively, are    *)
(* provided for the same reasons, and the standard arithmetic lemmas are    *)
(* replicated (however, this is not done for mult).                         *)
(*   Also included are replacements for the div2 lemmas, that fit better    *)
(* with the rest of the theory.                                             *)

Set Implicit Arguments.

Grammar constr if_is_pat : ast :=
  if_is_pat_O ["(" "0" ")"] ->
    [(QUALID O)]
| if_is_pat_1 ["(" "1" ")"] ->
    [(PATTCONSTRUCT (QUALID S) (QUALID O))]
| if_is_pat_2 ["(" "2" ")"] ->
    [(PATTCONSTRUCT (QUALID S) (PATTCONSTRUCT (QUALID S) (QUALID O)))]
| if_is_pat_3 ["(" "3" ")"] ->
    let $qS = [(QUALID S)] in
    [(PATTCONSTRUCT $qS (PATTCONSTRUCT $qS (PATTCONSTRUCT $qS (QUALID O))))]
| if_is_pat_4 ["(" "4" ")"] ->
    let $qS = [(QUALID S)] in let $p1 = [(PATTCONSTRUCT $qS (QUALID O))] in
    [(PATTCONSTRUCT $qS (PATTCONSTRUCT $qS (PATTCONSTRUCT $qS $p1)))]
| if_is_pat_5 ["(" "5" ")"] ->
    let $qS = [(QUALID S)] in let $p1 = [(PATTCONSTRUCT $qS (QUALID O))] in
    let $p4 = [(PATTCONSTRUCT $qS (PATTCONSTRUCT $qS (PATTCONSTRUCT $qS $p1)))] in
    [(PATTCONSTRUCT $qS $p4)]
| if_is_pat_6 ["(" "6" ")"] ->
    let $qS = [(QUALID S)] in let $p1 = [(PATTCONSTRUCT $qS (QUALID O))] in
    let $p4 = [(PATTCONSTRUCT $qS (PATTCONSTRUCT $qS (PATTCONSTRUCT $qS $p1)))] in
    [(PATTCONSTRUCT $qS (PATTCONSTRUCT $qS $p4))]
| if_is_pat_7 ["(" "7" ")"] ->
    let $qS = [(QUALID S)] in let $p1 = [(PATTCONSTRUCT $qS (QUALID O))] in
    let $p4 = [(PATTCONSTRUCT $qS (PATTCONSTRUCT $qS (PATTCONSTRUCT $qS $p1)))] in
    [(PATTCONSTRUCT $qS (PATTCONSTRUCT $qS (PATTCONSTRUCT $qS $p4)))]
| if_is_pat_8 ["(" "8" ")"] ->
    let $qS = [(QUALID S)] in let $p1 = [(PATTCONSTRUCT $qS (QUALID O))] in
    let $p4 = [(PATTCONSTRUCT $qS (PATTCONSTRUCT $qS (PATTCONSTRUCT $qS $p1)))] in
    let $p7 = [(PATTCONSTRUCT $qS (PATTCONSTRUCT $qS (PATTCONSTRUCT $qS $p4)))] in
    [(PATTCONSTRUCT $qS $p7)]
| if_is_pat_9 ["(" "9" ")"] ->
    let $qS = [(QUALID S)] in let $p1 = [(PATTCONSTRUCT $qS (QUALID O))] in
    let $p4 = [(PATTCONSTRUCT $qS (PATTCONSTRUCT $qS (PATTCONSTRUCT $qS $p1)))] in
    let $p7 = [(PATTCONSTRUCT $qS (PATTCONSTRUCT $qS (PATTCONSTRUCT $qS $p4)))] in
    [(PATTCONSTRUCT $qS (PATTCONSTRUCT $qS $p7))].

(* Canonical comparison and DataSet for nat.                                *)

Definition eq0 [n : nat] : bool :=
  if n is (0) then true else false.
Definition eqS [e_m : nat -> bool; n : nat] : bool :=
  if n is (S n') then (e_m n') else false.
Fixpoint eqn [n : nat] : nat -> bool :=
  if n is (S n') then (eqS (eqn n')) else eq0.

Lemma eq0E : eq0 = (eqn (0)). Proof. Done. Qed.
Lemma eqSE : (n : nat) (eqS (eqn n)) = (eqn (S n)). Proof. Done. Qed.

Lemma eqnPx : (reflect_eq eqn).
Proof.
Move=> n m; Apply: (iffP idP) => [|[]]; RightBy Elim n.
By Elim: n m => [|n Hrec] [|m]; Auto.
Qed.

Syntactic Definition eqnP := eqnPx | 2.

Canonical Structure natData := (DataSet eqnPx).

Lemma eqnE : eqn = (!eqd?). Proof. Done. Qed.

Lemma eqdSS : (m, n : nat) ((S m) =d (S n)) = (m =d n).
Proof. Done. Qed.

Lemma nat_eqT : (x, y : nat; E, E' : x = y) E == E'.
Proof. Exact (!data_eqT?). Qed.

(* Protected addition, with a more systematic set of lemmas.                *)

Definition addn : nat -> nat -> nat := (nosimpl plus).

Lemma addnI : plus = addn. Proof. Done. Qed.
Lemma add0n : (n : nat) (addn (0) n) = n. Proof. Done. Qed.
Lemma addSn : (m, n : nat) (addn (S m) n) = (S (addn m n)). Proof. Done. Qed.
Lemma add1n : (n : nat) (addn (1) n) = (S n). Proof. Done. Qed.

Lemma addn0 : (n : nat) (addn n (0)) = n.
Proof. By Move=> n; Apply: eqP; Elim: n. Qed.

Lemma addnS : (m, n : nat) (addn m (S n)) = (S (addn m n)).
Proof. By Move=> m n; Elim: m. Qed.

Lemma addSnnS : (m, n : nat) (addn (S m) n) = (addn m (S n)).
Proof. Move=> *; Rewrite addnS; Apply addSn. Qed.

Lemma addnCA : (m, n, p : nat) (addn m (addn n p)) = (addn n (addn m p)).
Proof. By Move=> m n; Elim: m => [|m Hrec] p; Rewrite: ?addSnnS -?addnS. Qed.

Lemma addnC : (m, n : nat) (addn m n) = (addn n m).
Proof. By Move=> m n; Rewrite: -{1 n}addn0 addnCA addn0. Qed.

Lemma addn1 : (n : nat) (addn n (1)) = (S n).
Proof. By Move=> *; Rewrite addnC. Qed.

Lemma addnA : (m, n, p : nat) (addn m (addn n p)) = (addn (addn m n) p).
Proof. By Move=> *; Rewrite: (addnC n) addnCA addnC. Qed.

Lemma eqn_add0 : (m, n : nat) ((addn m n) =d (0)) = (andb m =d (0) n =d (0)).
Proof. By Do 2 Case. Qed.

Lemma eqn_addl : (p, m, n : nat) ((addn p m) =d (addn p n)) = (m =d n).
Proof. By Move=> p *; Elim p. Qed.

Lemma eqn_addr : (p, m, n : nat) ((addn m p) =d (addn n p)) = (m =d n).
Proof. By Move=> p *; Rewrite: -!(addnC p) eqn_addl. Qed.

Lemma addn_injl : (p : nat) (injective (addn p)).
Proof. By Move=> p m n Heq; Apply: eqP; Rewrite: -(eqn_addl p) Heq set11. Qed.

Lemma addn_injr : (p : nat) (injective [m](addn m p)).
Proof. Move=> p m n; Rewrite: -!(addnC p); Apply addn_injl. Qed.

(* Protected substraction, and basic lemmas. Further properties depend on *)
(* ordering conditions.                                                   *)

Definition subn : nat -> nat -> nat := (nosimpl minus).

Lemma subnI : minus = subn. Proof. Done. Qed.
Lemma sub0n : (n : nat) (subn (0) n) = (0). Proof. Done. Qed.
Lemma subn0 : (n : nat) (subn n (0)) = n. Proof. By Case. Qed.
Lemma subnn : (n : nat) (subn n n) = (0). Proof. By Elim. Qed.
Lemma subSS : (n, m : nat) (subn (S m) (S n)) = (subn m n). Proof. Done. Qed.
Lemma subn1 : (n : nat) (subn n (1)) = (pred n). Proof. By Case; Try Case. Qed.

Lemma subn_add2l : (p, m, n : nat) (subn (addn p m) (addn p n)) = (subn m n).
Proof. By Move=> p *; Elim p. Qed.

Lemma subn_add2r : (p, m, n : nat) (subn (addn m p) (addn n p)) = (subn m n).
Proof. By Move=> *; Rewrite: -!(addnC p) subn_add2l. Qed.

Lemma subn_addr : (n, m : nat) (subn (addn n m) n) = m.
Proof. By Move=> n *; Rewrite: -{2 n}addn0 subn_add2l subn0. Qed.

Lemma subn_addl : (n, m : nat) (subn (addn m n) n) = m.
Proof. By Move=> n m; Rewrite: (addnC m) subn_addr. Qed.

Lemma subSnn : (n : nat) (subn (S n) n) = (1).
Proof. Exact [n](subn_addl n (1)). Qed.

Lemma subn_sub : (m, n, p : nat) (subn (subn n m) p) = (subn n (addn m p)).
Proof. By Move=> m n p; Elim: m n => [|m Hrec] [|n]; Try Exact (Hrec n). Qed.

(* Integer ordering, and its interaction with the other operations.       *)

Definition leq [m, n : nat] : bool := (subn m n) =d (0).

Grammar constr constr0 : constr :=
  ltn_to_leqS [ "(" "ltn" constr9($m) constr9($n) ")" ] ->
    [(leq (S $m) $n)]
| geq_to_leq  [ "(" "geq" constr9($m) constr9($n) ")" ] ->
    [(leq $n $m)]
| gtn_to_leq  [ "(" "gtn" constr9($m) constr9($n) ")" ] ->
    [(leq (S $n) $m)].

Syntax constr level 0:
    pp_leqS_ltn [(leq (S $m) $n)] ->
      [ (OPFORM ltn $m $n) ].

Lemma lePx : (m, n : nat) (reflect (le m n) (leq m n)).
Proof.
Move=> m n; Elim: m n => [|m Hrec] [|n]; Try (Constructor; Auto with arith).
Apply: (iffP (Hrec ?)); Auto with arith.
Qed.

Syntactic Definition leP := lePx | 2.

Lemma le_eqT : (m, n : nat; H, H' : (le m n)) H == H'.
Proof.
Move=> m n; Elim: {n}(S n) {-2}n (erefl (S n)) => [|n Hrec] n' //.
Injection=> Dn'; Rewrite: ~{n'}Dn'.
Move=> H; Rewrite: -{H}/(eq_ind ? ? ? H ? (erefl n)).
Case: {1 2 6}n / H (erefl n) => [|n' H] Dn H'.
  Case: H' Dn => [|n'' H'] Dn; LeftBy Rewrite (eqP_K Dn).
  By Case (lt_n_n n''); Rewrite: /lt -Dn.
Case: H' Dn {Hrec}(Hrec ? Dn H) =>  [|n'' H'] Dn Hrec.
  By Case: (lt_n_n n'); Rewrite: /lt Dn.
By Injection: Dn {}Dn H' => [] Dn H'; Rewrite: (eqP_K Dn) (Hrec H').
Qed.

Lemma ltPx : (m, n : nat) (reflect (lt m n) (ltn m n)).
Proof. Move=> *; Exact leP. Qed.

Syntactic Definition ltP := ltPx | 2.

Lemma lt_eqT : (m, n : nat; H, H' : (lt m n)) H == H'.
Proof. Exact [m](!le_eqT (S m)). Qed.

Lemma leqNgt : (m, n : nat) (leq m n) = (negb (ltn n m)).
Proof. By Elim=> [|m Hrec] [|n]; Try Exact (Hrec n). Qed. 

Lemma ltnNge : (m, n : nat) (ltn m n) = (negb (leq n m)).
Proof. By Move=> *; Rewrite leqNgt. Qed.

Lemma leqnn : (n : nat) (leq n n).
Proof. By Elim. Qed.

Lemma eq_leq : (m, n : nat) m = n -> (leq m n).
Proof. By Move=> m n []; Apply leqnn. Qed.

Lemma ltnn : (n : nat) (ltn n n) = false.
Proof. By Move=> *; Rewrite: ltnNge leqnn. Qed.

Lemma leqnSn : (n : nat) (leq n (S n)).
Proof. By Elim. Qed.

Lemma ltnSn : (n : nat) (ltn n (S n)).
Proof. Exact leqnn. Qed.

Lemma ltnS : (m, n : nat) (ltn m (S n)) = (leq m n).
Proof. Done. Qed.

Lemma leq0n : (n : nat) (leq (0) n).
Proof. Done. Qed.

Lemma ltn0Sn : (n : nat) (ltn (0) (S n)).
Proof. Done. Qed.

Lemma ltn0 : (n : nat) (ltn n (0)) = false.
Proof. Done. Qed.

Inductive leq_xor_gtn [m, n : nat] : bool -> bool -> Set :=
  LeqNotGtn  : (leq m n) -> (leq_xor_gtn m n true false)
| GtnNotLeq  : (ltn n m) -> (leq_xor_gtn m n false true).

Lemma leqP : (m, n : nat) (leq_xor_gtn m n (leq m n) (ltn n m)).
Proof.
Move=> m n; Rewrite: ltnNge; Case Hmn: (leq m n); Constructor; Auto.
By Rewrite: ltnNge Hmn.
Qed.

Inductive ltn_xor_geq [m, n : nat] : bool -> bool -> Set :=
  LtnNotGeq  : (ltn m n) -> (ltn_xor_geq m n true false)
| GeqNotLtn  : (leq n m) -> (ltn_xor_geq m n false true).

Lemma ltnP : (m, n : nat) (ltn_xor_geq m n (ltn m n) (leq n m)).
Proof. By Move=> m n; Rewrite: -(ltnS n); Case (leqP (S m) n); Constructor. Qed.

Lemma ltnSpred : (n, m : nat) (ltn m n) -> (S (pred n)) = n.
Proof. By Move=> [|n]. Qed.

Lemma leq_eqVlt : (m, n : nat) (leq m n) = (orb m =d n (ltn m n)).
Proof. By Elim=> [|m Hrec] [|n]; Try Exact (Hrec n). Qed.

Lemma ltn_neqAle : (m, n : nat) (ltn m n) = (andb (negb m =d n) (leq m n)).
Proof. By Elim=> [|m Hrec] [|n]; Try Exact (Hrec n). Qed.

Lemma leq_trans : (n, m, p : nat) (leq m n) -> (leq n p) -> (leq m p).
Proof. By Elim=> [|m Hrec] [|n] [|p]; Try Exact (Hrec n p). Qed.

Lemma leqW : (m, n : nat) (leq m n) -> (leq m (S n)).
Proof. Exact [m, n](leq_trans 3!(S ?) (leqnSn m)). Qed.

Lemma ltnW : (m, n : nat) (ltn m n) -> (leq m n).
Proof. Exact [m](!leqW (S m)). Qed.

Lemma ltn_trans : (n, m, p : nat) (ltn m n) -> (ltn n p) -> (ltn m p).
Proof. Exact [n,m,p; Hmn](leq_trans (leqW Hmn)). Qed.

Lemma leq_add2l : (p, m, n : nat) (leq (addn p m) (addn p n)) = (leq m n).
Proof. By Move=> p *; Elim p. Qed.

Lemma leq_add2r : (p, m, n : nat) (leq (addn m p) (addn n p)) = (leq m n).
Proof. Move=> p *; Rewrite: -!(addnC p); Apply leq_add2l. Qed.

Lemma leq_add2 : (m1, m2, n1, n2 : nat)
  (leq m1 m2) -> (leq n1 n2) -> (leq (addn m1 n1) (addn m2 n2)).
Proof.
Move=> m1 m2 n1 n2 Hm Hn.
By Apply (!leq_trans (addn m2 n1)); Rewrite: ?leq_add2l ?leq_add2r.
Qed.

Lemma leq_addr : (m, n : nat) (leq n (addn n m)).
Proof. By Move=> m n; Rewrite: -{1 n}addn0 leq_add2l. Qed.

Lemma leq_addl : (m, n : nat) (leq n (addn m n)).
Proof. Move=> *; Rewrite addnC; Apply leq_addr. Qed.

Lemma eqn_leq : (m, n : nat) (m =d n) = (andb (leq m n) (leq n m)).
Proof. By Elim=> [|m Hrec] [|n]; Try Exact (Hrec n). Qed.

Lemma leqn0 : (n : nat) (leq n (0)) = (n =d (0)).
Proof. By Move=> *; Rewrite: eqd_sym eqn_leq /=. Qed.

Lemma ltn_lt0sub : (m, n : nat) (ltn m n) = (ltn (0) (subn n m)).
Proof. By Elim=> [|m Hrec] [|n]; Try Exact (Hrec n). Qed.

Lemma eqn_sub0 : (m, n : nat) ((subn m n) =d (0)) = (leq m n).
Proof. Done. Qed.

Lemma leq_sub_add : (m, n, p : nat)(leq (subn m n) p) = (leq m (addn n p)).
Proof. By Move=> *; Rewrite: /leq subn_sub. Qed.

Lemma leq_subr : (m, n : nat) (leq (subn n m) n).
Proof. By Move=> *; Rewrite: leq_sub_add leq_addl. Qed.

Lemma leq_add_sub : (m, n : nat) (leq m n) -> (addn m (subn n m)) = n.
Proof. By Elim=> [|m Hrec] [|n]; Try Exact [H](congr S (Hrec n H)). Qed.

Lemma leq_sub_sub : (m, n : nat) (leq m n) -> (subn n (subn n m)) = m.
Proof. By Move=> m n Hmn; Rewrite: -{1 n}(leq_add_sub Hmn) subn_addl. Qed.

Lemma leq_subS : (m, n : nat) (leq m n)->(subn (S n) m) = (S (subn n m)).
Proof. By Elim=> [|m Hrec] [|n]; Try Exact (Hrec n). Qed.

Lemma ltn_subS : (m, n : nat) (ltn m n)->(subn n m) = (S (subn n (S m))).
Proof. Exact [m](!leq_subS (S m)). Qed.

Lemma leq_sub2r : (p, m, n : nat) (leq m n) -> (leq (subn m p) (subn n p)).
Proof.
Move=> p m n Hmn; Rewrite leq_sub_add; Apply: (leq_trans Hmn).
By Rewrite: -leq_sub_add leqnn.
Qed.

Lemma leq_sub2l : (p, m, n : nat) (leq m n) -> (leq (subn p n) (subn p m)).
Proof.
Move=> p m n; Rewrite: -(leq_add2r (subn p m)) leq_sub_add.
By Apply: leq_trans; Rewrite: -leq_sub_add leqnn.
Qed.

Lemma leq_sub2 : (m1, m2, n1, n2 : nat)
  (leq m1 m2) -> (leq n2 n1) -> (leq (subn m1 n1) (subn m2 n2)).
Proof.
Exact [_, _, _, _; Hm; Hn](leq_trans (leq_sub2l ? Hn) (leq_sub2r ? Hm)).
Qed.

(* Parity and bits. *)

Coercion nat_of_bool := [b : bool] if b then (1) else (0).

Lemma addn_negb : (b : bool) (addn (negb b) b) = (1).
Proof. By Case. Qed.

Fixpoint odd [n : nat] : bool := if n is (S n') then (negb (odd n')) else false.

Lemma odd_addn : (m, n : nat) (odd (addn m n)) = (addb (odd m) (odd n)).
Proof.
Move=> m n; Elim: m => [|m Hrec] //=.
By Rewrite: -addTb addnI Hrec addbA addTb.
Qed.

Lemma odd_subn : (m, n : nat) (leq n m) ->
  (odd (subn m n)) = (addb (odd m) (odd n)).
Proof.
Move=> m n Hnm; Apply addb_movelr.
Rewrite: -odd_addn; Exact (congr odd (leq_add_sub Hnm)).
Qed.

(* Doubling; *)

Fixpoint double_rec [n : nat] : nat :=
  if n is (S n') then (S (S (double_rec n'))) else (0).

Definition double : nat -> nat := (nosimpl double_rec).

Lemma doubleI : double_rec = double. Proof. Done. Qed.

Lemma double0 : (double (0)) = (0). Proof. Done. Qed.

Lemma doubleS : (n : nat) (double (S n)) = (S (S (double n))).
Proof. Done. Qed.

Lemma double_addnn : (n : nat) (double n) = (addn n n).
Proof. By Move=> n; Apply: eqP; Elim: n => *; Rewrite: ?addnS. Qed.

Lemma double_add : (m, n : nat)
  (double (addn m n)) = (addn (double m) (double n)).
Proof. By Move=> m n; Rewrite: !double_addnn -!addnA (addnCA n). Qed.

Lemma double_sub : (m, n : nat)
  (double (subn m n)) = (subn (double m) (double n)).
Proof. By Elim=> [|m Hrec] [|n]; Try Exact (Hrec n). Qed.

Lemma leq_double : (m, n : nat) (leq (double m) (double n)) = (leq m n).
Proof. By Move=> m n; Rewrite: /leq -double_sub; Case (subn m n). Qed.

Lemma ltn_double : (m, n : nat) (ltn (double m) (double n)) = (ltn m n).
Proof. By Move=> *; Rewrite: !ltnNge leq_double. Qed.

Lemma ltn_Sdouble : (m, n : nat) (ltn (S (double m)) (double n)) = (ltn m n).
Proof. By Move=> *; Rewrite: -doubleS leq_double. Qed.

Lemma leq_Sdouble : (m, n : nat) (leq (double m) (S (double n))) = (leq m n).
Proof. By Move=> *; Rewrite: leqNgt ltn_Sdouble -leqNgt. Qed.

Lemma odd_double : (n : nat) (odd (double n)) = false.
Proof. By Move=> *; Rewrite: double_addnn odd_addn addbb. Qed.

(* Halving. *)

Fixpoint half [n : nat] : nat := if n is (S n') then (uphalf n') else (0)
with uphalf [n : nat] : nat := if n is (S n') then (S (half n')) else (0).

Lemma half_double : (n : nat) (half (double n)) = n.
Proof. By Elim=> [|n Hrec] //=; Congr S. Qed.

Lemma uphalf_double : (n : nat) (uphalf (double n)) = n.
Proof. By Elim=> [|n Hrec] //=; Congr S. Qed.

Lemma uphalf_half : (n : nat) (uphalf n) = (addn (odd n) (half n)).
Proof. By Elim=> [|n Hrec] //=; Rewrite: Hrec addnA addn_negb. Qed.

Lemma odd_double_half : (n : nat) (addn (odd n) (double (half n))) = n.
Proof.
By Elim=> [|n Hrec] //=; Rewrite: -{3 n}Hrec uphalf_half double_add; Case (odd n).
Qed.

Lemma half_bit_double : (n : nat; b : bool) (half (addn b (double n))) = n.
Proof. Move=> n [|]; [Exact (uphalf_double n) | Exact (half_double n)]. Qed.

Lemma half_add : (m, n : nat)
  (half (addn m n)) = (addn (andb (odd m) (odd n)) (addn (half m) (half n))).
Proof.
Move=> m n; Rewrite: -{1 n}odd_double_half addnCA -{1 m}odd_double_half.
Rewrite: -addnA -double_add.
By Case (odd n); Case (odd m); Rewrite: /= ?add0n ?half_double ?uphalf_double.
Qed.

Lemma half_leq : (m, n : nat) (leq m n) -> (leq (half m) (half n)).
Proof.
Move=> m n; Rewrite: -{1 m}odd_double_half -{1 n}odd_double_half.
Case (odd m); Case (odd n); Rewrite: /addn /= ?add0n ?ltnS;
  By Rewrite: ?leq_double ?ltn_double ?leq_Sdouble; Try Exact [H](leqW H).
Qed.

(* A congruence tactic, similar to the boolean one, along with an S/addn *)
(* normalization tactic.                                                 *)

Definition natNorm1 : nat := (1).
Lemma addnNorm1 : (n : nat) (S n) = (addn natNorm1 n). Proof. Done. Qed.

Tactic Definition NatNorm :=
  Rewrite: ?add0n ?addn0;
  Rewrite: -/natNorm1 ?addnNorm1 -?addnA -?addnNorm1 /natNorm1 ?addnS ?addn0.

Tactic Definition NatCongr :=
  First [
    Refine (congr S ?)
  | Refine (congr pred ?)
  | Refine (congr (addn ?) ?)
  | Refine (congr (subn ?) ?)
  | Refine (congr [n](addn n ?) ?)
  | Refine (congr [n](subn n ?) ?)
  | Match Context With
    [|- (addn ?1 ?2) = ?3] ->
      Symmetry; Rewrite: -1?(addnC ?1) -?(addnCA ?1);
      Refine (congr (addn ?1) ?); Symmetry
  ].

Unset Implicit Arguments.
