(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require tacticext.
Require boolprop.
Require funs.
Require dataset.
Require natprop.

Set Implicit Arguments.

(* ``Dyck numbers'', i.e., the number of balanced bracket words of length n. *)
(* (In fact, we define generalized Dyck numbers, that allow for m-1 extra    *)
(* closing brackets.) Dyck numbers are the only link between the initial     *)
(* color and (chromo)gram trees.                                             *)

Fixpoint gen_dyck [m, n : nat] : nat :=
  Cases n m of
    (0) (1) => (1)
  | (S n') (S m') => (addn (gen_dyck (S m) n') (gen_dyck m' n'))
  | _ _ => (0)
  end.

Definition dyck : nat -> nat := (gen_dyck (1)).

Lemma gen_dyck_max : (m, n : nat; Hm : (ltn (S n) m))
  (gen_dyck m n) = (0).
Proof.
Move=> m n; Elim: n m => [|n Hrec] [|m] //; LeftBy Case m.
Move=> Hm; Rewrite: /= !Hrec //; Exact (leq_trans (leq_addl (2) n) Hm).
Qed.

Lemma gen_dyck_all_close : (m : nat) (gen_dyck (S m) m) = (1).
Proof.
Elim => [|m Hrec] //=; Rewrite: Hrec gen_dyck_max //; Exact (leqnSn m).
Qed.

Lemma even_dyck_pos : (n : nat) (ltn (0) (dyck (double n))).
Proof.
Move=> n; Rewrite: /dyck -(addn0 (double n)).
Elim: n {-1} (0) => [|n Hrec] m; LeftBy Rewrite gen_dyck_all_close.
Rewrite: doubleS addSnnS addSn; Exact (leq_trans (Hrec ?) (leq_addr ? ?)).
Qed.

Unset Implicit Arguments.
