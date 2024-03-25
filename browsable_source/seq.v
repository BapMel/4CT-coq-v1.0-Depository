(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require tacticext.
Require funs.
Require boolprop.
Require dataset.
Require natprop.
Require Export PolyList.

Set Implicit Arguments.

(* Generic dataSet seq : sequences of data items, essentially  polymorphic *)
(* lists of data items, but with additional operations, such as finding    *)
(* items and indexing. Sequences need to be defined as a separate type,    *)
(* rather than an abbreviation for lists, because that abbreviation would  *)
(* be expanded out when doing elimination on a sequence. We provide a      *)
(* sequence-to-list coercion, which in principle allows the use of length, *)
(* fold_right and fold_left on seq. Unfortunately, unavoidable reductions  *)
(* of the datum component of canonical dataSets would make equational      *)
(* lemmas for these operations all but useless; hence we need to define    *)
(* our own variants (size, foldr, and foldl) of these operations, with a   *)
(* more useful order of arguments for foldl to boot. The list operations   *)
(* app, rev and map need seq counterparts (cat, rev, and maps) anyway,     *)
(* since they return sequences.                                            *)
(*   Since there is no true subtyping in Coq, we don't use a type for non  *)
(* empty sequences; rather, we pass explicitly the head and "tail" of the  *)
(* sequence.                                                               *)
(*   The empty sequence is especially bothersome for subscripting, since   *)
(* it forces us to have a default value. We use a combination of syntactic *)
(* extensions/prettyprinting to hide them in most of the development.      *)
(*   Here is the list of seq operations :                                  *)
(*   - constructors : Seq0 (seq0 if polymorphic), Adds, addsn, add_last    *)
(*   - factories : seq0 (syntax def), seq1, seq2, seq3, seqn, nseq (n-ary) *)
(*                 mkseq (computing items from indexes).                   *)
(*   - casts: list_of_seq (coercion), seq_of_list                          *)
(*   - access: behead, last, belast (the latter for the non empty case)    *)
(*   - indexing: head, sub (with a default element), incr_sub (for natseq) *)
(*   - size: size (seq version of length)                                  *)
(*   - elemets lookup: index, mem (which is a coercion)                    *)
(*   - subset lookup: find, filter, count, has, all, sieve                 *)
(*   - "no duplicates" predicate: uniq                                     *)
(*   - surgery: cat, drop, take, rot, rotr, rev                            *)
(*   - iterators: maps, foldr (= fold_right), foldl, scanl, pairmap        *)
(* The sieve operator uses a boolean sequence to select a subsequence; it  *)
(* is used heavily for the correctness of the config compilation.          *)
(* We are quite systematic in providing lemmas to rewrite any composition  *)
(* of two operations. "rev", whose simplifications are not natural, is     *)
(* protected with nosimpl.                                                 *)
(* We also define a (Seq ...) syntactic form.                              *)

Section Sequences.

Variable n0 : nat.    (* numerical parameter for take, drop et al *) 
Variable d : dataSet. (* must come before the implicit domain *)
Variable x0 : d.      (* default for head/sub *)

Inductive seq : Set := Seq0 : seq | Adds : d -> seq -> seq.

Fixpoint list_of_seq [s : seq] : (list d) :=
  if s is (Adds x s') then (cons x (list_of_seq s')) else (nil ?).

Coercion list_of_seq : seq >-> list.

Definition seq_of_list : (list d) -> seq := (fold_right Adds Seq0).

Lemma seqI : (l : (list d)) l = (seq_of_list l).
Proof. By Elim => [|x l Hrec] //=; Rewrite: -Hrec. Qed.

Lemma seqE : (s : seq) s = (seq_of_list s).
Proof. By Elim => [|s l Hrec] //=; Rewrite: -Hrec. Qed.

Fixpoint size [s : seq] : nat :=
  if s is (Adds _ s') then (S (size s')) else (0).

Lemma size_length : (s : seq) (size s) = (length s).
Proof. By Elim; Simpl; Auto. Qed.

Definition head [s : seq] : d := if s is (Adds x _) then x else x0.

Definition behead [s : seq] : seq := if s is (Adds _ s') then s' else Seq0.

Lemma size_behead : (s : seq) (size (behead s)) = (pred (size s)).
Proof. By Case. Qed.

(* Equality makes both seq into a datatype. *)

Fixpoint eqseq [s1, s2 : seq] : bool :=
  Cases s1 s2 of
    Seq0 Seq0 => true
  | (Adds x1 s1') (Adds x2 s2') => (andb x1 =d x2 (eqseq s1' s2'))
  | _ _ => false
  end.

Lemma eqseqPx : (reflect_eq eqseq).
Proof.
Move; Elim=> [|x1 s1 Hrec] [|x2 s2]; First [By Constructor | Simpl].
Case: (x1 =P x2) => [[ ] | Hx]; RightBy Right; Move=> E; Case Hx; Injection E.
By Apply: (iffP (Hrec ?)) => [[]|E]; RightBy Injection E.
Qed.

Canonical Structure seqData := (DataSet eqseqPx).

Lemma eqseqE : eqseq =1 (!eqd seqData). Proof. Done. Qed.

Lemma eqseq_adds : (x1, x2 : d; s1, s2 : seq)
  ((Adds x1 s1) =d (Adds x2 s2)) = (andb x1 =d x2 s1 =d s2).
Proof. Done. Qed.

(* Factories *)

Syntactic Definition seq0 := Seq0. (* repeated after the end of section *)
Definition seq1 [x1 : d] : seq := (Adds x1 Seq0).
Definition seq2 [x1, x2 : d] : seq := (Adds x1 (seq1 x2)).
Definition seq3 [x1, x2, x3 : d] : seq := (Adds x1 (seq2 x2 x3)).
Definition seq4 [x1, x2, x3, x4 : d] : seq := (Adds x1 (seq3 x2 x3 x4)).
Definition addsn [n : nat; x : d] : seq -> seq := (iter n (Adds x)).
Definition seqn [n : nat; x : d] : seq := (addsn n x Seq0).

Lemma seq1I : (x1 : d) (Adds x1 seq0) = (seq1 x1). Proof. Done. Qed.
Lemma seq2I : (x1, x2 : d) (Adds x1 (seq1 x2)) = (seq2 x1 x2). Proof. Done. Qed.
Lemma seq3I : (x1, x2, x3 : d) (Adds x1 (seq2 x2 x3)) = (seq3 x1 x2 x3).
Proof. Done. Qed.
Lemma seq4I : (x1, x2, x3, x4 : d) (Adds x1 (seq3 x2 x3 x4)) = (seq4 x1 x2 x3 x4).
Proof. Done. Qed.

Lemma size_addsn : (n : nat; x : d; s : seq)
  (size (addsn n x s)) = (addn n (size s)).
Proof. By Move=> n x p; Elim: n => [|n Hrec] //=; Rewrite Hrec. Qed.

Lemma size_seqn : (n : nat; x : d) (size (seqn n x)) = n.
Proof. By Move=> *; Rewrite: /seqn size_addsn addn0. Qed.

(* Making a sequence of a specific length, using indexes to compute items. *)

Section MakeSeq.

Variable f : nat -> d.

Fixpoint mkseq_rec [i, n : nat] : seq :=
  if n is (S n') then (Adds (f i) (mkseq_rec (S i) n')) else Seq0.

Definition mkseq : nat -> seq := (mkseq_rec (0)).

Lemma size_mkseq : (n : nat) (size (mkseq n)) = n.
Proof. By Rewrite: /mkseq; Move=> n; Elim: n (0) => //= *; Congr S. Qed.

End MakeSeq.

Lemma eq_mkseq : (f, g : nat -> d) f =1 g -> (mkseq f) =1 (mkseq g).
Proof.
Move=> f g Efg n; Rewrite: /mkseq; Elim: n (0) => //= [n Hrec] i.
By Rewrite Efg; Congr Adds.
Qed.

(* n-ary, dependently typed constructor. *)

Fixpoint nseq_type [n : nat] : Set :=
  if n is (S n') then (d -> (nseq_type n')) else seq.

Fixpoint nseq_rec [f : seq -> seq; n : nat] : (nseq_type n) :=
  <nseq_type>Cases n of
    (0) => (f seq0)
  | (S n') => [x](nseq_rec [s](f (Adds x s)) n')
  end.

Definition nseq : (n : nat) (nseq_type n) := (nseq_rec [s]s).

(* Sequence catenation `cat'.                                                *)

Fixpoint cat [s1 : seq] : seq -> seq :=
  [s2]if s1 is (Adds x s1') then (Adds x (cat s1' s2)) else s2.

Lemma cat0s : (s : seq) (cat seq0 s) = s. Proof. Done. Qed.

Lemma cat1s : (x : d; s : seq) (cat (seq1 x) s) = (Adds x s).
Proof. Done. Qed.

Lemma cat_adds : (x : d; s1, s2 : seq)
  (cat (Adds x s1) s2) = (Adds x (cat s1 s2)).
Proof. Done. Qed.

Lemma cat_seqn : (n : nat; x : d; s : seq) (cat (seqn n x) s) = (addsn n x s).
Proof. By Elim=> //= *; Congr Adds. Qed.

Lemma cats0 : (s : seq) (cat s seq0) = s.
Proof. By Elim=> [|x s Hrec] //=; Rewrite Hrec. Qed.

Lemma catA : (s1, s2, s3 : seq)
  (cat s1 (cat s2 s3)) = (cat (cat s1 s2) s3).
Proof. By Move=> s1 s2 s3; Elim: s1 => [|x s1 Hrec] //=; Rewrite Hrec. Qed.

Lemma size_cat : (s1, s2 : seq)
  (size (cat s1 s2)) = (addn (size s1) (size s2)).
Proof. By Move=> s1 s2; Elim: s1 => [|x s1 Hrec] //=; Rewrite Hrec. Qed.

Lemma eqseq_cat : (s1, s2 : seq) (size s1) = (size s2) ->
  (s3, s4 : seq) ((cat s1 s3) =d (cat s2 s4)) = (andb s1 =d s2 s3 =d s4).
Proof.
Move=> s1 s2 Hs12 s3 s4; Elim: s1 s2 Hs12 => [|x1 s1 Hrec] [|x2 s2] //=.
By Injection=> Hs12; Rewrite: !eqseq_adds -andbA Hrec.
Qed.

(* last, belast, add_last, and last induction. *)

Fixpoint add_last [s : seq] : d -> seq :=
  if s is (Adds x s') then [z](Adds x (add_last s' z)) else seq1.

Lemma add_last_adds : (x : d; s : seq; z : d)
  (add_last (Adds x s) z) = (Adds x (add_last s z)).
Proof. Done. Qed.

Lemma eqseq_add_last : (s1, s2 : seq; x1, x2 : d)
  ((add_last s1 x1) =d (add_last s2 x2)) = (andb s1 =d s2 x1 =d x2).
Proof.
By Move=> s1 s2 x1 x2; Elim: s1 s2 => [|y1 s1 Hrec] [|y2 s2];
   Rewrite: /= /seq1 ?eqseq_adds ?andbT ?andbF // 1?Hrec 1?andbA //;
   Rewrite andbC; [Case s2 | Case s1].
Qed.

Lemma cats1 : (s : seq; z : d) (cat s (seq1 z)) = (add_last s z).
Proof. By Move=> s z; Elim: s => [|x s Hrec] //=; Rewrite Hrec. Qed.

Fixpoint last [x : d; s : seq] : d :=
  if s is (Adds x' s') then (last x' s') else x.

Fixpoint belast [x : d; s : seq] : seq :=
  if s is (Adds x' s') then (Adds x (belast x' s')) else seq0.

Lemma lastI : (x : d; s : seq) (Adds x s) = (add_last (belast x s) (last x s)).
Proof. By Move=> x s; Elim: s x => [|y s Hrec] x //=; Rewrite Hrec. Qed.

Lemma last_adds : (x, y : d; s : seq) (last x (Adds y s)) = (last y s).
Proof. Done. Qed.

Lemma size_add_last : (s : seq; x : d)
  (size (add_last s x)) = (S (size s)).
Proof. By Move=> *; Rewrite: -cats1 size_cat addnC. Qed.

Lemma size_belast : (x : d; s : seq) (size (belast x s)) = (size s).
Proof. By Move=> x s;  Elim: s x => [|y s Hrec] x //=; Rewrite Hrec. Qed.

Lemma last_cat : (x : d; s1, s2 : seq)
  (last x (cat s1 s2)) = (last (last x s1) s2).
Proof. By Move=> x s1 s2; Elim: s1 x => [|y s1 Hrec] x //=; Rewrite Hrec. Qed.

Lemma last_add_last : (x : d; s : seq; z : d) (last x (add_last s z)) = z.
Proof. By Move=> x s z; Rewrite: -cats1 last_cat. Qed.

Lemma belast_cat : (x : d; s1, s2 : seq)
 (belast x (cat s1 s2)) = (cat (belast x s1) (belast (last x s1) s2)).
Proof. By Move=> x s1 s2; Elim: s1 x => [|y s1 Hrec] x //=; Rewrite Hrec. Qed.

Lemma belast_add_last : (x : d; s : seq; z : d)
  (belast x (add_last s z)) = (Adds x s).
Proof. By Move=> *; Rewrite: lastI -!cats1 belast_cat. Qed.

Lemma cat_add_last : (x : d; s1, s2 : seq)
  (cat (add_last s1 x) s2) = (cat s1 (Adds x s2)).
Proof. By Move=> *; Rewrite: -cats1 -catA. Qed.

Lemma add_last_cat : (x : d; s1, s2 : seq)
  (add_last (cat s1 s2) x) = (cat s1 (add_last s2 x)).
Proof. By Move=> *; Rewrite: -!cats1 catA. Qed.

Inductive last_spec : seq -> Set :=
  LastSeq0 : (last_spec seq0)
| LastAdd : (s : seq; x : d) (last_spec (add_last s x)).

Lemma lastP : (s : seq) (last_spec s).
Proof. Move=> [|x s]; [Left | Rewrite lastI; Right]. Qed.

Lemma last_ind : (P : seq -> Type)
  (Hseq0 : (P seq0); Hlast : (s : seq; x : d) (P s) -> (P (add_last s x)))
  (s : seq) (P s).
Proof.
Move=> P Hseq0 Hlast s; Rewrite: -(cat0s s).
Elim: s (seq0) Hseq0 => [|x s2 Hrec] s1 Hs1; LeftBy Rewrite cats0.
By Rewrite: -cat_add_last; Auto.
Qed.

(* Sequence indexing. *)

Fixpoint sub [s : seq; n : nat] : d :=
  if s is (Adds x s') then (if n is (S n') then (sub s' n') else x) else x0.

Lemma sub0 : (s : seq) (sub s (0)) = (head s). Proof. Done. Qed.

Lemma sub_default : (s : seq; n : nat) (leq (size s) n) -> (sub s n) = x0.
Proof. By Elim=> [|x s Hrec] [|n]; Try Exact (Hrec n). Qed.

Lemma sub_last : (x : d; s : seq) (sub (Adds x s) (size s)) = (last x s).
Proof. By Move=> x s; Elim: s x => [|y s Hrec] x /=. Qed.

Lemma sub_behead : (s : seq; n : nat) (sub (behead s) n) = (sub s (S n)).
Proof. By Move=> [|x s] [|n]. Qed.

Lemma sub_cat : (s1, s2 : seq; n : nat) 
  (sub (cat s1 s2) n) = [n1 := (size s1)]
    if (ltn n n1) then (sub s1 n) else (sub s2 (subn n n1)).
Proof.
By Move=> s1 s2 n; Elim: s1 n => [|x s1 Hrec] [|n]; Try Exact (Hrec n).
Qed.

Lemma sub_add_last : (s : seq; x : d; n : nat)
  (sub (add_last s x) n) =
     (if (ltn n (size s)) then (sub s n) else
      if n =d (size s) then x else x0).
Proof.
Move=> s x n; Rewrite: -cats1 sub_cat eqn_leq andbC ltnNge -(eqn_sub0 n) /=.
By Case (leq (size s) n); LeftBy Case: (subn n (size s)) => [|[|m]].
Qed.

Lemma sub_mkseq : (f : nat -> d; n, i : nat) (ltn i n) ->
  (sub (mkseq f n) i) = (f i).
Proof.
Move=> f n i; Rewrite: /mkseq -{3 i}addn0; Elim: n (0) i => // [n Hrec] j.
Case=> //= [i]; Rewrite: addSnnS; Apply: Hrec.
Qed.

Lemma mkseq_sub : (s : seq) (mkseq (sub s) (size s)) = s.
Proof.
Move=> s; Step Ef: (i : nat) (sub s (addn (0) i)) = (sub s i) By Done.
Move: {1 3}(sub s) Ef => f; Rewrite: /mkseq.
Elim: s (0) => //= [x s Hrec] i Ef /=; Rewrite: -{1 i}addn0 Ef; Congr Adds.
By Apply: Hrec => [j]; Rewrite: addSnnS Ef.
Qed.

(* mem, find, count, has, all, and index; mem is a coercion to set. *)

Fixpoint mem [s : seq] : (set d) :=
  if s is (Adds x s') then (setU1 x (mem s')) else set0.

Coercion mem : seq >-> set.

Lemma mem_adds : (x : d; s : seq) (Adds x s) =1 (setU1 x s). Proof. Done. Qed.

Lemma mem_seq1 : (x : d) (seq1 x) =1 (set1 x).
Proof. By Move=> x1 y; Rewrite: /= /setU1 orbF. Qed.

Lemma mem_seq2 : (x1, x2 : d) (seq2 x1 x2) =1 (set2 x1 x2).
Proof. By Move=> x1 x2 y; Rewrite: /= /setU1 orbF. Qed.

Lemma mem_seq3 : (x1, x2, x3 : d) (seq3 x1 x2 x3) =1 (set3 x1 x2 x3).
Proof. By Move=> x1 x2 x3 y; Rewrite: /= /setU1 orbF. Qed.

Lemma mem_seq4 : (x1, x2, x3, x4 : d) (seq4 x1 x2 x3 x4) =1 (set4 x1 x2 x3 x4).
Proof. By Move=> x1 x2 x3 x4 y; Rewrite: /= /setU1 orbF. Qed.

Lemma mem_cat : (s1, s2 : seq) (cat s1 s2) =1 (setU s1 s2).
Proof.
Move=> s1 s2 y; Elim: s1 => [| x s1 Hrec] //=.
By Rewrite: /setU /setU1 -orbA Hrec.
Qed.

Lemma mem_add_last : (s : seq; x : d) (add_last s x) =1 (Adds x s).
Proof. By Move=> s x y; Rewrite: -cats1 mem_cat /setU mem_seq1 orbC. Qed.

Lemma mem_last : (x : d; s : seq) (Adds x s (last x s)).
Proof. By Move=> *; Rewrite: lastI mem_add_last /= setU11. Qed.

Lemma mem_lastU : (x : d; s : seq) (setU1 x s (last x s)).
Proof. Exact mem_last. Qed.

Lemma mem_behead : (s : seq; y : d) (behead s y) -> (s y).
Proof. Move=> [|x s] //; Exact (!setU1r d x s). Qed.

Lemma mem_belast : (x : d; s : seq; y : d) (belast x s y) -> (Adds x s y).
Proof. By Move=> *; Rewrite: lastI mem_add_last /= setU1r. Qed.

Lemma mem_sub : (s : seq; n : nat) (ltn n (size s)) -> (s (sub s n)).
Proof.
Elim=> [|x s Hrec] // [|n] /=; LeftBy Rewrite setU11.
Exact [H](setU1r ? (Hrec ? H)).
Qed.

Section SeqFind.

Variable a : (set d).

Fixpoint find [s : seq] : nat :=
  if s is (Adds x s') then (if (a x) then (0) else (S (find s'))) else (0).

Fixpoint filter [s : seq] : seq :=
  if s is (Adds x s') then (if (a x) then (Adds x) else id (filter s')) else seq0.

Fixpoint count [s : seq] : nat :=
  if s is (Adds x s') then (addn (a x) (count s')) else (0).

Fixpoint has [s : seq] : bool :=
  if s is (Adds x s') then (orb (a x) (has s')) else false.

Fixpoint all [s : seq] : bool :=
  if s is (Adds x s') then (andb (a x) (all s')) else true.

Lemma count_filter : (s : seq) (count s) = (size (filter s)).
Proof. By Elim=> [|x s Hrec] //=; Rewrite Hrec; Case (a x). Qed.

Lemma has_count : (s : seq) (has s) = (ltn (0) (count s)).
Proof. By Elim=> [|x s Hrec] //=; Rewrite Hrec; Case (a x). Qed.

Lemma count_size : (s : seq) (leq (count s) (size s)).
Proof. By Elim=> [|x s Hrec] //=; Case (a x); RightBy Apply ltnW. Qed.

Lemma all_count : (s : seq) (all s) = ((count s) =d (size s)).
Proof.
Elim=> [|x s Hrec] //=; Case: (a x) => [|] //=.
By Rewrite: add0n eqn_leq andbC ltnNge count_size.
Qed.

Lemma has_filter : (s : seq)
  (has s) = (if (filter s) is Seq0 then false else true).
Proof. By Move=> s; Rewrite: has_count count_filter; Case (filter s). Qed.

Lemma all_filterPx : (s : seq) (reflect (filter s) = s (all s)).
Proof.
Move=> s; Apply introP.
  By Elim: s => [|x s Hrec] //=; Case/andP => [Ha Hs]; Rewrite: Ha Hrec.
By Rewrite: all_count count_filter; Move=> H H'; Rewrite: H' set11 in H.
Qed.

Lemma has_find : (s : seq) (has s) = (ltn (find s) (size s)).
Proof. By Elim=> [|x s Hrec] //=; Case (a x); Rewrite: ?leqnn. Qed.

Lemma find_size : (s : seq) (leq (find s) (size s)).
Proof. By Elim => [|x s Hrec] //=; Case (a x). Qed.

Lemma find_cat : (s1, s2 : seq)
  (find (cat s1 s2)) =
    (if (has s1) then (find s1) else (addn (size s1) (find s2))).
Proof.
Move=> s1 s2; Elim: s1 => [|x s1 Hrec] //=; Case: (a x) => [|] //.
By Rewrite: Hrec (fun_if S).
Qed.

Lemma has_seq0 : (has seq0) = false. Proof. Done. Qed.

Lemma has_seq1 : (x : d) (has (seq1 x)) = (a x).
Proof. By Move=> *; Rewrite: /= orbF. Qed.

Lemma has_seqb : (b : bool; x : d) (has (seqn b x)) = (andb b (a x)).
Proof. By Case=> // *; Rewrite: /= orbF. Qed.

Lemma all_seq0 : (all seq0) = true. Proof. Done. Qed.

Lemma all_seq1 : (x : d) (all (seq1 x)) = (a x).
Proof. By Move=> *; Rewrite: /= andbT. Qed.

Lemma sub_find : (s : seq) (has s) -> (a (sub s (find s))).
Proof. By Elim=> [|x s Hrec] //=; Case Hx: (a x). Qed.

Lemma before_find : (s : seq; i : nat)
  (ltn i (find s)) -> (a (sub s i)) = false.
Proof.
Move=> s i; Elim: s i => [|x s Hrec] //=; Case Hx: (a x) => [|] // [|i] //.
Exact (Hrec i).
Qed.

Lemma hasPx : (s : seq) (reflect (EX x | (s x) & (a x)) (has s)).
Proof.
Elim=> [|x s Hrec] /=; LeftBy Right; Move=> [x Hx _].
Case Hax: (a x); LeftBy Left; Exists x; LeftBy Rewrite: /= setU11.
Apply: (iffP Hrec) => [[y Hy Hay]]; (Exists y; RightDone).
  Exact (setU1r x Hy).
By Case: (setU1P Hy) => [Dx|Hx] //; Rewrite: Dx Hay in Hax.
Qed.

Lemma hasPnx : (s : seq) (reflect ((x : d) (s x) -> (negb (a x))) (negb (has s))).
Proof.
Move=> s; Apply: (iffP idP) => [Hs x Hx | Hs].
  By Apply/negPn => [Hax]; Case: (elimN (hasPx ?) Hs); Exists x.
By Apply/(hasPx ?) => [[x Hx Hax]]; Case (negP (Hs ? Hx)).
Qed.

Lemma allPx : (s : seq) (reflect ((x : d) (s x) -> (a x)) (all s)).
Proof.
Elim=> [|x s Hrec]; LeftBy Left.
Rewrite: /= andbC; Case: Hrec => [Hrec | Hrec]; Simpl.
  Apply: (iffP idP) => [Hx y | H]; RightBy Apply H; Apply setU11.
  By Case/setU1P => [[]|Hy]; Auto.
By Right; Move=> H; Case Hrec; Move=> y Hy; Apply H; Apply setU1r.
Qed.

Lemma allPnx : (s : seq) (reflect (EX x | (s x) & (negb (a x))) (negb (all s))).
Proof.
Elim=> [|x s Hrec]; LeftBy Right; Move=> [x Hx _].
Rewrite: /= andbC negb_andb; Case: Hrec => [Hrec | Hrec]; Simpl.
  By Left; Case: Hrec => [y Hy Hay]; Exists y; LeftBy Apply setU1r.
Case Hax: (a x); Constructor; RightBy Exists x; Rewrite: ?Hax ?setU11.
Move=> [y Hy Hay]; Case Hrec; Exists y; RightDone.
By Case/setU1P: Hy Hay => [[]|Hy]; LeftBy Rewrite: Hax.
Qed.

Lemma filter_cat : (s1, s2 : seq)
  (filter (cat s1 s2)) = (cat (filter s1) (filter s2)).
Proof.
By Move=> s1 s2; Elim: s1 => [|x s1 Hrec] //=; Rewrite: Hrec; Case (a x).
Qed.

Lemma filter_add_last : (s : seq; x : d)
  (filter (add_last s x)) =
    (if (a x) then (add_last (filter s) x) else (filter s)).
Proof.
By Move=> s x; Rewrite: -!cats1 filter_cat /=; Case (a x); Rewrite: /= ?cats0.
Qed.

Lemma mem_filter : (s : seq) (filter s) =1 (setI a s).
Proof.
Move=> s y; Rewrite: /setI andbC; Elim: s => [|x s Hrec] //=.
Rewrite: if_arg /id (fun_if [s' : seq](s' y)) /= /setU1 Hrec.
By Case: (x =P y) => [[]|_]; Case (a x); Rewrite: /= ?andbF.
Qed.

Lemma count_cat : (s1, s2 : seq)
  (count (cat s1 s2)) = (addn (count s1) (count s2)).
Proof. By Move=> *; Rewrite: !count_filter filter_cat size_cat. Qed.

Lemma has_cat : (s1, s2 : seq) (has (cat s1 s2)) = (orb (has s1) (has s2)).
Proof. By Move=> s1 s2; Elim: s1 => [|x s1 Hrec] //=; Rewrite: Hrec orbA. Qed.

Lemma has_add_last : (s : seq; x : d) (has (add_last s x)) = (orb (a x) (has s)).
Proof. By Move=> *; Rewrite: -cats1 has_cat has_seq1 orbC. Qed.

Lemma all_cat : (s1, s2 : seq) (all (cat s1 s2)) = (andb (all s1) (all s2)).
Proof. By Move=> s1 s2; Elim: s1 => [|x s1 Hrec] //=; Rewrite: Hrec andbA. Qed.

Lemma all_add_last : (s : seq; x : d) (all (add_last s x)) = (andb (a x) (all s)).
Proof. By Move=> *; Rewrite: -cats1 all_cat all_seq1 andbC. Qed.

End SeqFind.

Lemma eq_find : (a1, a2 : (set d)) a1 =1 a2 -> (find a1) =1 (find a2).
Proof. By Move=> a1 a2 Ea; Elim=> [|x s Hrec] //=; Rewrite: Ea Hrec. Qed.

Lemma eq_filter : (a1, a2 : (set d)) a1 =1 a2 -> (filter a1) =1 (filter a2).
Proof. By Move=> a1 a2 Ea; Elim=> [|x s Hrec] //=; Rewrite: Ea Hrec. Qed.

Lemma eq_count : (a1, a2 : (set d)) a1 =1 a2 -> (count a1) =1 (count a2).
Proof. By Move=> a1 a2 Ea s; Rewrite: !count_filter (eq_filter Ea). Qed.

Lemma eq_has : (a1, a2 : (set d)) a1 =1 a2 -> (has a1) =1 (has a2).
Proof. By Move=> a1 a2 Ea s; Rewrite: !has_count (eq_count Ea). Qed.

Lemma eq_has_r : (s1, s2 : seq) s1 =1 s2 -> (a : (set d)) (has a s1) = (has a s2).
Proof.
Move=> s1 s2 Es12 a; Apply/(hasPx ? ?)/(hasPx ? ?) => [[x Hx Hax]];
  By Exists x; Rewrite: // ?Es12 // -Es12.
Qed.

Lemma eq_all : (a1, a2 : (set d)) a1 =1 a2 -> (all a1) =1 (all a2).
Proof. By Move=> a1 a2 Ea s; Rewrite: !all_count (eq_count Ea). Qed.

Lemma eq_all_r : (s1, s2 : seq) s1 =1 s2 -> (a : (set d)) (all a s1) = (all a s2).
Proof.
By Move=> s1 s2 Es12 a; Apply/(allPx ? ?)/(allPx ? ?) => [Hs x Hx | Hs x Hx];
  Apply Hs; Rewrite: Es12 in Hx *.
Qed.

Lemma filter_set0 : (s : seq) (filter set0 s) = seq0.
Proof. By Elim. Qed.

Lemma filter_setA : (s : seq) (filter d s) = s.
Proof. By Elim=> [|x s Hrec] //=; Rewrite: Hrec. Qed.

Lemma filter_setI : (a1, a2 : (set d); s : seq)
  (filter (setI a1 a2) s) = (filter a1 (filter a2 s)).
Proof.
Move=> a1 a2; Elim => [|x s Hrec] //=; Rewrite: /= {1}/setI andbC Hrec.
By Case: (a2 x) => [|] //=; Case (a1 x).
Qed.

Lemma count_set0 : (s : seq) (count set0 s) = (0).
Proof. By Move=> s; Rewrite: count_filter filter_set0. Qed.

Lemma count_setA : (s : seq) (count d s) = (size s).
Proof. By Move=> s; Rewrite: count_filter filter_setA. Qed.

Lemma count_setUI : (a1, a2 : (set d); s : seq)
  (addn (count (setU a1 a2) s) (count (setI a1 a2) s))
    = (addn (count a1 s) (count a2 s)).
Proof.
Move=> a1 a2; Elim => [|x s Hrec] //=; Rewrite: /= addnCA -addnA Hrec addnA addnC.
By Rewrite: -!addnA /setU /setI; Do 2 NatCongr; Case (a1 x); Case (a2 x).
Qed.

Lemma count_setC : (a : (set d); s : seq)
  (addn (count a s) (count (setC a) s)) = (size s).
Proof.
Move=> a; Elim=> [|x s Hrec] //=; Rewrite: -!addnA (addnCA (count a s)) Hrec /=.
By Rewrite: /setC; Case (a x).
Qed.

Lemma has_set0 : (s : seq) (has set0 s) = false.
Proof. By Move=> s; Rewrite: has_count count_set0. Qed.

Lemma has_setA : (s : seq) (has d s) = (ltn (0) (size s)).
Proof. By Move=> s; Rewrite: has_count count_setA. Qed.

Lemma has_setC : (a : (set d); s : seq) (has (setC a) s) = (negb (all a s)).
Proof. Move=> a s; Exact (sameP (hasPx (setC a) ?) (allPnx ? ?)). Qed.

Lemma has_setU : (a1, a2 : (set d); s : seq)
  (has (setU a1 a2) s) = (orb (has a1 s) (has a2 s)).
Proof.
Move=> a1 a2; Elim => [|x s Hrec] //=; Rewrite: Hrec /setU -!orbA.
By Repeat BoolCongr.
Qed.

Lemma all_set0 : (s : seq) (all set0 s) = ((size s) =d (0)).
Proof. By Move=> *; Rewrite: all_count count_set0 eqd_sym. Qed.

Lemma all_setA : (s : seq) (all d s) = true.
Proof. By Move=> *; Rewrite: all_count count_setA set11. Qed.

Lemma all_setC : (a : (set d); s : seq) (all (setC a) s) = (negb (has a s)).
Proof. Move=> a s; Exact (sameP (allPx (setC a) ?) (hasPnx ? ?)). Qed.

Lemma all_setI : (a1, a2 : (set d); s : seq)
   (all (setI a1 a2) s) = (andb (all a1 s) (all a2 s)).
Proof.
Move=> a1 a2 s; Apply (monic_inj 1!bool negb_elim).
Rewrite: negb_andb -!has_setC -has_setU; Apply: eq_has => [x].
By Rewrite: /setC /setI negb_andb.
Qed.

Lemma has_sym : (s1, s2 : seq) (has s1 s2) = (has s2 s1).
Proof. By Move=> *; Apply/(hasPx ? ?)/(hasPx ? ?) => [] [x H H']; Exists x. Qed.

Lemma has_set1 : (x : d; s : seq) (has (set1 x) s) = (s x).
Proof. By Move=> *; Rewrite: -(eq_has (mem_seq1 x)) has_sym /= orbF. Qed.

(* Duplicate-freenes. *)

Fixpoint uniq [s : seq] : bool :=
  if s is (Adds x s') then (andb (negb (s' x)) (uniq s')) else true.

Lemma uniq_adds : (x : d; s : seq)
  (uniq (Adds x s)) = (andb (negb (s x)) (uniq s)).
Proof. Done. Qed.

Lemma uniq_cat : (s1, s2 : seq)
  (uniq (cat s1 s2)) = (andb (uniq s1) (andb (negb (has s1 s2)) (uniq s2))).
Proof.
Move=> s1 s2; Elim: s1 => [|x s1 Hrec]; LeftBy Rewrite: /= has_set0.
Rewrite: has_sym /= mem_cat /setU !negb_orb has_sym Hrec -!andbA.
By Repeat BoolCongr.
Qed.

Lemma uniq_catC : (s1, s2 : seq) (uniq (cat s1 s2)) = (uniq (cat s2 s1)).
Proof. By Move=> *; Rewrite: !uniq_cat has_sym andbCA andbA andbC. Qed.

Lemma uniq_catCA : (s1, s2, s3 : seq)
  (uniq (cat s1 (cat s2 s3))) = (uniq (cat s2 (cat s1 s3))).
Proof.
Move=> *.
By Rewrite: !catA -!(uniq_catC s3) !(uniq_cat s3) uniq_catC !has_cat orbC.
Qed.

Lemma uniq_add_last : (s : seq; x : d)
  (uniq (add_last s x)) = (andb (negb (s x)) (uniq s)).
Proof. By Move=> *; Rewrite: -cats1 uniq_catC. Qed.

Lemma uniq_filter : (s : seq; a : (set d)) (uniq s) -> (uniq (filter a s)).
Proof.
Move=> s a; Elim: s => [|x s Hrec] //=; Case/andP => [Hx Hs]; Case (a x); Auto.
By Rewrite: /= mem_filter /setI (negbE Hx) andbF; Auto.
Qed.

Definition index [x : d] := (find (set1 x)).

Lemma index_size : (x : d; s : seq) (leq (index x s) (size s)).
Proof. By Move=> *; Rewrite: /index find_size. Qed.

Lemma index_mem : (x : d; s : seq) (ltn (index x s) (size s)) = (s x).
Proof. By Move=> *; Rewrite: -has_set1 has_find. Qed.

Lemma sub_index : (x : d; s : seq) (s x) -> (sub s (index x s)) = x.
Proof. By Move=> *; Apply: (esym (eqP (sub_find ?))); Rewrite has_set1. Qed.

Lemma subPx : (s : seq; x : d)
  (reflect (EX i | (ltn i (size s)) & (sub s i) = x) (s x)).
Proof.
Move=> s x; Apply: (iffP idP) => [|[n Hn []]]; RightBy Apply mem_sub.
By Exists (index x s); [Rewrite index_mem | Apply sub_index].
Qed.

Lemma has_subPx : (a : (set d); s : seq)
  (reflect (EX i | (ltn i (size s)) & (a (sub s i))) (has a s)).
Proof.
Move=> a s; Apply: (iffP (hasPx ? ?)) => [[x Hx Hax] | [i Hi Hai]].
  By Case/(subPx ? ?): Hx Hax => [i Hi []]; Exists i.
By Exists (sub s i); LeftBy Apply mem_sub.
Qed.

Lemma all_subPx : (a : (set d); s : seq)
  (reflect ((i : nat) (ltn i (size s)) -> (a (sub s i))) (all a s)).
Proof.
Move=> a s; Apply: (iffP (allPx ? ?)) =>  [Hs i Hi |  Hs x].
  By Apply Hs; Apply mem_sub.
Case/(subPx ? ?) => [i Hi []]; Auto.
Qed.

Lemma index_cat : (x : d; s1, s2 : seq)
  (index x (cat s1 s2))
    = (if (s1 x) then (index x s1) else (addn (size s1) (index x s2))).
Proof. By Move=> x s1 s2; Rewrite: /index find_cat has_set1. Qed.

Lemma index_uniq : (i : nat; s : seq)
  (ltn i (size s)) -> (uniq s) -> (index (sub s i) s) = i.
Proof.
Move=> i s; Simpl; Elim: s i => [|x s Hrec] //= [|i]; Rewrite: /= ?set11 // ltnS.
Move=> Hi; Case/andP => [Hx Hs]; Rewrite: (Hrec i Hi Hs).
By Case: ((sub s i) =P x) Hx => [[]|_]; LeftBy Rewrite mem_sub.
Qed.

Lemma index_head : (x : d; s : seq) (index x (Adds x s)) = (0).
Proof. By Move=> *; Rewrite: /= set11. Qed.

Lemma index_last : (x : d; s : seq)
  (uniq (Adds x s)) -> (index (last x s) (Adds x s)) = (size s).
Proof. By Move=> *; Rewrite: -sub_last index_uniq //= leqnn. Qed.

(* Surgery: drop, take, rot, rotr.                                              *)

Fixpoint drop [n : nat; s : seq] : seq :=
  Cases s n of
    (Adds _ s') (S n') => (drop n' s')
  |          _      _  => s
  end.

Lemma drop_behead : (drop n0) =1 (iter n0 behead).
Proof. By Elim: {}n0 => [|n Hrec] [|x s] //; Rewrite: -iter_f -Hrec. Qed.

Lemma drop0 : (s : seq) (drop (0) s) = s. Proof. By Case. Qed.

Lemma drop1 : (drop (1)) =1 behead. Proof. By Move=> [|x [|y s]]. Qed.

Lemma drop_oversize : (n : nat; s : seq) (leq (size s) n) -> (drop n s) = seq0.
Proof. By Elim=> [|n Hrec] [|x s]; Try Exact (Hrec s). Qed.

Lemma drop_size : (s : seq) (drop (size s) s) = seq0.
Proof. Exact [s](drop_oversize (leqnn ?)). Qed.

Lemma drop_adds : (x : d; s : seq)
  (drop n0 (Adds x s)) = (Cases n0 of (S n) => (drop n s) | _ => (Adds x s) end).
Proof. Done. Qed.

Lemma size_drop : (s : seq) (size (drop n0 s)) = (subn (size s) n0).
Proof. By Move=> s; Elim: s {}n0 => [|x s Hrec] [|n]; Try Exact (Hrec n). Qed.

Lemma drop_cat : (s1, s2 : seq)
  (drop n0 (cat s1 s2)) =
    (if (ltn n0 (size s1)) then (cat (drop n0 s1) s2)
                           else (drop (subn n0 (size s1)) s2)).
Proof.
By Move=> s1 s2; Elim: s1 (n0) => [|x s1 Hrec] [|n]; Try Exact (Hrec n).
Qed.

Lemma drop_size_cat : (s1, s2 : seq) (drop (size s1) (cat s1 s2)) = s2.
Proof. By Move=> s1 s2; Elim: s1 => [|x s1 Hrec] //=; Rewrite drop0. Qed.

Fixpoint take [n : nat; s : seq] : seq :=
  Cases s n of
    (Adds x s') (S n')  => (Adds x (take n' s'))
  |         _      _    => seq0
  end.

Lemma take0 : (s : seq) (take (0) s) = seq0. Proof. By Move=> [|x s]. Qed.

Lemma take_oversize : (n : nat; s : seq) (leq (size s) n) -> (take n s) = s.
Proof. By Elim=> [|n Hrec] [|x s] Hsn; Try (Congr Adds; Apply: Hrec). Qed.

Lemma take_size : (s : seq) (take (size s) s) = s.
Proof. Exact [s](take_oversize (leqnn ?)). Qed.

Lemma take_adds : (x : d; s : seq)
  (take n0 (Adds x s)) = (if n0 is (S n) then (Adds x (take n s)) else seq0).
Proof. Done. Qed.

Lemma drop_add_last : (s : seq; Hn : (leq n0 (size s)); x : d)
  (drop n0 (add_last s x)) = (add_last (drop n0 s) x).
Proof. By Move=> s; Elim: s (n0) => [|y s Hrec] [|n]; Try Exact (Hrec n). Qed.

Lemma cat_take_drop : (s : seq) (cat (take n0 s) (drop n0 s)) = s.
Proof.
By Move=> s; Elim: s (n0) => [|x s Hrec] [|n]; Try Exact (congr ? (Hrec n)).
Qed.

Lemma size_takel : (s : seq) (leq n0 (size s)) -> (size (take n0 s)) = n0.
Proof.
Move=> s Hn0; Apply: (addn_injr (etrans ? (esym (leq_add_sub Hn0)))).
By Rewrite: -size_drop -size_cat cat_take_drop.
Qed.

Lemma size_take : (s : seq)
  (size (take n0 s)) = (if (ltn n0 (size s)) then n0 else (size s)).
Proof.
Move=> s; Case: (ltnP n0 (size s)); RightBy Move=> *; Rewrite: take_oversize.
By Move=> *; Apply size_takel; Apply ltnW.
Qed.

Lemma take_cat : (s1, s2 : seq)
  (take n0 (cat s1 s2)) =
    (if (ltn n0 (size s1)) then (take n0 s1) else
    (cat s1 (take (subn n0 (size s1)) s2))).
Proof.
Move=> s1 s2; Elim: s1 (n0) => [|x s1 Hrec] [|n] //=.
By Rewrite: ltnS subSS  -(fun_if (Adds x)) -Hrec.
Qed.

Lemma take_size_cat : (s1, s2 : seq) (take (size s1) (cat s1 s2)) = s1.
Proof.
By Move=> s1 s2; Elim: s1 => [|x s1 Hrec]; [Case s2 | Exact (congr ? Hrec)].
Qed.

Lemma takel_cat : (s1: seq) (leq n0 (size s1)) ->
  (s2 : seq) (take n0 (cat s1 s2)) = (take n0 s1).
Proof.
Move=> s1 Hn0 s2; Rewrite: take_cat ltn_neqAle Hn0 andbT.
Case: (n0 =P (size s1)) => [Dn0 | _] //.
By Rewrite: Dn0 subnn take0 cats0 take_size.
Qed.

Lemma mem_take : (s : seq) (sub_set (take n0 s) s).
Proof. By Move=> s x Hx; Rewrite: -(cat_take_drop s) mem_cat /setU Hx. Qed.

Lemma mem_drop : (s : seq) (sub_set (drop n0 s) s).
Proof. By Move=> s x Hx; Rewrite: -(cat_take_drop s) mem_cat /setU Hx orbT. Qed.

Lemma sub_drop : (s : seq; i : nat) (sub (drop n0 s) i) = (sub s (addn n0 i)).
Proof.
Move=> s i; Case: (ltnP n0 (size s)) => [Hn | Hn].
  Rewrite: -{2 s}cat_take_drop sub_cat size_take Hn /=.
  By Rewrite: ltnNge leq_addr subn_addr.
Rewrite: !sub_default //; LeftBy Exact (leq_trans Hn (leq_addr ? ?)).
By Rewrite: -eqn_sub0 in Hn; Rewrite: size_drop (eqP Hn) leq0n.
Qed.

Lemma sub_take : (s : seq; i : nat)
  (ltn i n0) -> (sub (take n0 s) i) = (sub s i).
Proof.
Move=> s i Hi; Case Hn: (ltn n0 (size s)).
  By Rewrite: -{2 s}cat_take_drop sub_cat size_take Hn Hi.
By Rewrite: -{1 s}cats0 take_cat Hn /= cats0.
Qed.

(* drop_sub and take_sub below do NOT use the default n0, because the "n"  *)
(* can be inferred from the condition, whereas the sub default value x0    *)
(* will have to be given explicitly (and this will provide "d" as well).   *)

Lemma drop_sub : (n : nat; s : seq; Hn : (ltn n (size s)))
  (drop n s) = (Adds (sub s n) (drop (S n) s)).
Proof.
By Move=> n s; Elim: s n => [|x s Hrec] [|n] Hn //=; Rewrite: ?drop0 1?Hrec.
Qed.

Lemma take_sub : (n : nat; s : seq; Hn : (ltn n (size s)))
  (take (S n) s) = (add_last (take n s) (sub s n)).
Proof.
By Move=> n s; Elim: s n => [|x s Hrec] //= [|n] Hn /=; Rewrite: ?take0 -?Hrec.
Qed.

Lemma eq_from_sub : (s1, s2 : seq) (size s1) = (size s2) ->
  ((i : nat) (ltn i (size s1)) -> (sub s1 i) = (sub s2 i)) -> s1 = s2.
Proof.
Move=> s1 s2 Hs12 Es12; Rewrite: -{1 s2}take_size -{1 s1}take_size -Hs12.
Elim: {-2}(size s1) (leqnn (size s1)) => [|n Hrec] Hn; LeftBy Rewrite: !take0.
By Rewrite: (take_sub Hn) (Es12 ? Hn) (Hrec (ltnW Hn)) -take_sub // -Hs12.
Qed.

Definition rot [n : nat; s : seq] : seq := (cat (drop n s) (take n s)).

Lemma rot0 : (s : seq) (rot (0) s) = s.
Proof. By Move=> *; Rewrite: /rot drop0 take0 cats0. Qed.

Lemma size_rot : (s : seq) (size (rot n0 s)) = (size s).
Proof. By Move=> s; Rewrite: -{2 s}cat_take_drop /rot !size_cat addnC. Qed.

Lemma rot_oversize : (n : nat; s : seq) (leq (size s) n) -> (rot n s) = s.
Proof. By Move=> n s Hn; Rewrite: /rot (take_oversize Hn) (drop_oversize Hn). Qed.

Lemma rot_size : (s : seq) (rot (size s) s) = s.
Proof. Exact [s](rot_oversize (leqnn ?)). Qed.

Lemma mem_rot : (s : seq) (rot n0 s) =1 s.
Proof. By Move=> s x; Rewrite: -{2 s}cat_take_drop /rot !mem_cat /setU orbC. Qed.

Lemma has_rot : (s : seq; a : (set d)) (has a (rot n0 s)) = (has a s).
Proof. Exact [s](eq_has_r (mem_rot s)). Qed.

Lemma uniq_rot : (s : seq) (uniq (rot n0 s)) = (uniq s).
Proof. By Move=> *; Rewrite: /rot uniq_catC cat_take_drop. Qed.

Lemma rot_size_cat : (s1, s2 : seq) (rot (size s1) (cat s1 s2)) = (cat s2 s1).
Proof. By Move=> *; Rewrite: /rot take_size_cat drop_size_cat. Qed.

Definition rotr [n : nat; s : seq] : seq := (rot (subn (size s) n) s).

Lemma rotr_rot : (monic (rot n0) (rotr n0)).
Proof.
By Move=>s; Rewrite: /rotr size_rot -size_drop {2}/rot rot_size_cat cat_take_drop.
Qed.

Lemma rot_inj : (injective (rot n0)). Proof. Exact (monic_inj rotr_rot). Qed.

Lemma eqseq_rot : (s1, s2 : seq) ((rot n0 s1) =d (rot n0 s2)) = (s1 =d s2).
Proof. Apply: inj_eqd; Exact rot_inj. Qed.

Inductive rot_to_spec [s : seq; x : d] : Set :=
  RotToSpec : (i : nat; s' : seq) (rot i s) = (Adds x s') -> (rot_to_spec s x).

Lemma rot_to : (s : seq; x : d) (s x) -> (rot_to_spec s x).
Proof.
Move=> s x Hx; Pose i := (index x s); Exists i (cat (drop (S i) s) (take i s)).
Rewrite: ~/i /rot -cat_adds; Congr cat; Elim: s Hx => [|y s Hrec] //=.
By Rewrite: /setU1 eqd_sym; Case: (x =P y) => [[]|_]; [Rewrite drop0 | Auto].
Qed.

Lemma rot1_adds : (x : d; s : seq) (rot (1) (Adds x s)) = (add_last s x).
Proof. By Move=> *; Rewrite: /rot /= take0 drop0 -cats1. Qed.

(* (efficient) reversal *)

Fixpoint catrev [s2, s1 : seq] : seq :=
  if s1 is (Adds x s1') then (catrev (Adds x s2) s1') else s2.

Definition rev [s : seq] : seq := (nosimpl catrev seq0 s).

Lemma rev_add_last : (s : seq; x : d) (rev (add_last s x)) = (Adds x (rev s)).
Proof. By Move=> s x; Rewrite: /rev -cats1 /=; Elim: s {}seq0; Simpl. Qed.

Lemma rev_adds : (x : d; s : seq) (rev (Adds x s)) = (add_last (rev s) x).
Proof.
Move=> x; Elim/last_ind => [|s y Hrec] //.
By Rewrite: rev_add_last /= -Hrec -rev_add_last.
Qed.

Lemma size_rev : (s : seq) (size (rev s)) = (size s).
Proof. By Elim=> [|x s Hrec] //; Rewrite: rev_adds size_add_last Hrec. Qed.

Lemma rev_cat : (s1, s2 : seq) (rev (cat s1 s2)) = (cat (rev s2) (rev s1)).
Proof.
Move=> s1 s2; Elim: s1 => [|x s1 Hrec] /=; LeftBy Rewrite: cats0.
By Rewrite: !rev_adds Hrec -!cats1 catA.
Qed.

Lemma rev_rev : (monic rev rev).
Proof. By Elim=> [|x s Hrec] //=; Rewrite: rev_adds rev_add_last Hrec. Qed.

Lemma mem_rev : (s : seq) (rev s) =1 s.
Proof.
Move=> s y; Elim: s => [|x s Hrec] //.
By Rewrite: rev_adds /= mem_add_last /= /setU1 Hrec.
Qed.

Lemma uniq_rev : (s : seq) (uniq (rev s)) = (uniq s).
Proof.
Elim => [|x s Hrec] //.
By Rewrite: rev_adds -cats1 uniq_cat /= andbT andbC mem_rev orbF Hrec.
Qed.

Lemma sub_rev : (n : nat; s : seq) (ltn n (size s)) ->
 (sub (rev s) n) = (sub s (subn (size s) (S n))).
Proof.
Move=> n s; Elim/last_ind: s n => [|s x Hrec] n //.
Rewrite: rev_add_last size_add_last ltnS subSS -cats1 sub_cat /=.
Case: n => [|n] Hn; LeftBy Rewrite: subn0 ltnn subnn.
Rewrite: -{2 (size s)}(leq_add_sub Hn) addSnnS leq_addl /=; Auto.
Qed.

End Sequences.

Syntactic Definition seq0 := (Seq0 ?).

Syntactic Definition eqseqP      := eqseqPx      | 2.
Syntactic Definition all_filterP := all_filterPx | 2.
Syntactic Definition hasP        := hasPx        | 2.
Syntactic Definition hasPn       := hasPnx       | 2.
Syntactic Definition allP        := allPx        | 2.
Syntactic Definition allPn       := allPnx       | 2.
Syntactic Definition subP        := subPx        | 3.
Syntactic Definition has_subP    := has_subPx    | 3.
Syntactic Definition all_subP    := all_subPx    | 3.

(* Pretty-print of polymorphic constants must come before grammar *)

Syntax constr level 0:
  pp_seq_Adds [(Adds 1!$_)] -> ["Adds"]
| pp_seq_size [(size 1!$_)] -> ["size"]
| pp_seq_behead [(behead 1!$_)] -> ["behead"]
| pp_seq_cat [(cat 1!$_)] -> ["cat"]
| pp_seq_add_last [(add_last 1!$_)] -> ["add_last"]
| pp_seq_uniq [(uniq 1!$_)] -> ["uniq"]
| pp_seq_take [(take 1!$_)] -> ["take"]
| pp_seq_drop [(drop 1!$_)] -> ["drop"]
| pp_seq_rot [(rot 1!$_)] -> ["rot"]
| pp_seq_rotr [(rotr 1!$_)] -> ["rotr"]
| pp_seq_rev [(rev 1!$_)] -> ["rev"].

(* Keep the Adds forms intact, so that they can be matched in pretty   *)
(* printing rules. Note that the ternary form is possible, because of  *)
(* the coercion mem : seq >-> set >-> FUNCLASS.                        *)
Grammar constr constr0 : constr :=
  seq_Adds_form3 ["(" "Adds" constr9($x) constr9($s) constr9($y) ")"] ->
  [(Adds $x $s $y)]
| seq_Adds_form2 ["(" "Adds" constr9($x) constr9($s) ")"] -> [(Adds $x $s)]
| seq_Adds_form1 ["(" "Adds" constr9($x) ")"] -> [(Adds $x)]
| seq_Adds_form0 ["(" "Adds" ")"] -> [(!Adds ?)].

Grammar constr constr0 : constr :=
  seq_Adds ["Adds"] -> [(!Adds ?)]
| seq_size ["size"] -> [(!size ?)]
| seq_behead ["behead"] -> [(!behead ?)]
| seq_cat ["cat"] -> [(!cat ?)]
| seq_add_last ["add_last"] -> [(!add_last ?)]
| seq_uniq ["uniq"] -> [(!uniq ?)]
| seq_take ["take"] -> [(!take ?)]
| seq_drop ["drop"] -> [(!drop ?)]
| seq_rot ["rot"] -> [(!rot ?)]
| seq_rotr ["rotr"] -> [(!rotr ?)]
| seq_rev ["rev"] -> [(!rev ?)].

(* An N-ary sequence form; unfortunately, it can't be used in the      *)
(* pattern-matching clauses.                                           *)

Grammar constr constr0 : constr :=
  seq_form [ "(" "Seq" seq_body($s) ")" ] -> [$s]
with seq_body : constr :=
  seq_body_tail [ constr9($x) "&" constr9($s)] -> [(Adds $x $s)]
| seq_body_adds [ constr9($x) seq_body($s)] -> [(Adds $x $s)]
| seq_body_seq0 [ ] -> [seq0].

(* Sequence pretty-printing. Turns on by default when the sequence has *)
(* a definite length, or starts with at least three explicit items.    *)
(* The PPSEQPP marker is a hook that recursively pretty-prints the     *)
(* items in the list, with a given type.                               *)

Syntax constr level 10:
  pp_seq_call [(Pretty (seq $_) $s)] ->
  [ "Seq" [<hv 1> (PPSEQ SPC $s)]]
| pp_seq_seq1 [(Seq $x & (Seq0 $t))] ->
  [<<(Pretty (seq $t) (Seq $x & (Seq0 $t)))>>]
| pp_seq_seq2 [(Seq $x $y & (Seq0 $t))] ->
  [<<(Pretty (seq $t) (Seq $x $y & (Seq0 $t)))>>]
| pp_seq_seq3plus [(Seq $x $y $z & $s)] ->
  [<<(Pretty (seq ?) (Seq $x $y $z & $s))>>]
| pp_seq_default [<<(PPSEQ $sep $s)>>] ->
  [(SEP $sep) "& " $s:L]
| pp_seq_seq0 [<<(PPSEQ $_ <<(Seq0 $_)>>)>>] ->
  []
| pp_seq_adds [<<(PPSEQ $sep <<(Adds $x $s)>>)>>] ->
  [(SEP $sep) $x:L (PPSEQ BRK $s)]
| pp_ppseqpp_tail [<<(PPSEQPP $sep $_ $s)>>] ->
  [(SEP $sep) "& " $s:L]
| pp_ppseqpp_end [<<(PPSEQPP $_ $_ <<(Seq0 $_)>>)>>] ->
  []
| pp_ppseqpp_adds [<<(PPSEQPP $sep $t <<(Adds $x $s)>>)>>] ->
  [(SEP $sep) <<(Pretty $t $x)>> (PPSEQPP BRK $t $s)].


Lemma set_sub_default : (d : dataSet; x, x' : d; s : (seq d); n : nat)
  (ltn n (size s)) -> (sub x' s n) = (sub x s n).
Proof. By Move=> d x x' s n; Elim: s n => [|y s Hrec] [|n] /=; Auto. Qed.

Lemma headI : (d : dataSet; s : (seq d); x : d)
  (add_last s x) = (Adds (head x s) (behead (add_last s x))).
Proof. By Move=> d [|y s]. Qed.

Definition bitseq : Set := (seq boolData).

Definition natseq : Set := (seq natData).

(* Incrementing the ith nat in a natseq, padding with 0's if needed. This      *)
(* allows us to use natseqs as bags of nats.                                   *)

Fixpoint incr_sub [v : natseq; i : nat] : natseq :=
  if v is (Adds n v') then
    if i is (S i') then (Adds n (incr_sub v' i')) else (Adds (S n) v')
  else (addsn i (0) (seq1 (1))).

Lemma sub_incr_sub : (v : natseq; i, j : nat)
  (sub (0) (incr_sub v i) j) = (addn i =d j (sub (0) v j)).
Proof.
Elim=> [|n v Hrec] [|i] [|j] //=; Rewrite: ?eqdSS ?addn0 //; Try By Case j.
Elim: i j => [|i Hrec] [|j] //=; Rewrite: ?eqdSS //; By Case j.
Qed.

Lemma size_incr_sub : (v : natseq; i : nat)
  (size (incr_sub v i)) = (if (ltn i (size v)) then (size v) else (S i)).
Proof.
Elim=> [|n v Hrec] [|i] //=; LeftBy Rewrite: size_addsn /= addn1.
Rewrite: Hrec; Apply: fun_if.
Qed.


Section UniqPerm.

Variable d : dataSet.

Lemma uniq_leq_size : (s1 : (seq d)) (uniq s1) ->
  (s2 : (seq d)) (sub_set s1 s2) -> (leq (size s1) (size s2)).
Proof.
Elim=> [|x s1 Hrec] /=; LeftBy Clear; Case.
Move/andP=> [Hx Hs1] s2 Hs12.
Case: (!rot_to d s2 x); LeftBy Apply: Hs12; Apply: setU11.
Move=> i s2' Ds2'; Rewrite: -(size_rot i s2) Ds2'; Apply: Hrec => // [y Hy].
Move: (Hs12 ? (setU1r ? Hy)); Rewrite: -(mem_rot i) Ds2'; Case/setU1P => //.
By Move=> Dx; Rewrite: Dx Hy in Hx.
Qed.

Lemma leq_size_uniq : (s1 : (seq d)) (uniq s1) ->
  (s2 : (seq d)) (sub_set s1 s2) -> (leq (size s2) (size s1)) -> (uniq s2).
Proof.
Elim=> [|x s1 Hrec] Hs1 s2 Hs12; LeftBy Case s2.
Case: (!rot_to d s2 x); [By Apply: Hs12; Apply: setU11 | Move=> i s2' Ds2'].
Rewrite: -(size_rot i) -(uniq_rot i) Ds2' /=; Case Hs2': (s2' x).
  Rewrite: ltnNge; Case/idP; Apply: (uniq_leq_size Hs1) => [y Hy].
  By Move: (Hs12 ? Hy); Rewrite: -(mem_rot i) Ds2'; Case/setU1P => // [[]].
Simpl in Hs1; Move/andP: Hs1 => [Hx Hs1]; Apply: Hrec => // [y Hy].
Move: (Hs12 ? (setU1r ? Hy)); Rewrite: -(mem_rot i) Ds2'; Case/setU1P => //.
By Move=> Dx; Rewrite: Dx Hy in Hx.
Qed.

Lemma uniq_size_uniq : (s1 : (seq d)) (uniq s1) ->
  (s2 : (seq d)) s1 =1 s2 -> (uniq s2) = ((size s2) =d (size s1)).
Proof.
Move=> s1 Hs1 s2 Es12.
Rewrite: eqn_leq andbC uniq_leq_size //=; RightBy Move=> y; Rewrite Es12.
Apply/idP/idP => [Hs2|]; LeftBy Apply: uniq_leq_size => // [y]; Rewrite Es12.
By Apply: leq_size_uniq => // [y]; Rewrite Es12.
Qed.

Lemma uniq_perm : (s1, s2 : (seq d))
  s1 =1 s2 -> (size s1) = (size s2) -> (uniq s1) = (uniq s2).
Proof.
Move=> s1 s2 Es12 Hs12; Apply/idP/idP=> [Us];
  Rewrite: (uniq_size_uniq Us) ?Hs12 ?set11 //.
By Move=> y; Rewrite Es12.
Qed.

End UniqPerm.

Section RotrLemmas.

Variables n0 : nat; d : dataSet.

Lemma size_rotr : (s : (seq d)) (size (rotr n0 s)) = (size s).
Proof. By Move=> *; Rewrite: /rotr size_rot. Qed.

Lemma mem_rotr : (s : (seq d)) (rotr n0 s) =1 s.
Proof. By Move=> s x; Rewrite: /rotr mem_rot. Qed.

Lemma rotr_size_cat: (s1, s2 : (seq d))
  (rotr (size s2) (cat s1 s2)) = (cat s2 s1).
Proof. By Move=> *; Rewrite: /rotr size_cat subn_addl rot_size_cat. Qed.

Lemma rotr1_add_last : (x : d; s : (seq d))
  (rotr (1) (add_last s x)) = (Adds x s).
Proof. By Move=> *; Rewrite: -rot1_adds rotr_rot. Qed.

Lemma has_rotr : (a : (set d); s : (seq d)) (has a (rotr n0 s)) = (has a s).
Proof. By Move=> *; Rewrite: /rotr has_rot. Qed.

Lemma uniq_rotr : (s : (seq d)) (uniq (rotr n0 s)) = (uniq s).
Proof. By Move=> *; Rewrite: /rotr uniq_rot. Qed.

Lemma rot_rotr : (monic (!rotr d n0) (rot n0)).
Proof.
Move=> s; Case (ltnP n0 (size s)); Move=> Hs.
  Rewrite: -{1 n0}(leq_sub_sub (ltnW Hs)) -{1 (size s)}size_rotr.
  Exact (rotr_rot ? ?).
Rewrite: -{2 s}(rot_oversize Hs); Rewrite: -eqn_sub0 in Hs.
By Rewrite: /rotr (eqP Hs) rot0.
Qed.

Lemma rotr_inj : (injective (!rotr d n0)). Proof. Exact (monic_inj rot_rotr). Qed.

Lemma rev_rot : (s : (seq d)) (rev (rot n0 s)) = (rotr n0 (rev s)).
Proof.
Move=> s; Rewrite: /rotr size_rev -{3 s}(cat_take_drop n0) {1}/rot !rev_cat.
By Rewrite: -size_drop -size_rev rot_size_cat.
Qed.

Lemma rev_rotr : (s : (seq d)) (rev (rotr n0 s)) = (rot n0 (rev s)).
Proof.
Move=> s; Apply (monic_move rot_rotr).
Rewrite: {1}/rotr size_rev size_rotr /rotr {2}/rot rev_cat.
Pose m := (subn (size s) n0); Rewrite: -{1 m}(!size_takel m d s (leq_subr ? ?)).
By Rewrite: -size_rev rot_size_cat -rev_cat cat_take_drop.
Qed.

End RotrLemmas.

Section RotCompLemmas.

Variable d : dataSet.

Lemma rot_addn : (m, n : nat; s : (seq d)) (leq (addn m n) (size s)) ->
  (rot (addn m n) s) = (rot m (rot n s)).
Proof.
Move=> m n s; Rewrite: leq_eqVlt; Case/setU1P => [Emn | Hmn].
  By Rewrite: Emn rot_size -{1 s}(rot_rotr m) /rotr -Emn subn_addr.
Rewrite: -{1 s}(cat_take_drop n) /rot !take_cat !drop_cat.
Rewrite: addnC in Hmn; Def: Hn := (leq_trans (leq_addr ? ?) (ltnW Hmn)).
Rewrite: (size_takel Hn) ltnNge leq_addl subn_addl /= catA.
By Rewrite: ltnNge size_drop leq_sub_add -ltnNge Hmn.
Qed.

Lemma rotS : (n : nat; s : (seq d))
  (ltn n (size s)) -> (rot (S n) s) = (rot (1) (rot n s)).
Proof. Exact (!rot_addn (1)). Qed.

Lemma rot_rot : (m, n : nat; s : (seq d)) (leq n (size s)) -> (leq m (size s)) ->
  (rot m (rot n s)) =
     (if (leq (addn m n) (size s)) then (rot (addn m n) s) else
      (rot (subn (addn m n) (size s)) s)).
Proof.
Move=> m n s Hn Hm; Case: (leqP (addn m n) (size s)) => [Hmn | Hmn].
  Exact (esym (rot_addn Hmn)).
Step Hm': (leq (subn (addn m n) (size s)) m).
  By Rewrite: leq_sub_add addnC leq_add2r.
Rewrite: -{1 2 m}(leq_add_sub Hm') in Hm *.
Rewrite: rot_addn ?size_rot //; Congr rot.
Rewrite: -(subn_add2r n) -subn_sub (leq_sub_sub (ltnW Hmn)) -(size_rot n).
Exact (rotr_rot n s).
Qed.

Lemma rot_sym : (m, n : nat; s : (seq d)) (rot m (rot n s)) = (rot n (rot m s)).
Proof.
Move=> m n s; Case: (ltnP (size s) m) => [Hm|Hm].
  By Rewrite: !(!rot_oversize d m) ?size_rot 1?ltnW.
Case: (ltnP (size s) n) => [Hn | Hn].
  By Rewrite: !(!rot_oversize d n) ?size_rot 1?ltnW.
By Rewrite: !rot_rot 1?addnC.
Qed.

Lemma rot_rotr_sym : (m, n : nat; s : (seq d))
   (rot m (rotr n s)) = (rotr n (rot m s)).
Proof. By Move=> *; Rewrite: {2}/rotr size_rot rot_sym. Qed.

Lemma rotr_sym : (m, n : nat; s : (seq d))
   (rotr m (rotr n s)) = (rotr n (rotr m s)).
Proof. By Move=> *; Rewrite: /rotr !size_rot rot_sym. Qed.

End RotCompLemmas.

Section Sieve.

Variable n0 : nat; d : dataSet.

Fixpoint sieve [m : bitseq] : (seq d) -> (seq d) :=
  [s]Cases m s of
   (Adds b m') (Adds x s') =>
    if b then (Adds x (sieve m' s')) else (sieve m' s')
  | _ _ => seq0
  end.

Lemma sieve_false : (s : (seq d); n : nat) (sieve (seqn n false) s) = seq0.
Proof. By Elim=> [|x s Hrec] [|n] /=. Qed.

Lemma sieve_true : (s : (seq d); n : nat) (leq (size s) n) ->
  (sieve (seqn n true) s) = s.
Proof. By Elim=> [|x s Hrec] [|n] //= Hn; Congr Adds; Apply: Hrec. Qed.

Lemma sieve0 : (m : bitseq) (sieve m seq0) = seq0.
Proof. By Case. Qed.

Lemma sieve1 : (b : bool; x : d) (sieve (seq1 b) (seq1 x)) = (seqn b x).
Proof. By Case. Qed.

Lemma sieve_adds : (b : bool; m : bitseq; x : d; s : (seq d))
  (sieve (Adds b m) (Adds x s)) = (cat (seqn b x) (sieve m s)).
Proof. By Case. Qed.

Lemma size_sieve : (m : bitseq; s : (seq d)) (size m) = (size s) ->
  (size (sieve m s)) = (count id m).
Proof.
By Elim=> [|b m Hrec] [|x s] //=; Injection=> Hs; Case: b; Rewrite: /= Hrec.
Qed.

Lemma sieve_cat : (m1 : bitseq; s1 : (seq d)) (size m1) = (size s1) ->
  (m2 : bitseq; s2 : (seq d))
  (sieve (cat m1 m2) (cat s1 s2)) = (cat (sieve m1 s1) (sieve m2 s2)).
Proof.
Move=> m1 s1 Hm1 m2 s2; Elim: m1 s1 Hm1 => [|b1 m1 Hrec] [|x1 s1] //=.
By Injection=> Hm1; Rewrite: (Hrec ? Hm1); Case b1.
Qed.

Lemma mem_sieve_adds : (b : bool; m : bitseq; x : d; s : (seq d); y : d)
  (sieve (Adds b m) (Adds x s) y) = (orb (andb b x =d y) (sieve m s y)).
Proof. By Case. Qed.

Lemma mem_sieve : (m : bitseq; s : (seq d)) (sub_set (sieve m s) s).
Proof.
Move=> m s y; Elim: s m => [|x p Hrec] [|[|] m] //=;
  Rewrite: /setU1; Case (x =d y); Simpl; EAuto.
Qed.

Lemma has_sieve_adds : (a : (set d); b : bool; m : bitseq; x : d; s : (seq d))
  (has a (sieve (Adds b m) (Adds x s)))
    = (orb (andb b (a x)) (has a (sieve m s))).
Proof. By Move=> a [|]. Qed.

Lemma uniq_sieve : (s : (seq d)) (uniq s) -> (m : bitseq) (uniq (sieve m s)).
Proof.
Elim=> [|x s Hrec] //=; LeftBy Clear; Case.
Move/andP=> [Hx Hs] [|[|] m] //=; Rewrite: (Hrec Hs) // andbT.
Apply/idP=> [Hmx]; Case/idP: Hx; Exact (mem_sieve Hmx). 
Qed.

Lemma sieve_rot : (m : bitseq; s : (seq d)) (size m) = (size s) ->
  (sieve (rot n0 m) (rot n0 s)) = (rot (count id (take n0 m)) (sieve m s)).
Proof.
Move=> m s Hs; Step Hsn0: (size (take n0 m)) = (size (take n0 s)).
  By Rewrite: !size_take Hs.
Rewrite: -(size_sieve Hsn0) {1 2}/rot sieve_cat ?size_drop ?Hs //.
Rewrite: -{4 m}(cat_take_drop n0 m) -{4 s}(cat_take_drop n0 s) sieve_cat //.
By Rewrite rot_size_cat.
Qed.

Lemma mem_sieve_rot : (m : bitseq; s : (seq d)) (size m) = (size s) ->
  (sieve (rot n0 m) (rot n0 s)) =1 (sieve m s).
Proof. By Move=> m s Hm x; Rewrite: sieve_rot // mem_rot. Qed.

End Sieve.

Section Map.

Variables n0 : nat; d1 : dataSet; x1 : d1; d2 : dataSet; x2 : d2; f : d1 -> d2.

Fixpoint maps [s : (seq d1)] : (seq d2) :=
  if s is (Adds x s') then (Adds (f x) (maps s')) else seq0.

Lemma maps_adds : (x : d1; s : (seq d1))
  (maps (Adds x s)) = (Adds (f x) (maps s)).
Proof. Done. Qed.

Lemma maps_seqn : (x : d1) (maps (seqn n0 x)) = (seqn n0 (f x)).
Proof. By Move=> x; Elim: n0 => // *; Congr Adds. Qed.

Lemma maps_cat : (s1, s2 : (seq d1))
  (maps (cat s1 s2)) = (cat (maps s1) (maps s2)).
Proof. By Move=> s1 s2; Elim: s1 => [|x s1 Hrec] //=; Rewrite: Hrec. Qed.

Lemma size_maps : (s : (seq d1)) (size (maps s)) = (size s).
Proof. By Elim => [|x s Hrec] //=; Rewrite: Hrec. Qed.

Lemma behead_maps : (s : (seq d1)) (behead (maps s)) = (maps (behead s)).
Proof. By Case. Qed.

Lemma sub_maps : (n : nat; s : (seq d1))
  (ltn n (size s)) -> (sub x2 (maps s) n) = (f (sub x1 s n)).
Proof. By Move=> n s; Elim: s n => [|x s Hrec] [|n]; Try Exact (Hrec n). Qed.

Lemma maps_add_last : (s : (seq d1); x : d1)
  (maps (add_last s x)) = (add_last (maps s) (f x)).
Proof. By Move=> *; Rewrite: -!cats1 maps_cat. Qed.

Lemma last_maps : (s : (seq d1); x : d1)
  (last (f x) (maps s)) = (f (last x s)).
Proof. By Elim=> [|y s Hrec] x /=. Qed.

Lemma belast_maps : (s : (seq d1); x : d1)
  (belast (f x) (maps s)) = (maps (belast x s)).
Proof. By Elim=> [|y s Hrec] x //=; Rewrite: Hrec. Qed.

Lemma filter_maps : (a : (set d2); s : (seq d1))
  (filter a (maps s)) = (maps (filter (comp a f) s)).
Proof.
By Move=> a; Elim=> [|x s Hrec] //=; Rewrite: !if_arg (fun_if maps) /= Hrec.
Qed.

Lemma find_maps : (a : (set d2); s : (seq d1))
  (find a (maps s)) = (find (comp a f) s).
Proof. By Move=> a; Elim=> [|x s Hrec] //=; Rewrite: Hrec. Qed.

Lemma has_maps : (a : (set d2); s : (seq d1))
  (has a (maps s)) = (has (comp a f) s).
Proof. By Move=> a; Elim=> [|x s Hrec] //=; Rewrite: Hrec. Qed.

Lemma count_maps : (a : (set d2); s : (seq d1))
  (count a (maps s)) = (count (comp a f) s).
Proof. By Move=> a; Elim=> [|x s Hrec] //=; Rewrite: Hrec. Qed.

Lemma maps_take : (s : (seq d1)) (maps (take n0 s)) = (take n0 (maps s)).
Proof. By Elim: {}n0 => [|n Hrec] [|x s] //=; Rewrite: Hrec. Qed.

Lemma maps_drop : (s : (seq d1)) (maps (drop n0 s)) = (drop n0 (maps s)). 
Proof. By Elim: {}n0 => [|n Hrec] [|x s] //=; Rewrite: Hrec. Qed.

Lemma maps_rot : (s : (seq d1)) (maps (rot n0 s)) = (rot n0 (maps s)).
Proof. By Move=> *; Rewrite: /rot maps_cat maps_take maps_drop. Qed.

Lemma maps_rotr : (s : (seq d1)) (maps (rotr n0 s)) = (rotr n0 (maps s)).
Proof.
By Move=> *; Apply (monic_move (!rotr_rot n0 d2)); Rewrite: -maps_rot rot_rotr.
Qed.

Lemma maps_rev : (s : (seq d1)) (maps (rev s)) = (rev (maps s)).
Proof. By Elim=> [|x s Hrec] //=; Rewrite: !rev_adds -!cats1 maps_cat Hrec. Qed.

Lemma maps_sieve : (m : bitseq; s : (seq d1))
  (maps (sieve m s)) = (sieve m (maps s)).
Proof. By Elim=> [|[|] m Hrec] [|x p]  //=; Rewrite Hrec. Qed.

Lemma maps_f : (s : (seq d1); x : d1) (s x) -> (maps s (f x)).
Proof.
Move=> s x; Elim: s => [|y s Hrec] //=.
By Case/setU1P => [Dx | Hx]; [Rewrite: Dx setU11 | Apply setU1r; Auto].
Qed.

Lemma mapsPx : (s : (seq d1); y : d2)
  (reflect (EX x | (s x) & (f x) = y) (maps s y)).
Proof.
Move=> s y; Elim: s => [|x s Hrec]; LeftBy Right; Case.
Rewrite: /= /setU1; Case Hxy: ((f x) =d y).
  By Left; Exists x; [Rewrite set11 | Rewrite (eqP Hxy)].
Apply: (iffP Hrec) => [[x' Hx' []] | [x' Hx' Dy]].
  By Exists x'; LeftBy Rewrite: Hx' orbT.
By Case: Dy Hxy; Case: (x =P x') Hx' => [[]|_]; [Rewrite set11 | Exists x'].
Qed.

Lemma maps_uniq : (s : (seq d1)) (uniq (maps s)) -> (uniq s).
Proof.
Elim=> [|x s Hrec] //=; Case/andP => [Hsx Hs]; Rewrite: (Hrec Hs) andbT.
By Apply/idP => [Hx]; Case/(mapsPx ? ?): Hsx; Exists x.
Qed.

Hypothesis Hf : (injective f).

Lemma mem_maps : (s : (seq d1); x : d1) (maps s (f x)) = (s x).
Proof.
Move=> s x; Apply/(mapsPx ? ?)/idP; RightBy Exists x.
By Move=> [y Hy Hfy]; Rewrite: -(Hf Hfy).
Qed.

Lemma index_maps : (s : (seq d1); x : d1) (index (f x) (maps s)) = (index x s).
Proof.
Move=> s x; Rewrite: /index; Elim: s => [|y s Hrec] //=.
By Rewrite: (inj_eqd Hf) Hrec.
Qed.

Lemma uniq_maps : (s : (seq d1)) (uniq (maps s)) = (uniq s).
Proof. By Elim=> [|x s Hrec] //=; Rewrite: mem_maps /= Hrec. Qed.

Lemma inj_maps : (injective maps).
Proof.
Move=> s1 s2; Elim: s1 s2 => [|y1 s1 Hrec] [|y2 s2] //=.
By Injection=> Hs Hy; Rewrite: (Hf Hy) (Hrec ? Hs).
Qed.

End Map.

Syntactic Definition mapsP := mapsPx | 3.

Lemma filter_sieve : (d : dataSet; a : (set d); s : (seq d))
  (filter a s) = (sieve (maps a s) s).
Proof. By Move=> d a; Elim=> //= [x s []]; Case: (a x). Qed.

Section MapComp.

Variables d1, d2, d3 : dataSet.

Lemma maps_id : (s : (seq d1)) (maps [x]x s) = s.
Proof. By Elim=> [|x s Hrec] //=; Rewrite: Hrec. Qed.

Lemma eq_maps : (f1, f2 : d1 -> d2) f1 =1 f2 -> (maps f1) =1 (maps f2).
Proof. By Move=> f1 f2 Ef; Elim=> [|x s Hrec] //=; Rewrite: Ef Hrec. Qed.

Lemma maps_comp : (f1 : d2 -> d3; f2 : d1 -> d2; s : (seq d1))
  (maps (comp f1 f2) s) = (maps f1 (maps f2 s)).
Proof. By Move=> f1 f2; Elim=> [|x s Hrec] //=; Rewrite: Hrec. Qed.

Lemma monic_maps : (f1 : d1 -> d2; f2 : d2 -> d1)
  (monic f1 f2) -> (monic (maps f1) (maps f2)).
Proof. By Move=> f1 f2 Hf; Elim=> [|x s Hrec] //=; Rewrite: Hf Hrec. Qed.

End MapComp.


Section FoldRight.

Variables d : dataSet; R : Set; f : d -> R -> R; z0 : R.

Fixpoint foldr [s : (seq d)] : R :=
  if s is (Adds x s') then (f x (foldr s')) else z0.

Lemma foldr_fold_right : (s : (seq d)) (foldr s) = (fold_right f z0 s).
Proof. By Elim => [|x s Hrec] //=; Rewrite: Hrec. Qed.

End FoldRight.

Section FoldRightComp.

Variables d1, d2 : dataSet; h : d1 -> d2; R : Set; f : d2 -> R -> R; z0 : R.

Lemma foldr_cat : (s1, s2 : (seq d2))
  (foldr f z0 (cat s1 s2)) = (foldr f (foldr f z0 s2) s1).
Proof. By Move=> s1 s2; Elim: s1 => [|x s1 Hrec] //=; Rewrite: Hrec. Qed.

Lemma foldr_maps : (s : (seq d1))
  (foldr f z0 (maps h s)) = (foldr [x; z](f (h x) z) z0 s).
Proof. By Elim=> [|x s Hrec] //=; Rewrite: Hrec. Qed.

End FoldRightComp.

Section FoldLeft.

Variables d : dataSet; R : Set; f : R -> d -> R.

Fixpoint foldl [z : R; s : (seq d)] : R :=
  if s is (Adds x s') then (foldl (f z x) s') else z.

Lemma foldl_fold_left : (z : R; s : (seq d)) (foldl z s) = (fold_left f s z).
Proof. By Move=> z s; Elim: s z => [|x s Hrec] //=; Rewrite: Hrec. Qed.

Lemma foldl_rev : (z : R; s : (seq d))
  (foldl z (rev s)) = (foldr [x;z](f z x) z s).
Proof.
Move=> z s; Elim/last_ind: s z => [|s x Hrec] z //=.
By Rewrite: rev_add_last -cats1 foldr_cat -Hrec.
Qed.

Lemma foldl_cat : (z : R; s1, s2 : (seq d))
  (foldl z (cat s1 s2)) = (foldl (foldl z s1) s2).
Proof. 
Move=> z s1 s2; Rewrite: -(rev_rev (cat s1 s2)) foldl_rev rev_cat.
By Rewrite: foldr_cat -!foldl_rev !rev_rev.
Qed.

End FoldLeft.

Section Scan.

Variables d1 : dataSet; x1 : d1; d2 : dataSet; x2 : d2.
Variables f : d1 -> d1 -> d2; g : d1 -> d2 -> d1.

Fixpoint pairmap [x : d1; s : (seq d1)] : (seq d2) :=
  if s is (Adds y s') then (Adds (f x y) (pairmap y s')) else seq0.

Lemma size_pairmap : (x : d1; s : (seq d1))
  (size (pairmap x s)) = (size s).
Proof. By Move=> x s; Elim: s x => [|y s Hrec] x //=; Rewrite: Hrec. Qed.

Lemma sub_pairmap : (s : (seq d1); n : nat; Hn : (ltn n (size s)); x : d1)
  (sub x2 (pairmap x s) n) = (f (sub x1 (Adds x s) n) (sub x1 s n)).
Proof. By Simpl; Elim => [|x s Hrec] [|n]; Try Exact [H; y](Hrec n H x). Qed.

Fixpoint scanl [x : d1; s : (seq d2)] : (seq d1) :=
  if s is (Adds y s') then [x' := (g x y)](Adds x' (scanl x' s')) else seq0.

Lemma size_scanl : (x : d1; s : (seq d2))
  (size (scanl x s)) = (size s).
Proof. By Move=> x s; Elim: s x => [|y s Hrec] x //=; Rewrite: Hrec. Qed.

Lemma sub_scanl : (x : d1; s : (seq d2); n : nat; Hn : (ltn n (size s)))
  (sub x1 (scanl x s) n) = (foldl g x (take (S n) s)).
Proof.
By Move=> x s; Elim: s x => [|y s Hrec] x [|n] Hn //=; Rewrite: ?take0 1?Hrec.
Qed.

Hypothesis Hfg : (x : d1) (monic (g x) (f x)).

Lemma pairmap_scanl : (x : d1) (monic (scanl x) (pairmap x)).
Proof. By Move=> x s; Elim: s x => [|y s Hrec] x //=; Rewrite: Hfg Hrec. Qed.

Hypothesis Hgf : (x : d1) (monic (f x) (g x)).

Lemma scanl_pairmap : (x : d1) (monic (pairmap x) (scanl x)).
Proof. By Move=> x s; Elim: s x => [|y s Hrec] x //=; Rewrite: Hgf Hrec. Qed.

End Scan.

Unset Implicit Arguments.

Definition foo := (Seq (1) (1) (2) (3) (5) (8) (13)).





 
