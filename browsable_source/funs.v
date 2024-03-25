(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require tacticext.

Set Implicit Arguments.

(* Basic constructions for intuitionistic functions : extensional equality   *)
(* composition, override, update, inverse, and iteration, with some their    *)
(* identities, and reflected equalities.                                     *)

(* Extensional equality, for unary and binary functions, including syntactic *)
(* sugar.                                                                    *)

Section ExtensionalEquality.

Variables A, B, C : Set.

Definition eqfun [f, g : B -> A] : Prop := (x : B) (f x) = (g x).

Definition eqrel [f, g : C -> B -> A] : Prop :=
  (x : C; y : B) (f x y) = (g x y).

Lemma frefl : (f : B -> A) (eqfun f f). Proof. Split. Qed.
Lemma fsym : (f, g : B -> A) (eqfun f g) -> (eqfun g f).
Proof. Move=> f g H x; Auto. Qed.
Lemma rrefl : (f : C -> B -> A) (eqrel f f). Proof. Split. Qed.

End ExtensionalEquality.

Grammar constr constr1 : constr :=
  fun_equality [constr0($f1) "=1" constr0($f2)] ->[(eqfun $f1 $f2)]
| rel_equality [constr0($f1) "=2" constr0($f2)] ->[(eqrel $f1 $f2)].

Syntax constr
  level 1:
    fun_equal [ (eqfun $f1 $f2) ] -> [ [<hov 0> $f1:E [0 1]  " =1 " $f2:E ] ]
  | rel_equal [ (eqrel $f1 $f2) ] -> [ [<hov 0> $f1:E [0 1]  " =2 " $f2:E ] ].

Section Composition.

Variables A, B : Set.

Definition id := [x : A] x.

Definition comp [f : B -> A; C : Set; g : C -> B] := [x] (f (g x)).

Lemma eq_comp : (f, f' : B -> A; Ef : f =1 f')
        (C : Set; g, g' : C -> B; Eg : g =1 g')
  (comp f g) =1 (comp f' g').
Proof. By Move=> f f' Ef C g g' Eg x; Rewrite: /comp Eg Ef. Qed.

End Composition.

Grammar constr constr0 : constr := poly_id ["id"] -> [(!id ?)].

(* Simple iteration (`for' loops!), indexed and unindexed.                  *)

Section Iteration.

Variable A : Set.

Definition iter_n [n; f; x] := Eval Compute in (nat_rec [_]A x f n).

Definition iter [n; f] := Eval Compute in (iter_n n [_]f).

Lemma iter_plus : (n, m : nat; f : A -> A; x : A)
  (iter (plus n m) f x) = (iter n f (iter m f x)).
Proof. By Move=> n m f x; Elim: n => [|n Hrec] //; Congr f. Qed.

Lemma iter_f : (n : nat; f : A -> A; x : A)
  (iter n f (f x)) = (iter (S n) f x).
Proof. By Move=> n f x; Elim: n => [|n Hrec] //; Congr f. Qed.

Lemma f_iter : (n : nat; f : A -> A; x : A)
  (f (iter n f x)) = (iter (S n) f x).
Proof. Done. Qed.

End Iteration.

Lemma eq_iter : (A : Set; f, f' : A -> A; Ef : f =1 f'; n : nat)
   (iter n f) =1 (iter n f').
Proof.
By Move=> A f f' Ef n x /=; Elim: n => [|n Hrec] //=; Rewrite: Ef Hrec.
Qed.

Lemma eq_iter_n : (A : Set; f, f' : nat -> A -> A; Ef : f =2 f'; n : nat)
   (iter_n n f) =1 (iter_n n f').
Proof. By Move=> A f f' Ef /=; Elim=> [|n Hrec] x //=; Rewrite: Ef Hrec. Qed.

(* In an intuitionistic setting, we have two degrees of injectivity. The     *)
(* weaker one gives only simplification, and the strong one provides a left  *)
(* inverse (we show in `finset' that they coincide for finite types).        *)
(* (The definition could be further weakened if equality on A is not         *)
(* decidable, to ~ x = y -> ~ (f x) = (f y), but this doesn't seem useful.)  *)

Section Injections.

Variables A, B : Set; f : B -> A; g : A -> B.

Definition injective : Prop := (x, x' : B) (f x) = (f x') -> x = x'.

Definition monic : Prop := (x : B) (g (f x)) = x.
Hypothesis Hf : monic.

Lemma monic_move : (x : B; y : A) (f x) = y -> x = (g y).
Proof. Move=> x y [ ]; Exact (esym (Hf ?)). Qed.

Lemma monic_inj : injective.
Proof. Move=> x y Ef; Rewrite (monic_move Ef); Exact (Hf ?). Qed.

End Injections.

Section InjectionsTheory.

Variables A, B : Set; f : B -> A; g : A -> B.
Hypothesis Hf : (injective f); Hfg : (monic f g); Hg : (injective g).
Variables C : Set; h : C -> B; k : B -> C.
Hypothesis Hh : (injective h); Hhk : (monic h k).
Variable f' : B -> A.
Hypothesis Ef : f =1 f'.
Variable g' : A -> B.

Lemma inj_monic_sym : (monic g f).
Proof. Exact [x](Hg (Hfg (g x))). Qed.

Lemma inj_comp : (injective (comp f h)).
Proof. Exact [x, x'; Efhx](Hh (Hf Efhx)). Qed.

Lemma monic_comp : (monic (comp f h) (comp k g)).
Proof. Move=> x; Rewrite: /comp Hfg; Apply Hhk. Qed.

Lemma eq_injective : (injective f').
Proof. Move=> x y; Rewrite: -2!Ef; Apply Hf. Qed.

Lemma eq_monic : g =1 g' -> (monic f' g').
Proof. Move=> Eg; Intro; Rewrite: -Ef -Eg; Exact (Hfg ?). Qed.

Lemma inj_monic_eq : (monic f' g) -> f =1 f'.
Proof. Exact [Hf'g; x](Hg (etrans (Hfg x) (esym (Hf'g x)))). Qed.

End InjectionsTheory.

Section Isos.

Variables A, B : Set; f : B -> A.

Definition iso : Prop := (EX g | (monic f g) & (monic g f)).

Hypothesis Hf : iso.

Lemma iso_inj : (injective f).
Proof. Case: Hf => [h Ef _]; Exact (monic_inj Ef). Qed.

Lemma monic_iso_sym : (g : A -> B) (monic g f) -> (monic f g).
Proof. Exact [_; Eg](inj_monic_sym Eg iso_inj). Qed.

Lemma iso_monic_sym : (g : A -> B) (monic f g) -> (monic g f).
Proof. By Move=> g Eg x; Case: Hf => [h _ Eh]; Case: (Eh x); Congr f. Qed.

Lemma iso_monic_eq : (g  : A -> B; Eg  : (monic f g))
                     (g' : A -> B; Eg' : (monic f g')) g =1 g'.
Proof.
Move=> g Eg g' Eg'; Apply: (inj_monic_eq ? iso_inj); Apply iso_monic_sym; Auto.
Qed.

End Isos.

Section IsosTheory.

Variables A, B : Set; f : B -> A.

Lemma eq_iso : (iso f) -> (f' : B -> A) f =1 f' -> (iso f').
Proof.
Move=> [g Ef Eg] f' Eff'.
Exists g; [Apply (eq_monic Ef) | Apply (eq_monic Eg)]; By Auto.
Qed.

Lemma iso_comp : (iso f) -> (C : Set; g : C -> B) (iso g) -> (iso (comp f g)).
Proof.
Move=> [h Ef Eh] C g [k Eg Ek]; Exists (comp k h); Apply monic_comp; Auto.
Qed.

Lemma iso_monic_iso : (iso f) -> (g : A -> B) (monic f g) -> (iso g).
Proof. By Move=> Hf; Exists f; LeftBy Apply iso_monic_sym. Qed.

End IsosTheory.


Unset Implicit Arguments. 








