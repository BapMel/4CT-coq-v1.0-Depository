(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require tacticext.
Require boolprop.
Require funs.
Require dataset.
Require natprop.
Require seq.

Set Implicit Arguments.

(* The basic theory of paths over a dataSet; this is essentially a   *)
(* complement to seq.v.                                              *)
(* Paths are non-empty sequences that obey a progression relation.   *)
(* They are passed around in three parts : the head and tail of the  *)
(* sequence, and a (boolean) predicate asserting the progression.    *)
(* This is rarely embarrassing, as the first two are usually         *)
(* implicit parameters inferred from the predicate, and it saves the *)
(* hassle of constantly constructing and destructing a dependent     *)
(* record. We allow duplicates; uniqueness, if desired (as is the    *)
(* case for several geometric constructions), must be asserted       *)
(* separately. We do provide shorthand, but for cycles only, because *)
(* the equational properties of "path" and "uniq" are unfortunately  *)
(* incompatible (esp. wrt "cat").                                    *)
(*    We define similarly cycles, but in this case we allow the      *)
(* empty sequence (which is a non-rooted empty cycle; by contrast,   *)
(* the empty path from x is the one-item sequence containing only x) *)
(*    We define notations for the common cases of function paths,    *)
(* where the progress relation is actually a function. We also       *)
(* define additional traversal/surgery operations, many of which     *)
(* could have been in seq.v, but are here because they only really   *)
(* are useful for sequences considered as paths :                    *)
(*  - directed surgery : splitPl, splitP, splitPr are dependent      *)
(*    predicates whose elimination splits a path x0:p at one of its  *)
(*    elements (say x). The three variants differ as follows:        *)
(*      - splitPl applies when x in in x0:p, generates two paths p1  *)
(*        and p2, along with the equation x = (last x0 p), and       *)
(*        replaces p with (cat p1 p2) in the goal (the patterned     *)
(*        Elim can be used to select occurrences and generate an     *)
(*        equation p = (cat p1 p2).                                  *)
(*      - splitP applies when x is in p, and replaces p with         *)
(*        (cat (add_last p1 x) p2), where x appears explicitly at    *)
(*        the end of the left part.                                  *)
(*      - splitPr similarly replaces p with (cat p1 (Adds x p2)),    *)
(*        where appears explicitly at the right of the split, when x *)
(*        is actually in p.                                          *)
(*    The parts p1 and p2 are computed using index/take/drop. The    *)
(*    splitP variant (but not the others) attempts to replace the    *)
(*    explicit expressions for p1 and p2 by p1 and p2, respectively. *)
(*    This is moderately useful, allows for defining other splitting *)
(*    lemmas with conclusions of the form (split x p p1 p2), with    *)
(*    other expressions for p1 and p2 that might be known to occur.  *)
(*  - function trajectories: traject, and a looping predicate.       *)
(*  - cycle surgery : arc extracts the sub-arc between two points    *)
(*    (including the first, excluding the second). (arc p x y) is    *)
(*    thus only meaningful if x and y are different points in p.     *)
(*  - cycle traversal : next, prev                                   *)
(*  - path order: mem2 checks whether two points belong to a         *)
(*    and appear in order (i.e., (mem2 p x y) checks that y appears  *)
(*    after an occurrence of x in p). This predicate a crucial part  *)
(*    of the definition of the abstract Jordan property.             *)
(*  - loop removal : shorten returns a shorter, duplicate-free path  *)
(*    with the same endpoints as its argument. The related shortenP  *)
(*    dependent predicate simultaneously substitutes a new path p',  *)
(*    for (shorten e x p), (last x p') for (last x p), and generates *)
(*    predicates asserting that p' is a duplicate-free subpath of p. *)
(* Although these functions operate on the underlying sequences, we  *)
(* provide a series of lemmas that define their interaction with the *)
(* path and cycle predicates, e.g., the path_cat equation can be     *)
(* used to split the path predicate after splitting the underlying   *)
(* sequence.                                                         *)

Section Paths.

Variables n0 : nat; d : dataSet; x0 : d.

Syntactic Definition dsub := (sub x0).

Section Path.

Variable e : (rel d).

Fixpoint path [x : d; p : (seq d)] : bool :=
  if p is (Adds y p') then (andb (e x y) (path y p')) else true.

Lemma path_cat : (x : d; p1,  p2 : (seq d))
  (path x (cat p1 p2)) = (andb (path x p1) (path (last x p1) p2)).
Proof.
By Move=> x p1 p2; Elim: p1 x => [|y p1 Hrec] x //=; Rewrite: Hrec -!andbA.
Qed.

Inductive split [x : d] : (seq d) -> (seq d) -> (seq d) -> Set :=
  Split : (p1 : (seq d); p2 : (seq d))
    (split x (cat (add_last p1 x) p2) p1 p2).

Lemma splitP : (p : (seq d); x : d) (p x) -> 
           let i = (index x p) in (split x p (take i p) (drop (S i) p)).
Proof.
Move=> p x Hx i; Move: {}Hx (esym (cat_take_drop i p)) => Hi.
Rewrite: -index_mem -/i in Hi; Rewrite: (drop_sub x Hi) -cat_add_last.
By Rewrite: {2}/i (sub_index x Hx); Move=> Dp; Rewrite: {1 p}Dp.
Qed.

Inductive splitl [x1 : d; x : d] : (seq d) -> Set :=
  Splitl : (p1 : (seq d); p2 : (seq d))
    (last x1 p1) = x -> (splitl x1 x (cat p1 p2)).

Lemma splitPl : (x1 : d; p : (seq d); x : d) (Adds x1 p x) -> (splitl x1 x p).
Proof.
Move=> x1 p x; Rewrite: /= /setU1; Case: (x1 =P x) => [[]|_].
  By Rewrite: -(cat0s p).
By Case/splitP => [p1 p2]; Split; Rewrite last_add_last.
Qed.

Inductive splitr [x : d] : (seq d) -> Set :=
  Splitr : (p1 : (seq d); p2 : (seq d)) (splitr x (cat p1 (Adds x p2))).

Lemma splitPr : (p : (seq d); x : d) (p x) -> (splitr x p).
Proof. By Move=> p x; Case/splitP => [p1 p2]; Rewrite: cat_add_last. Qed.

Lemma pathPx : (x : d; p : (seq d))
  (reflect (i : nat) (ltn i (size p)) -> (e (dsub (Adds x p) i) (dsub p i))
      (path x p)).
Proof.
Move=> x p; Elim: p x => [|y p Hrec] x /=; LeftBy Left.
Apply: (iffP andP) => [[Hxy Hp] | Hp].
  Move=> [|i] Hi //; Exact (Hrec ? Hp i Hi).
Split; LeftBy Exact (Hp (0) (leq0n (size p))).
Apply/(Hrec y) => [i Hi]; Exact (Hp (S i) Hi).
Qed.

Fixpoint next_at [x, y0, y : d; p : (seq d)] : d :=
  Cases p of
    Seq0         => if x =d y then y0 else x
  | (Adds y' p') => if x =d y then y' else (next_at x y0 y' p')
  end.
  
Definition next [p : (seq d); x : d] : d :=
  if p is (Adds y p') then (next_at x y y p') else x.

Fixpoint prev_at [x, y0, y : d; p : (seq d)] : d :=
  Cases p of
    Seq0         => if x =d y0 then y else x
  | (Adds y' p') => if x =d y' then y else (prev_at x y0 y' p')
  end.
  
Definition prev [p : (seq d); x : d] : d :=
  if p is (Adds y p') then (prev_at x y y p') else x.

Lemma next_sub : (p : (seq d); x : d)
  (next p x) =
    (if (p x) then if p is (Adds y p') then (sub y p' (index x p)) else x else x).
Proof.
Move=> [|y0 p] x //=; Elim: p {2 3 5}y0 => [|y' p Hrec] y /=;
  By Rewrite: /setU1 -(eqd_sym x); Case (x =d y); Try Exact (Hrec ?).
Qed.

Lemma prev_sub : (p : (seq d); x : d)
  (prev p x) =
    (if (p x) then if p is (Adds y p') then (sub y p (index x p')) else x else x).
Proof.
Move=> [|y0 p] x //=; Rewrite: /setU1 eqd_sym orbC.
Elim: p {2 5}y0 => [|y' p Hrec] y; Rewrite: /= /setU1 eqd_sym //.
Case (y' =d x); Simpl; Auto.
Qed.

Lemma mem_next : (p : (seq d); x : d) (p (next p x)) = (p x).
Proof.
Move=> p x; Rewrite next_sub; Case Hpx: (p x) => [|] //.
Case: p (index x p) Hpx => [|y0 p'] //= i _; Rewrite: /setU1.
Case: (ltnP i (size p')) => [Hi | Hi]; LeftBy Rewrite: (mem_sub y0 Hi) orbT.
By Rewrite: (sub_default y0 Hi) set11.
Qed.

Lemma mem_prev : (p : (seq d); x : d) (p (prev p x)) = (p x).
Proof.
Move=> p x; Rewrite prev_sub; Case Hpx: (p x) => [|] //.
Case: p Hpx => [|y0 p'] Hpx //.
By Apply mem_sub; Rewrite: /= ltnS index_size.
Qed.

Definition cycle [p : (seq d)] : bool :=
  if p is (Adds x p') then (path x (add_last p' x)) else true.

(* ucycleb is the boolean predicate, but ucycle is defined as a Prop *)
(* so that it can be used as a coercion target. *)
Definition ucycleb [p : (seq d)] : bool := (andb (cycle p) (uniq p)).
Definition ucycle [p : (seq d)] : Prop := (andb (cycle p) (uniq p)).

(* Projections, used for creating local lemmas. *)
Lemma ucycle_cycle : (p : (seq d)) (ucycle p) -> (cycle p).
Proof. By Move=> p; Case/andP. Qed.

Lemma ucycle_uniq : (p : (seq d)) (ucycle p) -> (uniq p).
Proof. By Move=> p; Case/andP. Qed.

Lemma cycle_path : (p : (seq d)) (cycle p) = (path (last x0 p) p).
Proof. By Move=> [|x p] //=; Rewrite: -cats1 path_cat /= andbT andbC. Qed.

Lemma next_cycle : (p : (seq d); Hp : (cycle p))
  (x : d) (p x) -> (e x (next p x)).
Proof.
Move=> [|y0 p] //= Hp x.
Elim: p {1 3 5}y0 Hp => [|y' p Hrec] y /=; Rewrite: eqd_sym /setU1.
  By Rewrite: andbT orbF; Move=> H H'; Rewrite: H' -(eqP H').
Case/andP => [Hy Hp]; Case: (y =P x) => [[]|_] //; Exact (Hrec ? Hp).
Qed.

Lemma prev_cycle : (p : (seq d); Hp : (cycle p))
  (x : d) (p x) -> (e (prev p x) x).
Proof.
Move=> [|y0 p] //= Hp x; Rewrite: /setU1 orbC.
Elim: p {1 5}y0 Hp => [|y' p Hrec] y /=; Rewrite: /= ?(eqd_sym x) /setU1.
  By Rewrite: andbT; Move=> H H'; Rewrite: H' -(eqP H').
Case/andP => [Hy' Hp]; Case: (y' =P x) => [[]|_] //; Exact (Hrec ? Hp).
Qed.

Lemma cycle_rot : (p : (seq d)) (cycle (rot n0 p)) = (cycle p).
Proof.
Case: (n0) => [|n] [|y0 p] //=; LeftBy Rewrite: /rot /= cats0.
Rewrite: /rot /= -{3 p}(cat_take_drop n) -cats1 -catA path_cat.
Case: (drop n p) => [|z0 q]; Rewrite: /= -cats1 !path_cat /= !andbT andbC //.
By Rewrite: last_cat; Repeat BoolCongr.
Qed.

Lemma ucycle_rot : (p : (seq d)) (ucycle (rot n0 p)) == (ucycle p).
Proof. By Move=> *; Rewrite: /ucycle uniq_rot cycle_rot. Qed.

Lemma cycle_rotr : (p : (seq d)) (cycle (rotr n0 p)) = (cycle p).
Proof. By Move=> p; Rewrite: -cycle_rot rot_rotr. Qed.

Lemma ucycle_rotr : (p : (seq d)) (ucycle (rotr n0 p)) == (ucycle p).
Proof. By Move=> *; Rewrite: /ucycle uniq_rotr cycle_rotr. Qed.

(* The "appears no later" partial preorder defined by a path. *)

Definition mem2 [p : (seq d); x, y : d] : bool := (drop (index x p) p y).

Lemma mem2l : (p : (seq d); x, y : d) (mem2 p x y) -> (p x).
Proof.
Move=> p x y; Rewrite: /mem2 -!index_mem size_drop; Move=> Hxy.
By Rewrite: ltn_lt0sub -(ltnSpred Hxy) ltnS leq0n.
Qed.

Lemma mem2lf : (p : (seq d); x : d)
  (p x) = false -> (y : d) (mem2 p x y) = false.
Proof. Move=> p x Hx y; Apply/idP => [Hp]; Case/idP: Hx; Exact (mem2l Hp). Qed.

Lemma mem2r : (p : (seq d); x, y : d) (mem2 p x y) -> (p y).
Proof.
Unfold mem2; Move=> p x y Hxy.
By Rewrite: -(cat_take_drop (index x p) p) mem_cat /setU Hxy orbT.
Qed.

Lemma mem2rf : (p : (seq d); y : d)
  (p y) = false -> (x : d) (mem2 p x y) = false.
Proof. Move=> p x Hx y; Apply/idP => [Hp]; Case/idP: Hx; Exact (mem2r Hp). Qed.

Lemma mem2_cat : (p1, p2 : (seq d); x, y : d)
  (mem2 (cat p1 p2) x y) =
    (orb (orb (mem2 p1 x y) (mem2 p2 x y)) (andb (p1 x) (p2 y))).
Proof.
Move=> p1 p2 x y; Rewrite: {1}/mem2 index_cat drop_cat; Case Hp1x: (p1 x).
  Rewrite: index_mem Hp1x mem_cat /setU /= -orbA.
  By Case Hp2: (p2 y); [Rewrite: !orbT | Rewrite: (mem2rf Hp2)].
By Rewrite: ltnNge leq_addr /= orbF subn_addr (mem2lf Hp1x).
Qed.

Lemma mem2_splice : (p1, p3 : (seq d); x, y : d)
  (mem2 (cat p1 p3) x y) -> (p2 : (seq d)) (mem2 (cat p1 (cat p2 p3)) x y).
Proof.
Move=> p1 p3 x y Hxy p2; Move: Hxy; Rewrite: !mem2_cat mem_cat /setU.
Case: (mem2 p1 x y) (mem2 p3 x y) => [|] // [|] /=; LeftBy Rewrite: orbT.
By Case: (p1 x) => [|] //= H; Rewrite: H !orbT.
Qed.

Lemma mem2_splice1 : (p1, p3 : (seq d); x, y : d)
  (mem2 (cat p1 p3) x y) -> (z : d) (mem2 (cat p1 (Adds z p3)) x y).
Proof. Exact [p1, p3; x, y; Hxy; z](mem2_splice Hxy (seq1 z)). Qed.

Lemma mem2_adds : (x, y : d; p : (seq d))
  (mem2 (Adds x p) y) =1 (if x =d y then (setU1 x p) else (mem2 p y)).
Proof. By Move=> x y p z; Rewrite: {1}/mem2 /= eqd_sym; Case (x =d y). Qed.

Lemma mem2_last : (y0 : d; p : (seq d); x : d)
  (mem2 (Adds y0 p) x (last y0 p)) = (Adds y0 p x).
Proof.
Move=> y0 p x; Apply/idP/idP; LeftBy Apply mem2l.
Rewrite: -index_mem /mem2; Move: (index x (Adds y0 p)) => i Hi.
By Rewrite: lastI drop_add_last ?size_belast // mem_add_last /= setU11.
Qed.

Lemma mem2l_cat : (p1 : (seq d); x : d; Hx : (p1 x) = false)
   (p2 : (seq d)) (mem2 (cat p1 p2) x) =1 (mem2 p2 x).
Proof. By Move=> p1 x Hx p2 y; Rewrite: mem2_cat Hx (mem2lf Hx) /= orbF. Qed.

Lemma mem2r_cat : (p2 : (seq d); y : d; Hy : (p2 y) = false)
   (p1 : (seq d); x : d) (mem2 (cat p1 p2) x y) = (mem2 p1 x y).
Proof. By Move=> p2 y Hy p1 x; Rewrite: mem2_cat Hy (mem2rf Hy) andbF !orbF. Qed.

Lemma mem2lr_splice : (p2 : (seq d); x, y : d)
  (Hx : (p2 x) = false; Hy : (p2 y) = false)
  (p1, p3 : (seq d)) (mem2 (cat (cat p1 p2) p3) x y) = (mem2 (cat p1 p3) x y).
Proof.
Move=> p2 x y Hx Hy p1 p3.
By Rewrite: !mem2_cat !mem_cat /setU Hx Hy (mem2lf Hx) !andbF !orbF.
Qed.

Inductive split2r [x, y : d] : (seq d) -> Set :=
  Split2l : (p1 : (seq d); p2 : (seq d))
    (Adds x p2 y) -> (split2r x y (cat p1 (Adds x p2))).

Lemma splitP2r : (p : (seq d); x, y : d) (mem2 p x y) -> (split2r x y p).
Proof.
Move=> p x y Hxy; Def: Hx := (mem2l Hxy).
Def: Hi := Hx; Rewrite: -index_mem in Hi.
Move: Hxy; Rewrite: /mem2 (drop_sub x Hi) (sub_index x Hx).
By Case/splitP: Hx => [p1 p2]; Rewrite: cat_add_last; Split.
Qed.

Fixpoint shorten [x : d; p : (seq d)] : (seq d) :=
  if p is (Adds y p') then
    if (p x) then (shorten x p') else (Adds y (shorten y p'))
  else seq0.

Inductive shorten_spec [x : d; p : (seq d)] : d -> (seq d) -> Set :=
  ShortenSpec : (p' : (seq d))
                (path x p') -> (uniq (Adds x p')) -> (sub_set p' p) ->
              (shorten_spec x p (last x p') p').

Lemma shortenP : (x : d; p : (seq d); Hp : (path x p))
  (shorten_spec x p (last x p) (shorten x p)).
Proof.
Move=> x p Hp; Elim: p x {1 2 5}x Hp (setU11 x p) => [|y2 p Hrec] y0 y1.
  By Rewrite: /setU1 orbF; Move=> _ Dy1; Rewrite (eqP Dy1); Repeat Split; Move.
Rewrite: /setU1 /= orbC; Case/andP => [Hy12 Hp].
Case Hpy0: (setU1 y2 p y0).
  Case: (Hrec ? ? Hp Hpy0) => [p' Hp' Up' Hp'p] _; Split; Auto; Simpl.
  Exact [z; H](setU1r ? (Hp'p ? H)).
Case: (Hrec ? ? Hp (setU11 y2 p)) => [p' Hp' Up' Hp'p] Dy1.
Step Hp'p2 : (sub_set (setU1 y2 p') (setU1 y2 p)).
  Move=> z; Rewrite: /= /setU1; Case: (y2 =d z) => [|] //; Exact (Hp'p z).
Rewrite: -{(last y2 p')}/(last y0 (Adds y2 p')); Split; Auto.
  By Rewrite: -(eqP Dy1) /= Hy12.
By Simpl; Case Hy0: (setU1 y2 p' y0); LeftBy Rewrite (Hp'p2 ? Hy0) in Hpy0.
Qed.

End Path.

Lemma eq_path : (e, e' : (rel d)) e =2 e' -> (path e) =2 (path e').
Proof.
By Move=> e e' Ee x p; Elim: p x => [|y p Hrec] x //=; Rewrite: Ee Hrec.
Qed.

Lemma sub_path : (e, e' : (rel d))
  (sub_rel e e') -> (x : d; p : (seq d)) (path e x p) -> (path e' x p).
Proof.
Move=> e e' He x p; Elim: p x => [|y p Hrec] x //=.
By Case/andP => [Hx Hp]; Rewrite: (He ? ? Hx) (Hrec ? Hp).
Qed.

End Paths.

Syntactic Definition pathP := [x0](pathPx x0 ? ? ?).

Grammar constr constr0 : constr :=
  fun_path ["(" "fpath" constr9($f) constr9($x) constr9($p) ")"]
      -> [(path (eqdf $f) $x $p)]
| fun_path1 ["(" "fpath" constr9($f) constr9($x) ")"]
      -> [(path (eqdf $f) $x)]
| fun_path0 ["(" "fpath" constr9($f) ")"]
      -> [(path (eqdf $f))]
| fun_cycle ["(" "fcycle" constr9($f) constr9($p) ")"]
      -> [(cycle (eqdf $f) $p)]
| fun_cycle0 ["(" "fcycle" constr9($f) ")"]
      -> [(cycle (eqdf $f))]
| fun_ucycle ["(" "ufcycle" constr9($f) constr9($p) ")"]
      -> [(ucycle (eqdf $f) $p)]
| fun_ucycle0 ["(" "ufcycle" constr9($f) ")"]
      -> [(ucycle (eqdf $f))].

Syntax constr level 0:
    fun_path_pp [ (path (eqdf $f) $x $p) ] ->  [(OPFORM fpath $f $x $p)]
  | fun_path1_pp [ (path (eqdf $f) $x) ] ->    [(OPFORM fpath $f $x)]
  | fun_path0_pp [ (path (eqdf $f)) ] ->       [(OPFORM fpath $f)]
  | fun_cycle_pp [ (cycle (eqdf $f) $p) ] ->   [(OPFORM fcycle $f $p)]
  | fun_cycle0_pp [ (cycle (eqdf $f)) ] ->     [(OPFORM fcycle $f)]
  | fun_ucycle_pp [ (ucycle (eqdf $f) $p) ] -> [(OPFORM ufcycle $f $p)]
  | fun_ucycle0_pp [ (ucycle (eqdf $f)) ] ->   [(OPFORM ufcycle $f)].

Section Trajectory.

Variables d : dataSet; f : d -> d.

Fixpoint traject [x : d; n : nat] : (seq d) :=
  if n is (S n') then (Adds x (traject (f x) n')) else seq0.

Lemma size_traject : (x : d; n : nat) (size (traject x n)) = n.
Proof. By Move=> x n; Elim: n x => [|n Hrec] x //=; NatCongr. Qed.

Lemma last_traject : (x : d; n : nat) (last x (traject (f x) n)) = (iter n f x).
Proof. By Move=> x n; Elim: n x => [|n Hrec] x //; Rewrite: -iter_f -Hrec. Qed.

Lemma fpathPx : (x : d; p : (seq d))
  (reflect (EX n | (traject (f x) n) = p) (fpath f x p)).
Proof.
Move=> x p; Elim: p x => [|y p Hrec] x; LeftBy Left; Exists (0).
Rewrite: /= andbC; Case: {Hrec}(Hrec y) => [Hrec | Hrec].
  Apply: (iffP eqP); LeftBy Case: Hrec => [n []] []; Exists (S n).
  By Move=> [[|n] H]; [Done | Injection H].
By Right; Move=> [[|n] Dp] //; Case: Hrec; Exists n; Injection: Dp => [] [].
Qed.

Lemma fpath_traject : (x : d; n : nat) (fpath f x (traject (f x) n)).
Proof. By Move=> x n; Apply/(fpathPx x ?); Exists n. Qed.

Definition looping [x : d; n : nat] : bool := (traject x n (iter n f x)).

Lemma loopingPx : (x : d; n : nat)
  (reflect (m : nat) (traject x n (iter m f x)) (looping x n)).
Proof.
Move=> x n; Apply introP; RightBy Move=> Hn Hn'; Rewrite: /looping Hn' in Hn.
Case: n => [|n] Hn //; Elim=> [|m Hrec]; LeftBy Apply: setU11.
Move: (fpath_traject x n) Hn; Rewrite: /looping -!f_iter -last_traject /=.
Rewrite: /= in Hrec; Case/splitPl: Hrec; Move: (iter m f x) => y p1 p2 Ep1.
Rewrite: path_cat last_cat Ep1; Case: p2 => [|z p2] //; Case/and3P => [_ Dy _] _.
By Rewrite: /setU1 mem_cat /setU /= (eqP Dy) /= setU11 !orbT.
Qed.

Lemma sub_traject : (i, n : nat) (ltn i n) ->
  (x : d) (sub x (traject x n) i) = (iter i f x).
Proof.
Move=> i n Hi x; Elim: n {2 3}x i Hi => [|n Hrec] y [|i] Hi //=.
By Rewrite: Hrec ?iter_f.
Qed.

Lemma trajectPx : (x : d; n : nat; y : d)
  (reflect (EX i | (ltn i n) & (iter i f x) = y) (traject x n y)).
Proof.
Move=> x n y; Elim: n x => [|n Hrec] x; LeftBy Right; Case.
Rewrite: /= /setU1 orbC; Case: {Hrec}(Hrec (f x)) => [Hrec | Hrec].
  By Left; Case: Hrec => [i Hi []]; Exists (S i); RightBy Rewrite iter_f.
Apply: (iffP eqP); LeftBy Exists (0); LeftBy Rewrite ltnNge.
By Move=> [[|i] Hi Dy] //; Case Hrec; Exists i; RightBy Rewrite iter_f.
Qed.

Lemma looping_uniq : (x : d; n : nat)
  (uniq (traject x (S n))) = (negb (looping x n)).
Proof.
Move=> x n; Rewrite: /looping; Elim: n x => [|n Hrec] x //.
Rewrite: -iter_f {2 S}lock /= -lock ~Hrec -negb_orb /setU1; BoolCongr.
Pose y := (iter n f (f x)); Case (trajectPx (f x) n y); LeftBy Rewrite: !orbT.
Rewrite: !orbF; Move=> Hy; Apply/idP/eqP => [Hx | Dy].
  Case/(trajectPx ? ? ?): Hx => [m Hm Dx].
  Step Hx': (looping x (S m)) By Rewrite: /looping -iter_f Dx /= setU11.
  Case: (trajectPx ? ? ? (loopingPx ? ? Hx' (S n))); Rewrite: -iter_f -/y.
  Move=> [|i] Hi //; Rewrite: -iter_f; Move=> Dy.
  By Case: Hy; Exists i; LeftBy Exact (leq_trans Hi Hm).
By Rewrite: {2 x}Dy /y -last_traject /= mem_lastU.
Qed.

End Trajectory.

Syntactic Definition fpathP   := fpathPx   | 3.
Syntactic Definition loopingP := loopingPx | 3.
Syntactic Definition trajectP := trajectPx | 4.

Section UniqCycle.

Variables n0 : nat; d : dataSet; e : (rel d); p : (seq d).

Hypothesis Up : (uniq p).

Lemma prev_next : (x : d) (prev p (next p x)) = x.
Proof.
Move=> x; Rewrite: prev_sub mem_next next_sub.
Case Hpx: (p x) => [|] //; Case Dp: p Up Hpx => [|y p'] //.
Rewrite: -Dp {1 p}Dp /=; Move/andP=> [Hpy Hp'] Hx.
Pose i := (index x p); Rewrite: -(sub_index y Hx); Congr (sub y).
Rewrite: -index_mem -/i Dp /= ltnS leq_eqVlt in Hx.
Case/setU1P: Hx => [Di | Hi]; RightBy Apply: index_uniq.
Rewrite: Di (sub_default y 3!p' (leqnn ?)); Rewrite: -index_mem -leqNgt in Hpy.
By Apply: eqP; Rewrite: eqn_leq Hpy /index find_size.
Qed.

Lemma next_prev : (x : d) (next p (prev p x)) = x.
Proof.
Move=> x; Rewrite: next_sub mem_prev prev_sub.
Case Hpx: (p x) => [|] //; Case Dp: p Up Hpx => [|y p'] //.
Rewrite: -Dp; Move=> Hp Hpx; Pose i := (index x p').
Step Hi: (ltn i (size p)) By Rewrite: Dp /= ltnS /i /index find_size.
Rewrite: (index_uniq y Hi Hp); Case Hx: (p' x); LeftBy Apply: sub_index.
Rewrite: Dp /= /setU1 Hx orbF in Hpx; Rewrite (eqP Hpx).
Rewrite: -index_mem ltnNge -/i in Hx; Exact (sub_default ? (negbEf Hx)).
Qed.

Lemma cycle_next : (fcycle (next p) p).
Proof.
Case: p Up => [|x p'] Up' //; Apply/(pathPx x ? ? ?) => [i Hi].
Rewrite: size_add_last in Hi.
Rewrite: -cats1 -cat_adds sub_cat /= Hi /eqdf next_sub mem_sub //.
Rewrite: index_uniq // sub_cat /=; Rewrite: ltnS leq_eqVlt in Hi.
Case/setU1P: Hi => [Di | Hi]; RightBy Rewrite: Hi set11.
By Rewrite: Di ltnn subnn sub_default ?leqnn /= ?set11.
Qed.

Lemma cycle_prev : (cycle [x,y](x =d (prev p y)) p).
Proof.
Apply: etrans {}cycle_next; Symmetry; Case Dp: p => [|x p'] //.
Apply: eq_path; Rewrite: -Dp; Exact (monic2_eqd prev_next next_prev).
Qed.

Lemma cycle_from_next : (He : (x : d) (p x) -> (e x (next p x))) (cycle e p).
Proof.
Move=> He; Case Dp: p {}cycle_next => [|x p'] //; Rewrite: -Dp !(cycle_path x).
Step Hx: (p (last x p)) By Rewrite: Dp /= mem_lastU.
Move: (next p) He {Hx}(He ? Hx) => np.
Elim: {}p {x p' Dp}(last x p) => [|y p' Hrec] x He Hx //=.
Case/andP => [Dy Hp']; Rewrite: -{1 y}(eqP Dy) Hx /=.
Exact (Hrec ? [z; Hz](He ? (setU1r ? Hz)) (He ? (setU11 ? ?)) Hp').
Qed.

Lemma cycle_from_prev : (He : (x : d) (p x) -> (e (prev p x) x)) (cycle e p).
Proof.
Move=> He; Apply: cycle_from_next => [x Hx].
By Rewrite: -{1 x}prev_next He ?mem_next.
Qed.

Lemma next_rot : (next (rot n0 p)) =1 (next p).
Proof.
Move=> x; Def: Hp := cycle_next; Rewrite: -(cycle_rot n0) in Hp.
Case Hx: (p x); RightBy Rewrite: !next_sub mem_rot Hx.
Rewrite: -(mem_rot n0) in Hx; Exact (esym (eqP (next_cycle Hp Hx))).
Qed.

Lemma prev_rot : (prev (rot n0 p)) =1 (prev p).
Proof.
Move=> x; Def: Hp := cycle_prev; Rewrite: -(cycle_rot n0) in Hp.
Case Hx: (p x); RightBy Rewrite: !prev_sub mem_rot Hx.
Rewrite: -(mem_rot n0) in Hx; Exact (eqP (prev_cycle Hp Hx)).
Qed.

End UniqCycle.

Section UniqRotrCycle.

Variables n0 : nat; d : dataSet; p : (seq d).

Hypothesis Up : (uniq p).

Lemma next_rotr : (next (rotr n0 p)) =1 (next p).
Proof. Exact (next_rot ? Up). Qed.

Lemma prev_rotr : (prev (rotr n0 p)) =1 (prev p).
Proof. Exact (prev_rot ? Up). Qed.

End UniqRotrCycle.

Section UniqCycleRev.

Variable d : dataSet.

Lemma prev_rev : (p : (seq d)) (uniq p) -> (prev (rev p)) =1 (next p).
Proof.
Move=> p Up x; Case Hx: (p x); RightBy Rewrite: next_sub prev_sub mem_rev Hx.
Case/rot_to: Hx {}Up => [i p' Dp] Urp; Rewrite: -uniq_rev in Urp.
Rewrite: -(prev_rotr i Urp); Do 2 Rewrite: -(prev_rotr (1)) ?uniq_rotr //.
Rewrite: -rev_rot -(next_rot i Up) ~{i p Up Urp}Dp.
Case: p' => [|y p'] //; Rewrite: !rev_adds rotr1_add_last /= set11.
By Rewrite: -add_last_adds rotr1_add_last /= set11.
Qed.

Lemma next_rev : (p : (seq d)) (uniq p) -> (next (rev p)) =1 (prev p).
Proof. By Move=> p Up x; Rewrite: -{2 p}rev_rev prev_rev // uniq_rev. Qed.

End UniqCycleRev.

Section MapPath.

Variables d, d' : dataSet; h : d' -> d; e : (rel d); e' : (rel d').

Definition rel_base [b : (set d)] : Prop :=
  (x' : d'; Hx' : (b (h x')); y' : d') (e (h x') (h y')) = (e' x' y').

Lemma path_maps : (b : (set d); Hb : (rel_base b); x' : d'; p' : (seq d'))
  (sub_set (maps h (belast x' p')) b) ->
  (path e (h x') (maps h p')) = (path e' x' p').
Proof.
Move=> b Hb x' p'; Elim: p' x' => [|y' p' Hrec] x' //= Hbp.
Rewrite: (Hrec ? [y; H](Hbp ? (setU1r ? H))) Hb //.
Exact (Hbp ? (setU11 ? ?)).
Qed.

Hypothesis Hh : (injective h).

Lemma mem2_maps : (x', y' : d'; p' : (seq d'))
  (mem2 (maps h p') (h x') (h y')) = (mem2 p' x' y').
Proof. By Move=> *; Rewrite: {1}/mem2 (index_maps Hh) -maps_drop mem_maps. Qed.

Lemma next_maps : (p : (seq d')) (uniq p) ->
  (x : d') (next (maps h p) (h x)) = (h (next p x)).
Proof.
Move=> p Up x; Case Hx: (p x); RightBy Rewrite: !next_sub (mem_maps Hh) Hx.
Case/rot_to: Hx => [i p' Dp].
Rewrite: -(next_rot i Up); Rewrite: -(uniq_maps Hh) in Up.
Rewrite: -(next_rot i Up) -maps_rot ~{i p Up}Dp /=.
By Case: p' => [|y p] //=; Rewrite: !set11.
Qed.

Lemma prev_maps : (p : (seq d')) (uniq p) ->
  (x : d') (prev (maps h p) (h x)) = (h (prev p x)).
Proof.
Move=> p Up x; Rewrite: -{1 x}(next_prev Up) -(next_maps Up).
By Rewrite: prev_next ?uniq_maps.
Qed.

End MapPath.

Section CycleArc.

Variable d : dataSet.

Definition arc [p : (seq d); x, y : d] : (seq d) :=
  let px = (rot (index x p) p) in (take (index y px) px).

Lemma arc_rot : (i : nat; p : (seq d); Up : (uniq p))
  (x : d) (p x) -> (arc (rot i p) x) =1 (arc p x).
Proof.
Move=> i p Up x Hx y; Congr [q](take (index y q) q); Move: Up Hx {y}.
Rewrite: -{1 2 5 6 p}(cat_take_drop i) /rot uniq_cat; Case/and3P => [_ Hp _].
Rewrite: !drop_cat !take_cat !index_cat mem_cat /setU orbC.
Case Hx: (drop i p x) => [|] /=.
  Move=> _; Rewrite: (negbE (hasPn Hp ? Hx)).
  By Rewrite: index_mem Hx ltnNge leq_addr /= subn_addr catA.
By Move=> Hx'; Rewrite: Hx' index_mem Hx' ltnNge leq_addr /= subn_addr catA.
Qed.

Lemma left_arc : (x, y : d; p1, p2 : (seq d))
  let p = (Adds x (cat p1 (Adds y p2))) in
  (uniq p) -> (arc p x y) = (Adds x p1).
Proof.
Move=> x y p1 p2 p Up; Rewrite: /arc {1}/p /= set11 rot0.
Move: Up; Rewrite: /p -cat_adds uniq_cat index_cat; Move: (Adds x p1) => xp1.
Rewrite: /= negb_orb -!andbA; Case/and3P => [_ Hy _].
By Rewrite: (negbE Hy) set11 addn0 take_size_cat.
Qed.

Lemma right_arc : (x, y : d; p1, p2 : (seq d))
  let p = (Adds x (cat p1 (Adds y p2))) in
  (uniq p) -> (arc p y x) = (Adds y p2).
Proof.
Move=> x y p1 p2 p Up; Pose n := (size (Adds x p1)); Rewrite: -(arc_rot n Up).
  Move: Up; Rewrite: -(uniq_rot n) /p -cat_adds /n rot_size_cat.
  By Move=> *; Rewrite: /= left_arc.
By Rewrite: /p -cat_adds mem_cat /setU /= setU11 orbT.
Qed.

Inductive rot_to_arc_spec [p : (seq d); x, y : d] : Set :=
  RotToArcSpec : (i : nat; p1, p2 : (seq d))
   (Adds x p1) = (arc p x y) ->
   (Adds y p2) = (arc p y x) ->
   (rot i p) = (Adds x (cat p1 (Adds y p2))) ->
   (rot_to_arc_spec p x y).

Lemma rot_to_arc : (p : (seq d); Up : (uniq p))
  (x, y : d) (p x) -> (p y) -> (negb x =d y) -> (rot_to_arc_spec p x y).
Proof.
Move=> p Up x y Hx Hy Hxy; Case: (rot_to Hx) (Hy) (Up) => [i p' Dp] Hy'.
Rewrite: -(mem_rot i) Dp /= /setU1 (negbE Hxy) in Hy'; Rewrite: -(uniq_rot i) Dp.
Case/splitPr: p' / Hy' Dp => [p1 p2] Dp Up'; Exists i p1 p2; Auto.
  By Rewrite: -(arc_rot i Up Hx) Dp (left_arc Up').
By Rewrite: -(arc_rot i Up Hy) Dp (right_arc Up').
Qed.

(* These lemmas are mostly subsumed by the above, and might disappear. *)

Lemma cat_arc : (p : (seq d); Up : (uniq p))
  (x, y : d) (p x) -> (p y) -> (negb x =d y) ->
   {i : nat | (cat (arc p x y) (arc p y x)) = (rot i p)}.
Proof.
Move=> p Up x y Hx Hy Hxy; Case: (rot_to_arc Up Hx Hy Hxy) => [i p1 p2 [] [] Dp].
By Exists i.
Qed.

Lemma head_arc : (p : (seq d); x, y : d)
  (p x) -> (negb x =d y) ->
  {q : (seq d) | (Adds x q) = (arc p x y)}.
Proof.
Move=> p x y Hx Hxy; Exists (behead (arc p x y)); Unfold arc rot.
By Rewrite: (drop_sub x) ?index_mem ?sub_index // /= eqd_sym (negbE Hxy).
Qed.

End CycleArc.

Unset Implicit Arguments.


