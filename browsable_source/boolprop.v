(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require tacticext.
Require funs.
Require Export Bool.

(*   Lemmas for reflecting Prop to boolean expressions, using with the *)
(* reflect dependent inductive predicate defined below, and comparison *)
(* with true. The latter is made into a coercion, so b::Prop stands    *)
(* means b = true; conversely, a reflection property can be coerced to *)
(* its elimination lemma, so (r::(reflect P b) Hb::b) is a proof of P. *)
(*   In the following NEGATION is taken as the standard form of a      *)
(* false condition : hypotheses should be of the form (negb b) rather  *)
(* than b = false or ~b, as much as possible.                          *)
(*   A few lemmas to facilitate the manipulation of large conditionals *)
(* conclude this file.                                                 *)

Set Implicit Arguments.

Coercion is_true := [b](b = true).

Tactic Definition FoldIsTrue :=
  Match Context With [|- ?1 = true] -> Change (is_true ?1).

Lemma prop_congr : (b, b' : bool) b = b' -> <Prop> b == b'.
Proof. By Move=> b b' []. Qed.

Tactic Definition PropCongr := Apply: prop_congr.
  
Lemma is_true_true : true. Proof. Done. Qed.
Lemma not_is_true_false : ~false. Proof. Done. Qed.
Lemma is_true_locked_true : (locked true).
Proof. By Rewrite: -lock. Qed.
Lemma not_is_true_locked_false : ~(locked false).
Proof. By Rewrite: -lock. Qed.

Hints Resolve is_true_true is_true_locked_true.
Hints Resolve not_is_true_false not_is_true_locked_false.

Lemma negbI  : (b : bool) b = false -> (negb b). Proof. By Case. Qed.
Lemma negbE  : (b : bool) (negb b) -> b = false. Proof. By Case. Qed.
Lemma negbIf : (b : bool) b -> (negb b) = false. Proof. By Case. Qed.
Lemma negbEf : (b : bool) (negb b) = false -> b. Proof. By Case. Qed.
Lemma negbE2 : (b : bool) (negb (negb b)) -> b.  Proof. By Case. Qed.

Inductive reflect [P : Prop] : bool -> Set :=
  Reflect_true : P -> (reflect P true)
| Reflect_false : ~P -> (reflect P false).

Section Reflect.

Variables P : Prop; b : bool.

Lemma introP : (b -> P) -> ((negb b) -> ~P) -> (reflect P b).
Proof. Case b; Constructor; Auto. Qed.

Hypothesis Hb : (reflect P b).

Lemma introTF : (b' : bool) (if b' then P else ~P) -> b = b'.
Proof. By Case: Hb => [HbP|HbP] [|] // Hb'; Absurd P. Qed.

Lemma introNTF : (b' : bool) (if b' then ~P else P) -> (negb b) = b'.
Proof. By Case: Hb => [HbP|HbP] [|] // Hb'; Absurd P. Qed.

Lemma introT : P -> b.                 Proof. Exact (!introTF true). Qed.
Lemma introN : ~P -> (negb b).         Proof. Exact (!introNTF true). Qed.
Lemma introF : ~P -> b = false.        Proof. Exact (!introTF false). Qed.
Lemma introNF : P -> (negb b) = false. Proof. Exact (!introNTF false). Qed.

Lemma elimTF : (b' : bool) b = b' -> (if b' then P else ~P).
Proof. By Case: Hb => [HbP|HbP] b' []. Qed.

Lemma elimNTF : (b' : bool) (negb b) = b' -> (if b' then ~P else P).
Proof. By Case: Hb => [HbP|HbP] b' []. Qed.

Lemma elimT : b -> P.                 Proof. Exact (!elimTF true). Qed.
Lemma elimN : (negb b) -> ~P.         Proof. Exact (!elimNTF true). Qed.
Lemma elimF : b = false -> ~P.        Proof. Exact (!elimTF false). Qed.
Lemma elimNf : (negb b) = false -> P. Proof. Exact (!elimNTF false). Qed.

(* Reducing equality to equivalence. *)

Lemma iffP : (P' : Prop) (P -> P') -> (P' -> P) -> (reflect P' b).
Proof. Move=> *; Case Hb; Constructor; Auto. Qed.

Lemma sameP : (b' : bool) (reflect P b') -> b = b'.
Proof. By Move=> b' [Hb' | Hb']; Apply introTF. Qed.

Lemma equivP : (P' : Prop) (b' : bool) (reflect P' b') ->
                      (P -> P') -> (P' -> P) -> b = b'.
Proof. By Move=> P' b' [H | H]; Case Hb; Tauto. Qed.

Lemma equivNP : (P' : Prop) (b' : bool) (reflect P' b') ->
                      (P \/ P') -> ~(P /\ P') -> (negb b) = b'.
Proof. By Move=> P' b' [H | H]; Case Hb; Tauto. Qed.

Lemma equivPif : (P' : Prop) (P' -> P) -> (P -> P') -> if b then P' else ~P'.
Proof. By Case Hb; Tauto. Qed.

Lemma equivPifn : (P' : Prop) (P' \/ P) -> ~(P' /\ P) -> if b then ~P' else P'.
Proof. By Case Hb; Tauto. Qed.

Lemma decP : {P} + {~P}.
Proof. Case Hb; Auto. Qed.

End Reflect.

Coercion elimT : reflect >-> FUNCLASS.

(* Notations for wider connectives; WARNING: they associate to the right,     *)
(* because this is the natural orientation in most of the proof. It will be   *)
(* quite a bit of work to move to the v8 infix binary notation.               *)

Grammar constr constr0 : constr :=
  bool_and_3
    ["(" "and3b" constr9($b1) constr9($b2) constr9($b3) ")"] ->
  [(andb $b1 (andb $b2 $b3))]
| bool_and_4
    ["(" "and4b" constr9($b1) constr9($b2) constr9($b3) constr9($b4) ")"] ->
  [(andb $b1 (andb $b2 (andb $b3 $b4)))]
| bool_and_5
    ["(" "and5b" constr9($b1) constr9($b2) constr9($b3)
                 constr9($b4) constr9($b5) ")"] ->
  [(andb $b1 (andb $b2 (andb $b3 (andb $b4 $b5))))]
| bool_or_3
    ["(" "or3b" constr9($b1) constr9($b2) constr9($b3) ")"] ->
  [(orb $b1 (orb $b2 $b3))]
| bool_or_4
    ["(" "or4b" constr9($b1) constr9($b2) constr9($b3) constr9($b4) ")"] ->
  [(orb $b1 (orb $b2 (orb $b3 $b4)))].

Syntax constr level 0:
    bool_and_pp [(andb $b1 $b2)] ->
      [ (OPFORM andb $b1 $b2) ]
  | bool_and3_pp [(andb $b1 (andb $b2 $b3))] ->
      [ (OPFORM and3b $b1 $b2 $b3) ]
  | bool_and4_pp [(andb $b1 (andb $b2 (andb $b3 $b4)))] ->
      [ (OPFORM and4b $b1 $b2 $b3 $b4) ]
  | bool_and5_pp [(andb $b1 (andb $b2 (andb $b3 (andb $b4 $b5))))] ->
      [ (OPFORM and5b $b1 $b2 $b3 $b4 $b5) ]
  | bool_or_pp [(orb $b1 $b2)] ->
      [ (OPFORM orb $b1 $b2) ]
  | bool_or3_pp [(orb $b1 (orb $b2 $b3))] ->
      [ (OPFORM or3b $b1 $b2 $b3) ]
  | bool_or4_pp [(orb $b1 (orb $b2 (orb $b3 $b4)))] ->
      [ (OPFORM or4b $b1 $b2 $b3 $b4) ].

Inductive and3 [P, Q, R : Prop] : Prop :=
  And3 : P -> Q -> R -> (and3 P Q R).

Inductive and4 [P, Q, R, S : Prop] : Prop :=
  And4 : P -> Q -> R -> S -> (and4 P Q R S).

Inductive and5 [P, Q, R, S, T : Prop] : Prop :=
  And5 : P -> Q -> R -> S -> T -> (and5 P Q R S T).

Inductive or3 [P, Q, R : Prop] : Prop :=
  Or3_1 : P -> (or3 P Q R)
| Or3_2 : Q -> (or3 P Q R)
| Or3_3 : R -> (or3 P Q R).

Inductive or4 [P, Q, R, S : Prop] : Prop :=
  Or4_1 : P -> (or4 P Q R S)
| Or4_2 : Q -> (or4 P Q R S)
| Or4_3 : R -> (or4 P Q R S)
| Or4_4 : S -> (or4 P Q R S).

Syntax constr level 0:
    and3_pp [(and3 $p1 $p2 $p3)] ->
      [ (OPFORM and3 $p1 $p2 $p3) ]
  | and4_pp [(and4 $p1 $p2 $p3 $p4)] ->
      [ (OPFORM and4 $p1 $p2 $p3 $p4) ]
  | and5_pp [(and5 $p1 $p2 $p3 $p4 $p5)] ->
      [ (OPFORM and5 $p1 $p2 $p3 $p4 $p5) ]
  | or3_pp [(or3 $p1 $p2 $p3)] ->
      [ (OPFORM or3 $p1 $p2 $p3) ]
  | or4_pp [(or4 $p1 $p2 $p3 $p4)] ->
      [ (OPFORM or4 $p1 $p2 $p3 $p4) ].

Section ReflectConnectives.

Variables b1, b2, b3, b4, b5 : bool.

Lemma idPx : (reflect b1 b1).
Proof. By Case b1; Constructor. Qed.

Lemma idPnx : (reflect (negb b1) (negb b1)).
Proof. By Case b1; Constructor. Qed.

Lemma negPx : (reflect ~b1 (negb b1)).
Proof. By Case b1; Constructor; Auto. Qed.

Lemma negPnx : (reflect b1 (negb (negb b1))).
Proof. By Case b1; Constructor. Qed.

Lemma negPfx : (reflect b1 = false (negb b1)).
Proof. By Case b1; Constructor. Qed.

Lemma andPx : (reflect b1 /\ b2 (andb b1 b2)).
Proof. By Case b1; Case b2; Constructor; Try By Case. Qed.

Lemma and3Px : (reflect (and3 b1 b2 b3) (and3b b1 b2 b3)).
Proof. By Case b1; Case b2; Case b3; Constructor; Try By Case. Qed.

Lemma and4Px : (reflect (and4 b1 b2 b3 b4) (and4b b1 b2 b3 b4)).
Proof. By Case b1; Case b2; Case b3; Case b4; Constructor; Try By Case. Qed.

Lemma and5Px : (reflect (and5 b1 b2 b3 b4 b5) (and5b b1 b2 b3 b4 b5)).
Proof.
By Case b1; Case b2; Case b3; Case b4; Case b5; Constructor; Try By Case.
Qed.

Lemma orPx : (reflect b1 \/ b2 (orb b1 b2)).
Proof. By Case b1; Case b2; Constructor; Auto; Case. Qed.

Lemma or3Px : (reflect (or3 b1 b2 b3) (or3b b1 b2 b3)).
Proof.
Case b1; LeftBy Constructor; Constructor 1.
Case b2; LeftBy Constructor; Constructor 2.
Case b3; LeftBy Constructor; Constructor 3.
By Constructor; Case.
Qed.

Lemma or4Px : (reflect (or4 b1 b2 b3 b4) (or4b b1 b2 b3 b4)).
Proof.
Case b1; LeftBy Constructor; Constructor 1.
Case b2; LeftBy Constructor; Constructor 2.
Case b3; LeftBy Constructor; Constructor 3.
Case b4; LeftBy Constructor; Constructor 4.
By Constructor; Case.
Qed.

Lemma nandPx : (reflect (negb b1) \/ (negb b2) (negb (andb b1 b2))).
Proof. Case b1; Case b2; Constructor; Auto; Case; Auto. Qed.

Lemma norPx : (reflect (negb b1) /\ (negb b2) (negb (orb b1 b2))).
Proof. Case b1; Case b2; Constructor; Auto; Case; Auto. Qed.

End ReflectConnectives.

Syntactic Definition idP   := idPx   | 1.
Syntactic Definition idPn  := idPnx   | 1.
Syntactic Definition negP  := negPx  | 1.
Syntactic Definition negPn := negPnx  | 1.
Syntactic Definition negPf := negPfx  | 1.
Syntactic Definition andP  := andPx  | 2.
Syntactic Definition and3P := and3Px | 3.
Syntactic Definition and4P := and4Px | 4.
Syntactic Definition and5P := and5Px | 5.
Syntactic Definition orP   := orPx   | 2.
Syntactic Definition or3P  := or3Px  | 3.
Syntactic Definition or4P  := or4Px  | 4.
Syntactic Definition nandP := nandPx | 2.
Syntactic Definition norP  := norPx  | 2.

(* Lemmas and tactics for the reflection of a negated condition.               *)

Section ReflectNegb.

Variables P : Prop; b : bool; Hnb : (reflect P (negb b)).

Lemma introTFn: (b' : bool) (if b' then ~P else P) -> b = b'.
Proof. Rewrite: -{b}negb_elim; Exact (introNTF Hnb). Qed.

Lemma elimTFn: (b' : bool)  b = b' -> (if b' then ~P else P).
Proof. Rewrite: -{b}negb_elim; Exact (elimNTF Hnb). Qed.

Lemma introTn : ~P -> b.        Proof. Exact (!introTFn true). Qed.
Lemma introFn : P -> b = false. Proof. Exact (!introTFn false). Qed.
Lemma elimTn : b -> ~P.         Proof. Exact (!elimTFn true). Qed.
Lemma elimFn : b = false -> P.  Proof. Exact (!elimTFn false). Qed.

End ReflectNegb.

(* Shorter, more systematic names for the boolean connectives laws.       *)

Lemma andTb : (b : bool) (andb true b) = b.      Proof. Done. Qed.
Lemma andFb : (b : bool) (andb false b) = false. Proof. Done. Qed.
Lemma andbT : (b : bool) (andb b true) = b.      Proof. By Case. Qed.
Lemma andbF : (b : bool) (andb b false) = false. Proof. By Case. Qed.
Lemma andbb : (b : bool) (andb b b) = b.         Proof. By Case. Qed.

Lemma andbC : (b, b' : bool) (andb b b') = (andb b' b).
Proof. By Do 2 Case. Qed.

Lemma andbA : (b, b', b'' : bool) (and3b b b' b'') = (andb (andb b b') b'').
Proof. By Do 3 Case. Qed.

Lemma andbCA : (b, b', b'' : bool) (and3b b b' b'') = (and3b b' b b'').
Proof. By Do 3 Case. Qed.

Lemma orTb : (b : bool) (orb true b) = true. Proof. Done. Qed.
Lemma orFb : (b : bool) (orb false b) = b.   Proof. Done. Qed.
Lemma orbT : (b : bool) (orb b true) = true. Proof. By Case. Qed.
Lemma orbF : (b : bool) (orb b false) = b.   Proof. By Case. Qed.
Lemma orbb : (b : bool) (orb b b) = b.       Proof. By Case. Qed.

Lemma orbC : (b, b' : bool) (orb b b') = (orb b' b).
Proof. By Do 2 Case. Qed.

Lemma orbA : (b, b', b'' : bool) (or3b b b' b'') = (orb (orb b b') b'').
Proof. By Do 3 Case. Qed.

Lemma orbCA : (b, b', b'' : bool) (or3b b b' b'') = (or3b b' b b'').
Proof. By Do 3 Case. Qed.

(* Finally, an alternative to xorb that behaves somewhat better wrt Simpl. *)

Definition addb [b : bool] : bool -> bool := if b then negb else [b']b'.

Lemma addTb : (b : bool) (addb true b) = (negb b). Proof. Done. Qed.
Lemma addFb : (b : bool) (addb false b) = b. Proof. Done. Qed.
Lemma addbT : (b : bool) (addb b true) = (negb b). Proof. By Case. Qed.
Lemma addbF : (b : bool) (addb b false) = b. Proof. By Case. Qed.
Lemma addbb : (b : bool) (addb b b) = false. Proof. By Case. Qed.

Lemma addbC : (b, b' : bool) (addb b b') = (addb b' b).
Proof. By Do 2 Case. Qed.

Lemma addbA : (b, b', b'' : bool)
  (addb b (addb b' b'')) = (addb (addb b b') b'').
Proof. By Do 3 Case. Qed.

Lemma addbCA : (b, b', b'' : bool)
  (addb b (addb b' b'')) = (addb b' (addb b b'')).
Proof. By Do 3 Case. Qed.

Lemma addb_inv : (b, b' : bool) (addb b (addb b b')) = b'.
Proof. By Do 2 Case. Qed.

Lemma addb_movell : (b, b', b'' : bool) (addb b b') = b'' -> b' = (addb b b'').
Proof. By Do 3 Case. Qed.

Lemma addb_movelr : (b, b', b'' : bool) (addb b b') = b'' -> b' = (addb b'' b).
Proof. By Do 3 Case. Qed.

Lemma addb_moverl : (b, b', b'' : bool) (addb b b') = b'' -> b = (addb b' b'').
Proof. By Do 3 Case. Qed.

Lemma addb_moverr : (b, b', b'' : bool) (addb b b') = b'' -> b = (addb b'' b').
Proof. By Do 3 Case. Qed.

Lemma addbP : (b1, b2 : bool) (addb b1 b2) -> (negb b1) = b2.
Proof. By Do 2 Case. Qed.

(* Resolution tactic for blindly weeding out common terms from boolean       *)
(* equalities. When faced with a goal of the form (andb/orb/addb b1 b2) = b' *)
(* they will try to locate b1 in b' and remove it. This can fail!            *)

Tactic Definition BoolCongr :=
  Match Context With
    [|- (andb ?1 ?2) = ?3] ->
      First [
        Symmetry; Rewrite: -1?(andbC ?1) -?(andbCA ?1);
        Refine (congr (andb ?1) ?); Symmetry
      | Case ?1; [Rewrite: ?andTb ?andbT | By Rewrite: /= ?andbF]]
  | [|- (orb ?1 ?2) = ?3] ->
      First [
        Symmetry; Rewrite: -1?(orbC ?1) -?(orbCA ?1);
        Refine (congr (orb ?1) ?); Symmetry
      | Case ?1; [By Rewrite: /= ?orbT | Rewrite: ?orFb ?orbF]]
  | [|- (addb ?1 ?2) = ?3] ->
      Symmetry; Rewrite: -1?(addbC ?1) -?(addbCA ?1);
      Refine (congr (addb ?1) ?); Symmetry
  | [|- (negb ?1) = ?2 ] ->
      Refine (congr negb ?).

(* Tactics for proving and using boolean predicates (see tacticext.v). *)

Grammar tactic simple_tactic : ast :=
  move_view_gens
    ["Move" "/" command:command($view) ":" ext_gen($gt) ext_gens($eg)
                      ext_simpl_intros_opt_tacs($si)] ->
  let (GT $pat ($LIST $ids2)) = [$gt] in
  let (EG (T ($LIST $t1o)) (G ($LIST $terms)) ($LIST $ids1)) = [$eg] in
  let (T ($LIST $t2o)) = case [(Generalize ($LIST $terms))] of
    (Generalize) -> [(T)]
  | $t2 -> [(T $t2)]
  esac in
  let (T ($LIST $t34o)) =  case [$pat] of
    (PATTERN (COMMAND $term)) ->
    [(T <:tactic:<First [
       Move: (elimNTF $view $term) | Move: (elimTF $view $term)
     | Move: (elimTFn $view $term) | Move: ($view $term)]>>)]
  | (PATTERN (COMMAND $term) ($LIST $occ)) ->
    let $p3 = [(PATTERN <:tactic:<'($view $term)>> ($LIST $occ))] in
    let $t3 = [(Reduce (REDEXP (Pattern $p3)) (CLAUSE))] in
    [(T $p3 <:tactic:<GeneralizePattern>>)]
  esac in
  let (I (S ($LIST $s)) ($LIST $t6o)) = [$si] in
  let (T ($LIST $t5o)) = case [(CLAUSE ($LIST $ids1) ($LIST $ids2))] of
    (CLAUSE) -> [(T ($LIST $s))]
  | $clause -> [(T ($LIST $s) (Clear $clause))]
  esac in
  case [(T ($LIST $t1o) ($LIST $t2o) ($LIST $t34o) ($LIST $t5o) ($LIST $t6o))] of
    (T $t1)                     -> [$t1]
  | (T $t1 $t2)                 -> [<:tactic:<$t1; $t2>>]
  | (T $t1 $t2 $t3)             -> [<:tactic:<$t1; $t2; $t3>>]
  | (T $t1 $t2 $t3 $t4)         -> [<:tactic:<$t1; $t2; $t3; $t4>>]
  | (T $t1 $t2 $t3 $t4 $t5)     -> [<:tactic:<$t1; $t2; $t3; $t4; $t5>>]
  | (T $t1 $t2 $t3 $t4 $t5 $t6) -> [<:tactic:<$t1; $t2; $t3; $t4; $t5; $t6>>]
  | (T $t1 $t2 $t3 $t4 $t5 $t6 $t7) ->
                              [<:tactic:<$t1; $t2; $t3; $t4; $t5; $t6; $t7>>]
  esac
| move_view_eq_gens
    ["Move" "/" command:command($view) identarg($eqname) ":"
      ext_gen($gt) ext_gens($eg) ext_move_simpl_intros_eq_opt_tacs($si)] ->
  let (GT (PATTERN (COMMAND $term) ($LIST $occ)) ($LIST $_)) = [$gt] in
  let (EG (T ($LIST $t1o)) (G ($LIST $terms)) ($LIST $ids1)) = [$eg] in
  let (T ($LIST $t24o)) = 
    let $p3 = [(PATTERN <:tactic:<'($view $term)>> ($LIST $occ))] in
    let $t3 = [(Reduce (REDEXP (Pattern $p3)) (CLAUSE))] in
    let $t4 = [<:tactic:<GeneralizeEqPattern>>] in
    case [(Generalize ($LIST $terms))] of
        (Generalize) -> [(T $t3 $t4)]
      | $t2 -> [(T $t2 $t3 $t4)]
    esac
  in
  let (I (S ($LIST $s)) $t7a) = [$si] in
  let (T ($LIST $t5o)) = case [(CLAUSE ($LIST $ids1))] of
    (CLAUSE) -> [(T ($LIST $s))]
  | $clause -> [(T ($LIST $s) (Clear $clause))]
  esac in
  let $t6a = [<:tactic:<Let ext_eq_name = $eqname In $t7a>>] in
  case [(T ($LIST $t1o) ($LIST $t24o) ($LIST $t5o) $t6a)] of
    (T $t1 $t2 $t3)             -> [<:tactic:<$t1; $t2; $t3>>]
  | (T $t1 $t2 $t3 $t4)         -> [<:tactic:<$t1; $t2; $t3; $t4>>]
  | (T $t1 $t2 $t3 $t4 $t5)     -> [<:tactic:<$t1; $t2; $t3; $t4; $t5>>]
  | (T $t1 $t2 $t3 $t4 $t5 $t6) -> [<:tactic:<$t1; $t2; $t3; $t4; $t5; $t6>>]
  | (T $t1 $t2 $t3 $t4 $t5 $t6 $t7) ->
                              [<:tactic:<$t1; $t2; $t3; $t4; $t5; $t6; $t7>>]
  esac
| move_view_defective
    ["Move"  "/" command:command($view) opt_clear($ids)
      ext_simpl_intros_opt_tacs($si)] ->
  let $var = [defective_term] in
  let $t1a = [<:tactic:<Intros $var; First [
       Move: (elimNTF $view $var) | Move: (elimTF $view $var)
     | Move: (elimTFn $view $var) | Move: ($view $var)]>>] in
  let $t3a = [(Clear (CLAUSE (INHYP $var) ($LIST $ids)))] in
  let (I (S ($LIST $t2o)) ($LIST $t4o)) = [$si] in
  case [(T $t1a ($LIST $t2o) $t3a ($LIST $t4o))] of
    (T $t1 $t2)                 -> [<:tactic:<$t1; $t2>>]
  | (T $t1 $t2 $t3)             -> [<:tactic:<$t1; $t2; $t3>>]
  | (T $t1 $t2 $t3 $t4)         -> [<:tactic:<$t1; $t2; $t3; $t4>>]
  esac.

Grammar tactic simple_tactic : ast :=
  case_view_gens
    ["Case" "/" command:command($view) ":" ext_gen($gt) ext_dgens($eg)
      ext_case_opt_intros($ds)] ->
  let (GT $pat ($LIST $ids2)) = [$gt] in
  let (EG (T ($LIST $t1o)) $gen ($LIST $ids1)) = [$eg] in
  case [$gen] of
    (G ($LIST $terms)) ->
    let (T ($LIST $t2o)) = case [(Generalize ($LIST $terms))] of
      (Generalize) -> [(T)] | $t2 -> [(T $t2)] esac in
    let (T ($LIST $t34o)) = case [$pat] of
      (PATTERN (COMMAND $term)) ->
      [(T <:tactic:<First [
          Case (elimNTF $view $term) | Case (elimTF $view $term)
        | Case (elimTFn $view $term) | Case ($view $term)]>>)]
    | (PATTERN (COMMAND $term) ($LIST $occ)) ->
      let $vterm = [<:tactic:<'($view $term)>>] in
      let $p3 = [(PATTERN $vterm ($LIST $occ))] in
      let $t3 = [(Reduce (REDEXP (Pattern $p3)) (CLAUSE))] in
      [(T (Reduce (REDEXP (Pattern $p3)) (CLAUSE)) (Case $term (BINDINGS)))]
    esac in
    let (D (S ($LIST $t5o)) ($LIST $t78o)) = [$ds] in
    let (T ($LIST $t58o)) = case [(CLAUSE ($LIST $ids1) ($LIST $ids2))] of
      (CLAUSE) -> [(T ($LIST $t5o) ($LIST $t78o))]
    | $clause -> [(T ($LIST $t5o) (Clear $clause) ($LIST $t78o))]
    esac in
    case [(T ($LIST $t1o) ($LIST $t2o) ($LIST $t34o) ($LIST $t58o))] of
      (T $t1)                     -> [$t1]
    | (T $t1 $t2)                 -> [<:tactic:<$t1; $t2>>]
    | (T $t1 $t2 $t3)             -> [<:tactic:<$t1; $t2; $t3>>]
    | (T $t1 $t2 $t3 $t4)         -> [<:tactic:<$t1; $t2; $t3; $t4>>]
    | (T $t1 $t2 $t3 $t4 $t5)     -> [<:tactic:<$t1; $t2; $t3; $t4; $t5>>]
    | (T $t1 $t2 $t3 $t4 $t5 $t6) -> [<:tactic:<$t1; $t2; $t3; $t4; $t5; $t6>>]
    | (T $t1 $t2 $t3 $t4 $t5 $t6 $t7) ->
                                  [<:tactic:<$t1; $t2; $t3; $t4; $t5; $t6; $t7>>]
    | (T $t1 $t2 $t3 $t4 $t5 $t6 $t7 $t8) ->
                             [<:tactic:<$t1; $t2; $t3; $t4; $t5; $t6; $t7; $t8>>]
    esac
  | (D (P ($LIST $pats)) $bpat ($LIST $_)) ->
    let $var = [viewed_term] in
    let $t2a = case [$bpat] of
      (PATTERN (COMMAND $term)) -> [<:tactic:<Move/$view: ($term) => $var>>]
    | (PATTERN (COMMAND $term) ($LIST $occ)) ->
      let $p2 = [(PATTERN <:tactic:<'($view $term)>> ($LIST $occ))] in
      let $t2 = [(Reduce (REDEXP (Pattern $p2)) (CLAUSE))] in
      [<:tactic:<$t2; GeneralizePattern; Intros $var>>]
    esac in
    let $vterm = [(COMMAND (QUALID $var))] in
    let $t3a =
      let $p3 = [(Pattern $pat ($LIST $pats) (PATTERN $vterm))] in
      [(Reduce (REDEXP $p3) (CLAUSE))] in 
    let $t4a = [(Case $vterm (BINDINGS))] in
    let $t6a = [(Clear (CLAUSE (INHYP $var) ($LIST $ids1) ($LIST $ids2)))] in
    let (D (S ($LIST $t5o)) ($LIST $t78o)) = [$ds] in
    case [(T ($LIST $t1o) $t2a $t3a $t4a ($LIST $t5o) $t6a ($LIST $t78o))] of
      (T $t1 $t2 $t3 $t4)         -> [<:tactic:<$t1; $t2; $t3; $t4>>]
    | (T $t1 $t2 $t3 $t4 $t5)     -> [<:tactic:<$t1; $t2; $t3; $t4; $t5>>]
    | (T $t1 $t2 $t3 $t4 $t5 $t6) -> [<:tactic:<$t1; $t2; $t3; $t4; $t5; $t6>>]
    | (T $t1 $t2 $t3 $t4 $t5 $t6 $t7) ->
                                  [<:tactic:<$t1; $t2; $t3; $t4; $t5; $t6; $t7>>]
    | (T $t1 $t2 $t3 $t4 $t5 $t6 $t7 $t8) ->
                             [<:tactic:<$t1; $t2; $t3; $t4; $t5; $t6; $t7; $t8>>]
    esac
  esac
| case_view_eq_gens
    ["Case" "/" command:command($view) identarg($eqname) ":" 
     ext_gen($gt) ext_dgens($eg) ext_case_opt_intros($ds)] ->
  let (GT $pat ($LIST $_)) = [$gt] in
  let (EG (T ($LIST $t1o)) $gen ($LIST $ids1)) = [$eg] in
  let (T (S ($LIST $t5o)) ($LIST $t78o)) = case [$ds] of
    (D $s) -> [(T $s <:tactic:<IntrosUntilName $eqname>>)]
  | (D $s (Intros)) -> [(T $s (Intros))]
  | (D $s $t7) -> [(T $s $t7 <:tactic:<Intros $eqname>>)]
  | (D $s $t7 $t8) -> [(T $s $t7 <:tactic:<Intros $eqname; $t8>>)]
  esac in
  case [$gen] of
    (G ($LIST $terms)) ->
    let (T ($LIST $t2o)) = case [(Generalize ($LIST $terms))] of
      (Generalize) -> [(T)] | $t2 -> [(T $t2)] esac in
    let (PATTERN (COMMAND $term) ($LIST $occ)) = [$pat] in
    let $vpat = [(PATTERN <:tactic:<'($view $term)>> ($LIST $occ))] in
    let $t3a = [(Reduce (REDEXP (Pattern $vpat)) (CLAUSE))] in  
    let $t34a = [<:tactic:<$t3a; CaseWithEq $eqname>>] in
    let (T ($LIST $t56o)) = case [(CLAUSE ($LIST $ids1))] of
      (CLAUSE) -> [(T ($LIST $t5o))]
    | $clause -> [(T ($LIST $t5o) (Clear $clause))]
    esac in
    case [(T ($LIST $t1o) ($LIST $t2o) $t34a ($LIST $t56o) ($LIST $t78o))] of
      (T $t1 $t2)                 -> [<:tactic:<$t1; $t2>>]
    | (T $t1 $t2 $t3)             -> [<:tactic:<$t1; $t2; $t3>>]
    | (T $t1 $t2 $t3 $t4)         -> [<:tactic:<$t1; $t2; $t3; $t4>>]
    | (T $t1 $t2 $t3 $t4 $t5)     -> [<:tactic:<$t1; $t2; $t3; $t4; $t5>>]
    | (T $t1 $t2 $t3 $t4 $t5 $t6) -> [<:tactic:<$t1; $t2; $t3; $t4; $t5; $t6>>]
    | (T $t1 $t2 $t3 $t4 $t5 $t6 $t7) ->
                                  [<:tactic:<$t1; $t2; $t3; $t4; $t5; $t6; $t7>>]
    esac
  | (D (P ($LIST $pats)) $bpat ($LIST $ise)) ->
    let (PATTERN $term ($LIST $_)) = [$pat] in
    let $var = [viewed_term] in
    let $t2a = case [$bpat] of
      (PATTERN (COMMAND $bterm)) -> [<:tactic:<Move/$view: ($bterm) => $var>>]
    | (PATTERN (COMMAND $bterm) ($LIST $occ)) ->
      let $p2 = [(PATTERN <:tactic:<'($view $bterm)>> ($LIST $occ))] in
      let $t2 = [(Reduce (REDEXP (Pattern $p2)) (CLAUSE))] in
      [<:tactic:<$t2; GeneralizePattern; Intros $var>>]
    esac in
    let $vterm = [(COMMAND (QUALID $var))] in
    let $vpat = [(PATTERN $vterm)] in
    let $t6a = [(Clear (CLAUSE (INHYP $var) ($LIST $ids1)))] in
    let $isepat = [(APPLIST (META 1) (ISEVAR) (ISEVAR) ($LIST $ise))] in
    let $t34a =
      let $dpat = [(PATTERN (COMMAND (QUALID eqdep_var)) 2)] in
      let $p3 = [(Pattern $dpat $pat ($LIST $pats) $vpat)] in
      let $t3a = [(Reduce (REDEXP $p3) (CLAUSE))] in
      let $t4arg = [<:tactic:<Pose EqDepBody := ?1>>] in
      let $t4 = [<:tactic:<Match Context With [|- $isepat] -> $t4arg>>] in
      [<:tactic:<CaseWithDepEq $eqname $term $vterm ($t3a; $t4)>>] in
    case [(T ($LIST $t1o) $t2a $t34a ($LIST $t5o) $t6a ($LIST $t78o))] of
      (T $t1 $t2 $t3 $t4)         -> [<:tactic:<$t1; $t2; $t3; $t4>>]
    | (T $t1 $t2 $t3 $t4 $t5)     -> [<:tactic:<$t1; $t2; $t3; $t4; $t5>>]
    | (T $t1 $t2 $t3 $t4 $t5 $t6) -> [<:tactic:<$t1; $t2; $t3; $t4; $t5; $t6>>]
    | (T $t1 $t2 $t3 $t4 $t5 $t6 $t7) ->
                                  [<:tactic:<$t1; $t2; $t3; $t4; $t5; $t6; $t7>>]
    esac
  esac
| case_view_defective
    ["Case" "/" command:command($view) opt_clear($ids)
      ext_case_opt_intros($ds)] ->
  let $var = [defective_term] in
  let $t1a = [<:tactic:<Intros $var; First [
       Case (elimNTF $view $var) | Case (elimTF $view $var)
     | Case (elimTFn $view $var) | Case ($view $var)]>>] in
  let $t3a = [(Clear (CLAUSE (INHYP $var) ($LIST $ids)))] in
  let (D (S ($LIST $t2o)) ($LIST $t45o)) = [$ds] in
  case [(T $t1a ($LIST $t2o) $t3a ($LIST $t45o))] of
    (T $t1 $t2)                 -> [<:tactic:<$t1; $t2>>]
  | (T $t1 $t2 $t3)             -> [<:tactic:<$t1; $t2; $t3>>]
  | (T $t1 $t2 $t3 $t4)         -> [<:tactic:<$t1; $t2; $t3; $t4>>]
  | (T $t1 $t2 $t3 $t4 $t5)     -> [<:tactic:<$t1; $t2; $t3; $t4; $t5>>]
  esac.

Grammar tactic simple_tactic : ast :=
  apply_view
    ["Apply" "/" command:command($prop) ext_case_opt_intros($ds)] ->
  let $t1a = [<:tactic:<First [ Refine (introNTF $prop ?)
             | Refine (introTF $prop ?) | Refine (introTFn $prop ?)]>>] in
  let (D (S ($LIST $t2o)) ($LIST $t34o)) = [$ds] in
  case [(T $t1a ($LIST $t2o) ($LIST $t34o))] of
    (T $t1)                     -> [$t1]
  | (T $t1 $t2)                 -> [<:tactic:<$t1; $t2>>]
  | (T $t1 $t2 $t3)             -> [<:tactic:<$t1; $t2; $t3>>]
  | (T $t1 $t2 $t3 $t4)         -> [<:tactic:<$t1; $t2; $t3; $t4>>]
  esac.

Lemma if_neg_Prop : (b : bool; P, P' : Prop)
 (if (negb b) then P else P') == (if b then P' else P).
Proof. By Case. Qed.

Tactic Definition RefineEquiv refine1 refine2 :=
  refine1; Rewrite: ?if_neg_Prop;
  First [refine2 | Rewrite: -if_neg_Prop; refine2].

Grammar tactic simple_tactic : ast :=
  apply_view_view
    ["Apply" "/" command:command($prop1)  "/" command:command($prop2)
       ext_case_opt_intros($ds)] ->
  let $tp2 = [<:tactic:<First [
    Refine (equivPif $prop2 ? ?) | Refine (equivPifn $prop2 ? ?)]>>] in
  let $t1a = [<:tactic:<RefineEquiv (Apply/$prop1) ($tp2)>>] in
  let (D (S ($LIST $t2o)) ($LIST $t34o)) = [$ds] in
  case [(T $t1a ($LIST $t2o) ($LIST $t34o))] of
    (T $t1)                     -> [$t1]
  | (T $t1 $t2)                 -> [<:tactic:<$t1; $t2>>]
  | (T $t1 $t2 $t3)             -> [<:tactic:<$t1; $t2; $t3>>]
  | (T $t1 $t2 $t3 $t4)         -> [<:tactic:<$t1; $t2; $t3; $t4>>]
  esac.

(* The following lemmas are mainly useful for ifs with large conditions : *)
(* they allow reasoning about the condition without repeating it inside   *)
(* the proof (the latter IS preferable when the condition is short).      *)
(* Usage :                                                                *)
(*   if the goal has the form (if cond then ...) = ...                    *)
(*     Apply cases_of_if; Move=> Dcond.                                   *)
(*   generates two subgoal, with the assumption Dcond : cond = true/false *)
(*     Rewrite if_same  eliminates redundant ifs                          *)
(*     Rewrite (fun_if f) moves a function f inside an if                 *)
(*     Rewrite if_arg moves an argument inside a function-valued if       *)

Lemma cases_of_if : (A : Set; b : bool; v1, v2, v3 : A)
  (b -> v1 = v3) -> (b = false -> v2 = v3) -> (if b then v1 else v2) = v3.
Proof. Move=> A [|]; Auto. Qed.

Lemma if_same : (A : Set; b : bool; v : A)
  (if b then v else v) = v.
Proof. By Move=> A [|]. Qed.

Lemma fun_if : (A, B : Set; f : A -> B; b : bool; v1, v2 : A)
  (f (if b then v1 else v2)) = (if b then (f v1) else (f v2)).
Proof. By Move=> A B f [|]. Qed.

Lemma if_arg : (A : Set; x : A; b : bool; B : Set; f1, f2 : A -> B)
  ((if b then f1 else f2) x) = (if b then (f1 x) else (f2 x)).
Proof. By Move=> A x [|]. Qed.

(* These lemmatas were useful for xorb, but they should not be needed now.

Lemma ifb_idb : (b : bool) (if b then true else false) = b.
Proof. By Case. Qed.

Lemma ifb_negb : (b : bool) (if b then false else true) = (negb b).
Proof. By Case. Qed.

*)

Unset Implicit Arguments.
