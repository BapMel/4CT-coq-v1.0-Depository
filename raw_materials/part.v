(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require tacticext.
Require boolprop.
Require funs.
Require dataset.
Require natprop.
Require seq.
Require paths.
Require finset.
Require connect.
Require hypermap.
Require color.
Require geometry.

Set Implicit Arguments.

(*    These "parts" are patterns for performing local matching on graphs. *)
(* Specifically, a part specifies ranges of arities for darts in the      *)
(* second neighborhood of some match anchor x, using the "prange" type    *)
(* below to specify ranges.                                               *)
(*   A part is broken into a sequence of subparts, with each subpart      *)
(* specifying arities in successive sectors around the "hub" x, following *)
(* a counterclockwise order. Each subpart comprises a "spoke" (darts      *)
(* immediately adjacent to x; the spoke of the first sector is the face   *)
(* orbit of (edge x)), a "hat" (non-hub darts adjacent to this spoke and  *)
(* the previous spoke; (edge (face (face (edge x)))) is in the hat of the *)
(* first spoke), and "fans" (other darts adjacent to the spoke, listed    *)
(* counterclockwise). This is a partition; the hat of the next spoke is   *)
(* not a fan of the current one.                                          *)
(*   A part fits a dart x when all its subparts fit x, (face x), etc,     *)
(* respectively; it fits exactly when, in addition, its length is equal   *)
(* to the arity of x.                                                     *)
(*   Because parts are created and traversed in the inner loop of the     *)
(* unavoidability checks their representation is somewhat optimised. The  *)
(* list structure is merged into the record structure, and there are four *)
(* different kinds of parts, according to the number of (known) fans. The *)
(* spoke arity is always fixed when there are known fans (e.g., if there  *)
(* are two known fans, the spoke is a heptagon). The converse isn't true, *)
(* in fact we never use the explicit fan form when there are no           *)
(* nontrivial fan constraints (this simplifies the converse part          *)
(* computation, but isn't strictly necessary for correctness).            *)
(*   Parts are used throughout the unavoidability check: to specify the   *)
(* arity discharging procedure and its rules, to enumerate all possible   *)
(* second neighborhoods, to check for the presence of a reducible         *)
(* configuration. If x fits p, we check whether a discharge rule applies  *)
(* to x by comparing p to the part r of the rule; we force the            *)
(* application of the rule by intersecting p with r (function meet_part   *)
(* below); we check whether a reducible map appears near x by applying    *)
(* its quiz to the part ranges in p (file redpart).                       *)
(*   This file contains the formal definition of "fit", and the basic     *)
(* operations on parts :                                                  *)
(*    - size_part, cat_part, take_part, drop_part, rot_part, catrev_part, *)
(*      rev_part : list operations.                                       *)
(*    - mirror_part : reflection along the first spoke (similar, but not  *)
(*      identical to rev_part).                                           *)
(*    - converse_part : reflection across the first spoke.                *)
(*    - split_part : restricting a specific range in the part.            *)
(* The converse_part operation is only used to compute converse discharge *)
(* rules, and is (safely) approximate : upon reflection, some ranges      *)
(* may fall outside the second neighborhood. This never happens with the  *)
(* parts given in discharge.v; in fact, we've somewhat tailored the       *)
(* function to that data; there are a few other cases where it over       *)
(* approximates because such cases don't arise with our data.             *)
(*   Some of the internal accessors/updators defined here are also used   *)
(* in redpart.v to implement zipped parts.                                *)

(* PrMN stands for the range M..N; N=9 actually means infinity, e.g, Pr59 *)
(* means any arity greater than or equal to 5, that is any arity in a     *)
(* pentagonal map.                                                        *)
Inductive prange : Set :=
   Pr55 : prange
 | Pr66 : prange
 | Pr77 : prange
 | Pr88 : prange
 | Pr99 : prange
 | Pr56 : prange
 | Pr67 : prange
 | Pr78 : prange
 | Pr89 : prange
 | Pr57 : prange
 | Pr68 : prange
 | Pr79 : prange
 | Pr58 : prange
 | Pr69 : prange
 | Pr59 : prange.

Inductive part : Set :=
  Pnil : part
| Pcons : (spk, hat : prange) part -> part
| Pcons6 : (hat, fan1 : prange) part -> part
| Pcons7 : (hat, fan1, fan2 : prange) part -> part
| Pcons8 : (hat, fan1, fan2, fan3 : prange) part -> part.

Lemma prangeDataP : (comparable prange).
Proof. Rewrite: /comparable. Decide Equality. Qed.
Lemma partDataP : (comparable part).
Proof. Rewrite: /comparable. Decide Equality; Apply prangeDataP. Qed.
Definition partData : dataSet := Eval Compute in (compareData partDataP).
Canonical Structure partData.

Inductive subpart_loc : Set :=
  Pspoke : subpart_loc
| Phat   : subpart_loc
| Pfan1  : subpart_loc
| Pfan2  : subpart_loc
| Pfan3  : subpart_loc.

Syntax constr level 0 :
  pp_prange55 [(Pretty $_ Pr55)] -> ["5"]
| pp_prange66 [(Pretty $_ Pr66)] -> ["6"]
| pp_prange77 [(Pretty $_ Pr77)] -> ["7"]
| pp_prange88 [(Pretty $_ Pr88)] -> ["8"]
| pp_prange99 [(Pretty $_ Pr99)] -> ["9+"]
| pp_prange59 [(Pretty $_ Pr59)] -> ["*"]
| pp_prange69 [(Pretty $_ Pr69)] -> ["6+"]
| pp_prange79 [(Pretty $_ Pr79)] -> ["7+"]
| pp_prange89 [(Pretty $_ Pr89)] -> ["8+"]
| pp_prange56 [(Pretty $_ Pr56)] -> ["-6"]
| pp_prange57 [(Pretty $_ Pr57)] -> ["-7"]
| pp_prange58 [(Pretty $_ Pr58)] -> ["-8"]
| pp_prange67 [(Pretty $_ Pr67)] -> ["6:7"]
| pp_prange68 [(Pretty $_ Pr68)] -> ["6:8"]
| pp_prange78 [(Pretty $_ Pr78)] -> ["7:8"]
| pp_subpi_s  [(Pretty $_ Pspoke)] -> ["s"]
| pp_subpi_h  [(Pretty $_ Phat  )] -> ["h"]
| pp_subpi_f1 [(Pretty $_ Pfan1 )] -> ["f1"]
| pp_subpi_f2 [(Pretty $_ Pfan2 )] -> ["f2"]
| pp_subpi_f3 [(Pretty $_ Pfan3 )] -> ["f3"].

Syntax constr level 10 :
  pp_part [(Pretty part $p)] ->
  ["Part" [<hov 0> (PPPART $p)]]
| pppart_default [<<(PPPART $p)>>] ->
  [[1 0] "& " $p:L]
| pppart_pnil [<<(PPPART <<Pnil>>)>>] ->
  []
| pppart_pcons_hat [<<(PPPART <<(Pcons $s $h $p)>>)>>] ->
  [[1 0] "[" <<(Pretty prange $h)>> "]" [1 0] <<(Pretty prange $s)>> (PPPART $p)]
| pppart_pcons_nohat [<<(PPPART <<(Pcons $s Pr59 $p)>>)>>] ->
  [[1 0] <<(Pretty prange $s)>> (PPPART $p)]
| pppart_pcons6 [<<(PPPART <<(Pcons6 $h $f1 $p)>>)>>] ->
  [[1 0] "[" <<(Pretty prange $h)>> " " <<(Pretty prange $f1)>> "]"
   [1 0] "6" (PPPART $p)]
| pppart_pcons7 [<<(PPPART <<(Pcons7 $h $f1 $f2 $p)>>)>>] ->
  [[1 0] "[" <<(Pretty prange $h)>> " " <<(Pretty prange $f1)>>
          " " <<(Pretty prange $f2)>> "]"
   [1 0] "7" (PPPART $p)]
| pppart_pcons8 [<<(PPPART <<(Pcons8 $h $f1 $f2 $f3 $p)>>)>>] ->
  [[1 0] "[" <<(Pretty prange $h)>> " " <<(Pretty prange $f1)>>
          " " <<(Pretty prange $f2)>> " " <<(Pretty prange $f3)>> "]"
   [1 0] "8" (PPPART $p)]
| pp_seq_part [(Pretty (seq part) $s)] ->
  ["Pseq" [<hv 1> (PPSEQPP SPC <<part>> $s)]].

Grammar constr constr10 : constr :=
  part_form ["Part" part_body($p)] -> [$p]
with part_body : constr :=
  part_form_nohat [prange($s) part_body($p)] ->
  [(Pcons $s Pr59 $p)]
| part_form_1hat [ "[" prange($h) "]" prange($s) part_body($p) ] ->
  [(Pcons $s $h $p)]
| part_form_2hat [ "[" prange($h) prange($f1) "]" "6" part_body($p) ] ->
  [(Pcons6 $h $f1 $p)]
| part_form_3hat [ "[" prange($h) prange($f1) prange($f2)"]" "7" part_body($p) ] ->
  [(Pcons7 $h $f1 $f2 $p)]
| part_form_4hat
    [ "[" prange($h)  prange($f1) prange($f2) prange($f3)"]" "8" part_body($p) ] ->
  [(Pcons8 $h $f1 $f2 $f3 $p)]
| part_form_tail [ "&" constr9($p) ] ->
  [$p]
| part_form_end [ ] ->
  [Pnil]
with prange : constr :=
  prange55 ["5"] ->  [Pr55]
| prange66 ["6"] ->  [Pr66]
| prange77 ["7"] ->  [Pr77]
| prange88 ["8"] ->  [Pr88]
| prange99 ["9" "+"] -> [Pr99]
| prange59 ["*"] ->  [Pr59]
| prange59p ["5" "+"] ->  [Pr59]
| prange69 ["6" "+"] -> [Pr69]
| prange79 ["7" "+"] -> [Pr79]
| prange89 ["8" "+"] -> [Pr89]
| prange56 ["-" "6"] -> [Pr56]
| prange57 ["-" "7"] -> [Pr57]
| prange58 ["-" "8"] -> [Pr58]
| prange67 ["6" ":" "7"] -> [Pr67]
| prange68 ["6" ":" "8"] -> [Pr68]
| prange78 ["7" ":" "8"] -> [Pr78]
| prange_var [constr0($r)] -> [$r]
with subpart_loc : constr :=
  subpart_spoke ["s"]  -> [Pspoke]
| subpart_hat   ["h"]  -> [Phat]
| subpart_fan1  ["f1"] -> [Pfan1]
| subpart_fan2  ["f2"] -> [Pfan2]
| subpart_fan3  ["f3"] -> [Pfan3].


(* This automatically turns on pretty-printing for parts that start with at *)
(* least three explicit constructors.                                       *)

Syntax constr level 10 :
  pp_part_start_check [(Pcons $s $h $p)] ->
  [(PPARTCK <<(2)>> $p <<(Pcons $s $h $p)>>)]
| pp_part_start_check6 [(Pcons6 $h $f1 $p)] ->
  [(PPARTCK <<(2)>> $p <<(Pcons6 $h $f1 $p)>>)]
| pp_part_start_check7 [(Pcons7 $h $f1 $f2 $p)] ->
  [(PPARTCK <<(2)>> $p <<(Pcons7 $h $f1 $f2 $p)>>)]
| pp_part_start_check8 [(Pcons8 $h $f1 $f2 $f3 $p)] ->
  [(PPARTCK <<(2)>> $p <<(Pcons7 $h $f1 $f2 $f3 $p)>>)]
| pp_part_check_pretty [<<(PPARTCK <<(0)>> $_ $p)>>] ->
  [<<(Pretty part $p)>>]
| pp_part_check_raw [<<(PPARTCK <<(S $_)>> $_ $p)>>] ->
  [[<hov 2> (PPARTRAW $p)]]
| pp_part_check [<<(PPARTCK <<(S $n)>> <<(Pcons $_ $_ $p)>> $p0)>>] ->
  [(PPARTCK $n $p $p0)]
| pp_part_check6 [<<(PPARTCK <<(S $n)>> <<(Pcons6 $_ $_ $p)>> $p0)>>] ->
  [(PPARTCK $n $p $p0)]
| pp_part_check7 [<<(PPARTCK <<(S $n)>> <<(Pcons7 $_ $_ $_ $p)>> $p0)>>] ->
  [(PPARTCK $n $p $p0)]
| pp_part_check8 [<<(PPARTCK <<(S $n)>> <<(Pcons8 $_ $_ $_ $p)>> $p0)>>] ->
  [(PPARTCK $n $p $p0)]
| pp_part_raw_default [<<(PPARTRAW $p)>>] ->
  [$p]
| pp_part_raw_pcons [<<(PPARTRAW <<(Pcons $s $h $p)>>)>>] ->
  ["Pcons" [1 0] $s:L [1 0] $h:L [1 0] (PPARTRAW $p):L]
| pp_part_raw_pcons6 [<<(PPARTRAW <<(Pcons6 $h $f1 $p)>>)>>] ->
  ["Pcons6" [1 0] $h:L [1 0] $f1:L [1 0] (PPARTRAW $p):L]
| pp_part_raw_pcons7 [<<(PPARTRAW <<(Pcons7 $h $f1 $f2 $p)>>)>>] ->
  ["Pcons7" [1 0] $h:L [1 0] $f1:L [1 0] $f2:L [1 0] (PPARTRAW $p):L]
| pp_part_raw_pcons8 [<<(PPARTRAW <<(Pcons8 $h $f1 $f2 $f3 $p)>>)>>] ->
  ["Pcons8" [1 0] $h:L [1 0] $f1:L [1 0] $f2:L [1 0] $f3:L [1 0] (PPARTRAW $p):L].
Syntax constr level 0 : pp_part_raw_pnil [<<(PPARTRAW <<Pnil>>)>>] -> ["Pnil"].


(* Shorthand for making (mostly) empty parts.                                 *)

Definition pcons_s [s : prange] : part -> part := (Pcons s Pr59).

Definition pcons_ [n : nat] : part := (iter n (Pcons Pr59 Pr59) Pnil).

(* Range semantics.                                                           *)

Definition mem_range [r : prange] : nat -> bool :=
  Cases r of
   Pr55 => (set1 (5))
 | Pr66 => (set1 (6))
 | Pr77 => (set1 (7))
 | Pr88 => (set1 (8))
 | Pr56 => (set2 (5) (6))
 | Pr67 => (set2 (6) (7))
 | Pr78 => (set2 (7) (8))
 | Pr57 => (set3 (5) (6) (7))
 | Pr68 => (set3 (6) (7) (8))
 | Pr58 => (set4 (5) (6) (7) (8))
 | Pr59 => (leq (5))
 | Pr69 => (leq (6))
 | Pr79 => (leq (7))
 | Pr89 => (leq (8))
 | Pr99 => (leq (9))
 end.

Coercion mem_range : prange >-> FUNCLASS.

(* Part/range comparison results; Pstraddle covers all the remaining cases,  *)
(* including when the left hand side stricly contains the right hand side.   *)
(* We use the result of a comparison by applying it to a "fit" predicate.    *)

Inductive part_rel : Set :=
  Pdisjoint : part_rel
| Pstraddle : part_rel
| Psubset   : part_rel.

Definition apply_part_rel [pr : part_rel; b : bool] : bool :=
  Cases pr of Pdisjoint => false | Psubset => true | _ => b end.

Coercion apply_part_rel : part_rel >-> FUNCLASS.

Definition notPsubset [c : part_rel] : part_rel :=
  if c is Psubset then Pstraddle else c.

Definition meet_prel [c, c' : part_rel] : part_rel :=
  Cases c of
    Pdisjoint => c
  | Psubset   => c'
  | Pstraddle  => (notPsubset c')
  end.

(* Range comparison and meet.                                                 *)

Definition cmp_range [r, r' : prange] : part_rel :=
  Cases r' r of
    Pr59    _ => Psubset
  |    _ Pr59 => Pstraddle

  | Pr69 Pr55 => Pdisjoint
  | Pr69 Pr56 => Pstraddle
  | Pr69 Pr57 => Pstraddle
  | Pr69 Pr58 => Pstraddle
  | Pr69    _ => Psubset
  | Pr55 Pr69 => Pdisjoint
  |    _ Pr69 => Pstraddle

  | Pr58 Pr99 => Pdisjoint
  | Pr58 Pr89 => Pstraddle
  | Pr58 Pr79 => Pstraddle
  | Pr58    _ => Psubset
  | Pr99 Pr58 => Pdisjoint
  |    _ Pr58 => Pstraddle

  | Pr55 Pr55 => Psubset
  | Pr55 Pr56 => Pstraddle
  | Pr55 Pr57 => Pstraddle
  | Pr55    _ => Pdisjoint
  | Pr56 Pr55 => Psubset
  | Pr57 Pr55 => Psubset
  |    _ Pr55 => Pdisjoint

  | Pr99 Pr99 => Psubset
  | Pr99 Pr89 => Pstraddle
  | Pr99 Pr79 => Pstraddle
  | Pr99    _ => Pdisjoint
  | Pr89 Pr99 => Psubset
  | Pr79 Pr99 => Psubset
  |    _ Pr99 => Pdisjoint
 
  | Pr66 Pr66 => Psubset
  | Pr66 Pr56 => Pstraddle
  | Pr66 Pr57 => Pstraddle
  | Pr66 Pr67 => Pstraddle
  | Pr66 Pr68 => Pstraddle
  | Pr66    _ => Pdisjoint
  | Pr56 Pr66 => Psubset
  | Pr57 Pr66 => Psubset
  | Pr67 Pr66 => Psubset
  | Pr68 Pr66 => Psubset
  |    _ Pr66 => Pdisjoint

  | Pr88 Pr88 => Psubset
  | Pr88 Pr89 => Pstraddle
  | Pr88 Pr79 => Pstraddle
  | Pr88 Pr78 => Pstraddle
  | Pr88 Pr68 => Pstraddle
  | Pr88    _ => Pdisjoint
  | Pr89 Pr88 => Psubset
  | Pr79 Pr88 => Psubset
  | Pr78 Pr88 => Psubset
  | Pr68 Pr88 => Psubset
  |    _ Pr88 => Pdisjoint

  | Pr77 Pr77 => Psubset
  | Pr77 Pr56 => Pdisjoint
  | Pr77 Pr89 => Pdisjoint
  | Pr77    _ => Pstraddle
  | Pr56 Pr77 => Pdisjoint
  | Pr89 Pr77 => Pdisjoint
  |    _ Pr77 => Psubset

  | Pr68 Pr68 => Psubset
  | Pr68 Pr67 => Psubset
  | Pr68 Pr78 => Psubset
  | Pr68    _ => Pstraddle
  |    _ Pr68 => Pstraddle

  | Pr67 Pr67 => Psubset
  | Pr67 Pr89 => Pdisjoint
  | Pr67    _ => Pstraddle
  | Pr57 Pr67 => Psubset
  | Pr89 Pr67 => Pdisjoint
  |    _ Pr67 => Pstraddle

  | Pr78 Pr78 => Psubset
  | Pr78 Pr56 => Pdisjoint
  | Pr78    _ => Pstraddle
  | Pr79 Pr78 => Psubset
  | Pr56 Pr78 => Pdisjoint
  |    _ Pr78 => Pstraddle

  | Pr89 Pr56 => Pdisjoint
  | Pr79 Pr56 => Pdisjoint
  |    _ Pr56 => Psubset
  | Pr56 Pr57 => Pstraddle
  | Pr56    _ => Pdisjoint

  | Pr57 Pr89 => Pdisjoint
  |    _ Pr89 => Psubset
  | Pr89 Pr79 => Pstraddle
  | Pr89    _ => Pdisjoint

  | Pr57 Pr57 => Psubset
  | Pr79 Pr79 => Psubset
  |    _    _ => Pstraddle
  end.

Definition meet_range [r, r' : prange] : prange :=
  Cases r' r of
    Pr56 Pr67 => Pr66
  | Pr56 Pr68 => Pr66
  | Pr56 Pr69 => Pr66
  | Pr67 Pr56 => Pr66
  | Pr68 Pr56 => Pr66
  | Pr69 Pr56 => Pr66
  
  | Pr57 Pr78 => Pr77
  | Pr57 Pr79 => Pr77
  | Pr67 Pr78 => Pr77
  | Pr67 Pr79 => Pr77
  | Pr78 Pr57 => Pr77
  | Pr79 Pr57 => Pr77
  | Pr78 Pr67 => Pr77
  | Pr79 Pr67 => Pr77

  | Pr89 Pr58 => Pr88
  | Pr89 Pr68 => Pr88
  | Pr89 Pr78 => Pr88
  | Pr58 Pr89 => Pr88
  | Pr68 Pr89 => Pr88
  | Pr78 Pr89 => Pr88

  | Pr57 Pr68 => Pr67
  | Pr57 Pr69 => Pr67
  | Pr68 Pr57 => Pr67
  | Pr69 Pr57 => Pr67

  | Pr79 Pr58 => Pr78
  | Pr79 Pr68 => Pr78
  | Pr58 Pr79 => Pr78
  | Pr68 Pr79 => Pr78

  | Pr58 Pr69 => Pr68
  | Pr69 Pr58 => Pr68

  | Pr59    _ => r
  | _    Pr59 => r'
  | Pr58    _ => r
  | Pr69    _ => r
  | _    Pr58 => r'
  | _    Pr69 => r'
  | Pr57    _ => r
  | Pr68    _ => r
  | Pr79    _ => r
  |    _ Pr57 => r'
  |    _ Pr68 => r'
  |    _ Pr79 => r'
  | Pr56    _ => r
  | Pr67    _ => r
  | Pr78    _ => r
  | Pr89    _ => r
  |    _ Pr56 => r'
  |    _ Pr67 => r'
  |    _ Pr78 => r'
  |    _    _ => r'
  end.

Lemma mem_cmp_range : (r : prange; n : nat) (r n) ->
  (r' : prange) (r' n) = (cmp_range r r' (r' n)).
Proof.
By Move=> r; Move=> [|[|[|[|[|[|[|[|[|n]]]]]]]]]; Case: r => // [_]; Case.
Qed.

Lemma mem_meet_range : (r, r' : prange; n : nat)
  (r n) -> (r' n) -> (meet_range r r' n).
Proof.
By Move=> r r' [|[|[|[|[|[|[|[|[|n]]]]]]]]]; Case: r => // [_]; Case r'.
Qed.

(* List-like operations on parts. Most also have a geometric meaning, exept   *)
(* "rev_part", which is just a subroutine for the implementation of zipped    *)
(* parts in redpart.v.                                                        *)

Fixpoint size_part [p : part] : nat :=
  Cases p of
    Pnil => (0)
  | (Pcons _ _ p') => (S (size_part p'))
  | (Pcons6 _ _ p') => (S (size_part p'))
  | (Pcons7 _ _ _ p') => (S (size_part p'))
  | (Pcons8 _ _ _ _ p') => (S (size_part p'))
  end.

Fixpoint drop_part [n : nat] : part -> part :=
  [p]Cases n p of
    (S n') (Pcons _ _ p') => (drop_part n' p')
  | (S n') (Pcons6 _ _ p') => (drop_part n' p')
  | (S n') (Pcons7 _ _ _ p') => (drop_part n' p')
  | (S n') (Pcons8 _ _ _ _ p') => (drop_part n' p')
  | _ _ => p
  end.

Fixpoint take_part [n : nat] : part -> part :=
  [p]Cases n p of
    (S n') (Pcons s h p')         => (Pcons s h (take_part n' p'))
  | (S n') (Pcons6 h f1 p')       => (Pcons6 h f1 (take_part n' p'))
  | (S n') (Pcons7 h f1 f2 p')    => (Pcons7 h f1 f2 (take_part n' p'))
  | (S n') (Pcons8 h f1 f2 f3 p') => (Pcons8 h f1 f2 f3 (take_part n' p'))
  | _ _ => Pnil
  end.

Fixpoint cat_part [p : part] : part -> part :=
  [q]Cases p of
    (Pcons s h p')         => (Pcons s h (cat_part p' q))
  | (Pcons6 h f1 p')       => (Pcons6 h f1 (cat_part p' q))
  | (Pcons7 h f1 f2 p')    => (Pcons7 h f1 f2 (cat_part p' q))
  | (Pcons8 h f1 f2 f3 p') => (Pcons8 h f1 f2 f3 (cat_part p' q))
  | Pnil => q
  end.

Definition rot_part [n : nat; p : part] : part :=
  (cat_part (drop_part n p) (take_part n p)).

Lemma size_cat_part : (p1, p2 : part)
  (size_part (cat_part p1 p2)) = (addn (size_part p1) (size_part p2)).
Proof. By Move=> p1 p2; Elim: p1 => //= *; Congr S. Qed.

Lemma size_drop_part : (n : nat; p : part)
   (size_part (drop_part n p)) = (subn (size_part p) n).
Proof. By Move=> n; Elim: n => [|n Hrec] p; Case p. Qed.

Lemma cat_take_drop_part : (n : nat; p : part)
  (cat_part (take_part n p) (drop_part n p)) = p.
Proof. By Elim=> [|n Hrec]; Case=> //= *; Rewrite Hrec. Qed.

Lemma size_rot_part : (n : nat; p : part)
   (size_part (rot_part n p)) = (size_part p).
Proof.
Move=> n p.
By Rewrite: -{2 p}(cat_take_drop_part n) /rot_part !size_cat_part addnC.
Qed.

Fixpoint catrev_part [p1 : part] : part -> part :=
  [p2]Cases p1 of
    Pnil =>
    p2
  | (Pcons s h p1') =>
      (catrev_part p1' (Pcons s h p2))
  | (Pcons6 h f1 p1') =>
      (catrev_part p1' (Pcons6 h f1 p2))
  | (Pcons7 h f1 f2 p1') =>
      (catrev_part p1' (Pcons7 h f1 f2 p2))
  | (Pcons8 h f1 f2 f3 p1') =>
      (catrev_part p1' (Pcons8 h f1 f2 f3 p2))
  end.

Definition rev_part [p : part] : part := (catrev_part p Pnil).

Lemma catrev_part_eq : (p1, p2 : part)
  (catrev_part p1 p2) = (cat_part (rev_part p1) p2).
Proof.
Move=> p1 p2; Rewrite: /rev_part -{1 p2}/(cat_part Pnil p2); Move: p1 {}Pnil p2.
Elim=> [|s h p1 Hrec|h f1 p1 Hrec|h f1 f2 p1 Hrec|h f1 f2 f3 p1 Hrec] p2 p3 //=;
  By Rewrite: -Hrec.
Qed.

Lemma size_rev_part : (p : part) (size_part (rev_part p)) = (size_part p).
Proof.
Move=> p; Rewrite: /rev_part -{(size_part p)}addn0 -{(0)}/(size_part Pnil).
Elim: p {}Pnil => //= [s h p Hrec|h f1 p Hrec|h f1 f2 p Hrec|h f1 f2 f3 p Hrec] p';
  By Rewrite: addSnnS Hrec.
Qed.

Lemma rev_rev_part : (p : part) (rev_part (rev_part p)) = p.
Proof.
Move=> p; Rewrite: {2}/rev_part -{2 p}/(catrev_part Pnil p); Move: p {}Pnil.
By Elim=> //=  [s h p Hrec|h f1 p Hrec|h f1 f2 p Hrec|h f1 f2 f3 p Hrec] p';
  Rewrite: Hrec.
Qed.

(* Accessors; except for "next_hat", they assume the part is not nil.         *)
(* The accessors are mostly used for zipped parts, where we also need to      *)
(* access the fans in clockwise order, so we have both "r" (counterclockwise) *)
(* and "l" (clockwise) versions of the fan accessors. We don't provide update *)
(* functions because both here (for split_part) and in redpart, update is     *)
(* bundeled with another operation.                                           *)

Definition get_spoke [p : part] : prange :=
  Cases p of
    (Pcons s _ _)      => s
  | (Pcons6 _ _ _)     => Pr66
  | (Pcons7 _ _ _ _)   => Pr77
  | (Pcons8 _ _ _ _ _) => Pr88
  | _                  => Pr59
  end.

Definition next_hat [h0 : prange; p : part] : prange :=
  Cases p of
    Pnil               => h0
  | (Pcons _ h _)      => h
  | (Pcons6 h _ _)     => h
  | (Pcons7 h _ _ _)   => h
  | (Pcons8 h _ _ _ _) => h
  end.

Definition get_hat : part -> prange := Eval Compute in (next_hat Pr59).

Definition get_fan1r [p : part] : prange :=
  Cases p of
    (Pcons6 _ f1 _)     => f1
  | (Pcons7 _ f1 _ _)   => f1
  | (Pcons8 _ f1 _ _ _) => f1
  | _                   => Pr59
  end.

Definition get_fan2r [p : part] : prange :=
  Cases p of
    (Pcons7 _ _ f2 _)   => f2
  | (Pcons8 _ _ f2 _ _) => f2
  | _ => Pr59
  end.

Definition get_fan3r [p : part] : prange :=
  Cases p of
  | (Pcons8 _ _ _ f3 _) => f3
  | _ => Pr59
  end.

Definition get_fan1l [p : part] : prange :=
  Cases p of
    (Pcons6 _ f1 _)     => f1
  | (Pcons7 _ _ f2 _)   => f2
  | (Pcons8 _ _ _ f3 _) => f3
  | _                   => Pr59
  end.

Definition get_fan2l [p : part] : prange :=
  Cases p of
    (Pcons7 _ f1 _ _)   => f1
  | (Pcons8 _ _ f2 _ _) => f2
  | _                   => Pr59
  end.

Definition get_fan3l [p : part] : prange :=
  Cases p of
  | (Pcons8 _ f1 _ _ _) => f1
  | _                   => Pr59
  end.

(* Mirror image : reflection ACROSS the first spoke (exchanges second  *)
(* and last spoke).                                                    *)

Fixpoint mirror_part_rec [h0 : prange; rp, p : part] : part :=
  Cases p of
    Pnil =>
       rp
  | (Pcons s _ p') =>
      (mirror_part_rec h0 (Pcons s (next_hat h0 p') rp) p')
  | (Pcons6 _ f1 p') =>
      (mirror_part_rec h0 (Pcons6 (next_hat h0 p') f1 rp) p')
  | (Pcons7 _ f1 f2 p') =>
      (mirror_part_rec h0 (Pcons7 (next_hat h0 p') f2 f1 rp) p')
  | (Pcons8 _ f1 f2 f3 p') =>
      (mirror_part_rec h0 (Pcons8 (next_hat h0 p') f3 f2 f1 rp) p')
  end.

Definition mirror_part [p : part] : part :=
  (mirror_part_rec (get_hat p) Pnil p).

Lemma size_mirror_part : (p : part) (size_part (mirror_part p)) = (size_part p).
Proof.
Move=> p; Unfold mirror_part.
Rewrite: -{(size_part p)}/(addn (size_part Pnil) (size_part p)).
Elim: p (Pnil) (get_hat p) =>
   [|s h p Hrec | h f1 p Hrec | h f1 f2 p Hrec | h f1 f2 f3 p Hrec] q h0;
 By Rewrite: /= ?addn0 ?addnS ?Hrec.
Qed.

Lemma mirror_mirror_part : (p : part) (mirror_part (mirror_part p)) = p.
Proof.
Move=> p; Rewrite: {2}/mirror_part; Def Dh0: h0 := (get_hat p).
Step Eh0: (next_hat if p is Pnil then Pr59 else h0 Pnil) = (next_hat h0 p).
  By Rewrite Dh0; Case p.
Transitivity (mirror_part_rec h0 p Pnil); RightDone.
By Elim: p {Dh0} (Pnil) Eh0 =>
   [|s h p Hrec | h f1 p Hrec | h f1 f2 p Hrec | h f1 f2 f3 p Hrec] q /= Eh0;
   Rewrite: /= ?Hrec // /mirror_part /= ?Eh0 // -Eh0.
Qed.

(* Converse part: reflection ALONG the first spoke (exchanges hub and first *)
(* spoke).                                                                  *)

Definition conv_part12 [p4 : part] : prange * (part -> part) :=
  Cases p4 of
    (Pcons s2 s1 (Pcons h23 Pr59 _)) =>
      (h23, [q3](pcons_s s1 (pcons_s s2 q3)))
  | (Pcons Pr55 s1 (Pcons h23 h12 _)) =>
      (h23, [q3](pcons_s s1 (Pcons Pr55 h12 q3)))
  | (Pcons Pr66 s1 (Pcons h23 f21 _)) =>
      (h23, [q3](pcons_s s1 (Pcons6 Pr59 f21 q3)))
  | (Pcons Pr77 s1 (Pcons h23 f22 _)) =>
      (h23, [q3](pcons_s s1 (Pcons7 Pr59 Pr59 f22 q3)))
  | (Pcons6 s1 h12 (Pcons h23 f21 _)) =>
      (h23, [q3](pcons_s s1 (Pcons6 h12 f21 q3)))
  | (Pcons7 s1 h12 f21 (Pcons h23 f22 _)) =>
      (h23, [q3](pcons_s s1 (Pcons7 h12 f21 f22 q3)))
  | _ =>
      (Pr59, [_]Pnil)
  end.

Definition conv_part3 [h23 : prange; p6 : part] : part -> part :=
  Cases p6 of
    Pnil     
                  => (Pcons Pr55 h23)
  | (Pcons _ _ Pnil)
                  => (Pcons Pr66 h23)
  | (Pcons f31 _ (Pcons f32 _ Pnil)) =>
      Cases f31 f32 of
        Pr59 Pr59 => (Pcons Pr77 h23)
      |    _    _ => (Pcons7 h23 f31 f32)
      end
  | (Pcons f31 _ (Pcons f32 _ (Pcons f33 _ Pnil)))
                  => (Pcons8 h23 f31 f32 f33)
  | _
                  => [_]Pnil
  end.

Definition conv_part4 [p1 : part] : prange * (part -> part) :=
  Cases p1 of
    (Pcons h34  _ (Pcons s4 Pr59 _))      => (Pr59, (Pcons s4 h34))
  | (Pcons h34  _ (Pcons Pr55 h45 _))     => (h45,  (Pcons Pr55 h34))
  | (Pcons h34  _ (Pcons Pr66 f41 _))     => (Pr59, (Pcons6 h34 f41))
  | (Pcons h34  _ (Pcons Pr77 f41 _))     => (Pr59, (Pcons7 h34 f41 Pr59))
  | (Pcons h34  _ (Pcons6 f41 h45 _))     => (h45,  (Pcons6 h34 f41))
  | (Pcons h34  _ (Pcons7 f41 f42 h45 _)) => (h45,  (Pcons7 h34 f41 f42))
  |      _                                => (Pr59, [_]Pnil)
   end.

Definition conv_part5 [h45 : prange; p3 : part] : prange * part :=
  Cases p3 of
    (Pcons u s5 _)      => (u, (Pcons s5 h45 Pnil))
  | (Pcons7 s5 s6 s7 _) => (Pr77, (Pcons s5 h45 (pcons_s s6 (pcons_s s7 Pnil))))
  |       _             => (Pr59, Pnil)
  end.

Definition converse_part [p1 : part] : prange * part :=
  let (h45, q4) = (conv_part4 p1) in
  let (u, q5) = (conv_part5 h45 (drop_part (2) p1)) in
  let (h23, q12) = (conv_part12 (drop_part (3) p1)) in
  let q3 = (conv_part3 h23 (drop_part (5) p1)) in
  (u, (q12 (q3 (q4 q5)))).

(* Part (and range) splitting with respect to a condition, that is a quadruple *)
(* part location i, spoke index j, arity value k, and a boolean lo, true if we *)
(* want to restrict the range at i[j] to arities lower than or equal to k, and *)
(* false if we want the arities greater than k. A split is "good" if it is     *)
(* nontrivial (k is in the range) and definite (if i is a fan location, the    *)
(* spoke below it has a definite arity that is large enough).                  *)

Definition prange_lo [k : nat] : prange :=
  Cases k of (5) => Pr55 | (6) => Pr56 | (7) => Pr57 | (8) => Pr58 | _ => Pr59 end.

Definition prange_hi [k : nat] : prange :=
  Cases k of (5) => Pr69 | (6) => Pr79 | (7) => Pr89 | (8) => Pr99 | _ => Pr59 end.

Definition good_rsplit [k : nat; r : prange]  : bool :=
   if (cmp_range r (prange_lo k)) is Pstraddle then true else false.

Definition split_range [k : nat; lo : bool; r : prange] : prange :=
  (meet_range (if lo then prange_lo else prange_hi k) r).

Lemma fit_split_range : (k : nat; r : prange) (good_rsplit k r) ->
  (lo : bool; a : nat) (split_range k lo r a) = (andb (addb lo (ltn k a)) (r a)).
Proof. Repeat Case=> //. Qed.

Definition good_split [i : subpart_loc; j, k : nat; p : part] : bool :=
  Cases i (drop_part j p) of
    Pspoke (Pcons s _ _)       => (good_rsplit k s)
  | Phat   (Pcons s h _)       => (good_rsplit k h)
  | Phat   (Pcons6 h _ _)      => (good_rsplit k h)
  | Phat   (Pcons7 h _ _ _)    => (good_rsplit k h)
  | Phat   (Pcons8 h _ _ _ _)  => (good_rsplit k h)
  | Pfan1  (Pcons6 _ f1 _)     => (good_rsplit k f1)
  | Pfan1  (Pcons Pr66 _ _)    => (good_rsplit k Pr59)
  | Pfan1  (Pcons7 _ f1 _ _)   => (good_rsplit k f1)
  | Pfan1  (Pcons Pr77 _ _)    => (good_rsplit k Pr59)
  | Pfan1  (Pcons8 _ f1 _ _ _) => (good_rsplit k f1)
  | Pfan1  (Pcons Pr88 _ _)    => (good_rsplit k Pr59)
  | Pfan2  (Pcons7 _ _ f2 _)   => (good_rsplit k f2)
  | Pfan2  (Pcons Pr77 _ _)    => (good_rsplit k Pr59)
  | Pfan2  (Pcons8 _ _ f2 _ _) => (good_rsplit k f2)
  | Pfan2  (Pcons Pr88 _ _)    => (good_rsplit k Pr59)
  | Pfan3  (Pcons8 _ _ _ f3 _) => (good_rsplit k f3)
  | Pfan3  (Pcons Pr88 _ _)    => (good_rsplit k Pr59)
  | _       _                   => false
  end.

Definition split_part [i : subpart_loc; j, k : nat; lo : bool; p : part] : part :=
  let p1 = (take_part j p) in let p2 = (drop_part j p) in
  let mkp = [df; r; p'](cat_part p1 (df (split_range k lo r) p')) in
  Cases i p2 of
    Pspoke (Pcons s h p')         => (mkp [r](Pcons r h) s p')
  | Phat   (Pcons s h p')         => (mkp [r](Pcons s r) h p')
  | Phat   (Pcons6 h f1 p')       => (mkp [r](Pcons6 r f1) h p')
  | Phat   (Pcons7 h f1 f2 p')    => (mkp [r](Pcons7 r f1 f2) h p')
  | Phat   (Pcons8 h f1 f2 f3 p') => (mkp [r](Pcons8 r f1 f2 f3) h p')
  | Pfan1  (Pcons6 h f1 p')       => (mkp [r](Pcons6 h r) f1 p')
  | Pfan1  (Pcons Pr66 h p')      => (mkp [r](Pcons6 h r) Pr59 p')
  | Pfan1  (Pcons7 h f1 f2 p')    => (mkp [r](Pcons7 h r f2) f1 p')
  | Pfan1  (Pcons Pr77 h p')      => (mkp [r](Pcons7 h r Pr59) Pr59 p')
  | Pfan1  (Pcons8 h f1 f2 f3 p') => (mkp [r](Pcons8 h r f2 f3) f1 p')
  | Pfan1  (Pcons Pr88 h p')      => (mkp [r](Pcons8 h r Pr59 Pr59) Pr59 p')
  | Pfan2  (Pcons7 h f1 f2 p')    => (mkp [r](Pcons7 h f1 r) f2 p')
  | Pfan2  (Pcons Pr77 h p')      => (mkp [r](Pcons7 h Pr59 r) Pr59 p')
  | Pfan2  (Pcons8 h f1 f2 f3 p') => (mkp [r](Pcons8 h f1 r f3) f2 p')
  | Pfan2  (Pcons Pr88 h p')      => (mkp [r](Pcons8 h Pr59 r Pr59) Pr59 p')
  | Pfan3  (Pcons8 h f1 f2 f3 p') => (mkp [r](Pcons8 h f1 f2 r) f3 p')
  | Pfan3  (Pcons Pr88 h p')      => (mkp [r](Pcons8 h Pr59 Pr59 r) Pr59 p')
  | _       _                      => p
  end.

Lemma size_split_part : (i : subpart_loc; j, k : nat; lo : bool; p : part)
  (size_part (split_part i j k lo p)) = (size_part p).
Proof.
Move=> i j k lo p.
Move: (size_rot_part j p); Rewrite: /rot_part size_cat_part addnC.
By Case: i => //=; Case: (drop_part j p) => [|s h|h f1|h f1 f2|h f1 f2 f3] //= p';
  Try Case: s => //=; Rewrite: size_cat_part.
Qed.

(* Part comparison and intersection; note that the intersection is slightly *)
(* asymmetric, in that it will truncate the second argument.                *)

Fixpoint cmp_part [p, q : part] : part_rel :=
  Cases q p of
     (Pcons sq hq q') (Pcons sp hp p') =>
       (meet_prel (cmp_range sp sq)
       (meet_prel (cmp_range hp hq)
                  (cmp_part p' q')))
  | (Pcons sq hq q') (Pcons6 hp _ p') =>
      (meet_prel (cmp_range Pr66 sq)
      (meet_prel (cmp_range hp hq)
                 (cmp_part p' q')))
  | (Pcons sq hq q') (Pcons7 hp _ _ p') =>
      (meet_prel (cmp_range Pr77 sq)
      (meet_prel (cmp_range hp hq)
                 (cmp_part p' q')))
  | (Pcons sq hq q') (Pcons8 hp _ _ _ p') =>
      (meet_prel (cmp_range Pr88 sq)
      (meet_prel (cmp_range hp hq)
                 (cmp_part p' q')))
  | (Pcons6 hq _ q') (Pcons sp hp p') =>
      (meet_prel (notPsubset (cmp_range sp Pr66))
      (meet_prel (cmp_range hp hq)
                 (cmp_part p' q')))
  | (Pcons7 hq _ _ q') (Pcons sp hp p') =>
      (meet_prel (notPsubset (cmp_range sp Pr77))
      (meet_prel (cmp_range hp hq)
                 (cmp_part p' q')))
  | (Pcons8 hq _ _ _ q') (Pcons sp hp p') =>
      (meet_prel (notPsubset (cmp_range sp Pr88))
      (meet_prel (cmp_range hp hq)
                 (cmp_part p' q')))
  | (Pcons6 hq f1q q') (Pcons6 hp f1p p') =>
      (meet_prel (cmp_range hp hq)
      (meet_prel (cmp_range f1p f1q)
                (cmp_part p' q')))
  | (Pcons7 hq f1q f2q q') (Pcons7 hp f1p f2p p') =>
      (meet_prel (cmp_range hp hq)
      (meet_prel (cmp_range f1p f1q)
      (meet_prel (cmp_range f2p f2q)
                 (cmp_part p' q'))))
  | (Pcons8 hq f1q f2q f3q q') (Pcons8 hp f1p f2p f3p p') =>
      (meet_prel (cmp_range hp hq)
      (meet_prel (cmp_range f1p f1q)
      (meet_prel (cmp_range f2p f2q)
      (meet_prel (cmp_range f3p f3q)
                 (cmp_part p' q')))))
  | Pnil _ => Psubset
  | _ Pnil => Pstraddle
  | _ _ => Pdisjoint
  end.

Fixpoint meet_part [p, q : part] : part :=
  Cases q p of
    (Pcons sq hq q') (Pcons sp hp p') =>
      (Pcons (meet_range sp sq) (meet_range hp hq)
         (meet_part p' q'))
  | (Pcons sq hq q') (Pcons6 hp f1 p') =>
      (Pcons6 (meet_range hp hq) f1
         (meet_part p' q'))
  | (Pcons sq hq q') (Pcons7 hp f1 f2 p') =>
      (Pcons7 (meet_range hp hq) f1 f2
         (meet_part p' q'))
  | (Pcons sq hq q') (Pcons8 hp f1 f2 f3 p') =>
      (Pcons8 (meet_range hp hq) f1 f2 f3
         (meet_part p' q'))
  | (Pcons6 hq f1 q') (Pcons sp hp p') =>
      (Pcons6 (meet_range hp hq) f1
         (meet_part p' q'))
  | (Pcons7 hq f1 f2 q') (Pcons sp hp p') =>
      (Pcons7 (meet_range hp hq) f1 f2
         (meet_part p' q'))
  | (Pcons8 hq f1 f2 f3 q') (Pcons sp hp p') =>
      (Pcons8 (meet_range hp hq) f1 f2 f3
         (meet_part p' q'))
  | (Pcons6 hq f1q q') (Pcons6 hp f1p p') =>
      (Pcons6 (meet_range hp hq)
          (meet_range f1p f1q)
          (meet_part p' q'))
  | (Pcons7 hq f1q f2q q') (Pcons7 hp f1p f2p p') =>
      (Pcons7 (meet_range hp hq)
          (meet_range f1p f1q)
          (meet_range f2p f2q)
          (meet_part p' q'))
  | (Pcons8 hq f1q f2q f3q q') (Pcons8 hp f1p f2p f3p p') =>
      (Pcons8 (meet_range hp hq)
          (meet_range f1p f1q)
          (meet_range f2p f2q)
          (meet_range f3p f3q)
          (meet_part p' q'))
  | _ _ => p
  end.

Lemma size_meet_part : (p, q : part)
  (size_part (meet_part p q)) = (size_part p).
Proof.
Move=> p q; Def Dn: n := (size_part q).
By Elim: n p q {Dn}(introT eqP Dn) => [|n Hrec] p;
  Case=> //; Case: p => //= *; Rewrite: Hrec.
Qed.

(* Part semantics : matching maps. *)

Definition subpart_loc_move [i : subpart_loc; g : hypermap; x : g] : g :=
  Cases i of
    Pspoke => (edge x)
  | Phat   => (edge (iter (2) face (edge x)))
  | Pfan1  => (edge (iter (3) face (edge x)))
  | Pfan2  => (edge (iter (4) face (edge x)))
  | Pfan3  => (edge (iter (5) face (edge x)))
  end.

Coercion subpart_loc_move : subpart_loc >-> FUNCLASS.

Section FitPart.

Variable g : hypermap.

Fixpoint fitp [x : g; p : part] : bool :=
  let ax = (arity (edge x)) in
  let axn = [n](arity (edge (iter n face (edge x)))) in
  Cases p of
    (Pcons s h p') =>
    (and3b (s (arity (Pspoke g x)))
           (h (arity (Phat g x)))
           (fitp (face x) p'))
  | (Pcons6 h f1 p') =>
    (and4b (Pr66 (arity (Pspoke g x)))
           (h  (arity (Phat g x)))
           (f1 (arity (Pfan1 g x)))
           (fitp (face x) p'))
  | (Pcons7 h f1 f2 p') =>
    (and5b (Pr77 (arity (Pspoke g x)))
           (h  (arity (Phat g x)))
           (f1 (arity (Pfan1 g x)))
           (f2 (arity (Pfan2 g x)))
           (fitp (face x) p'))
  | (Pcons8 h f1 f2 f3 p') =>
    (and5b (Pr88 (arity (Pspoke g x)))
           (h  (arity (Phat g x)))
           (f1 (arity (Pfan1 g x)))
           (f2 (arity (Pfan2 g x)))
     (andb (f3 (arity (Pfan3 g x)))
           (fitp (face x) p')))
  | Pnil => true
  end.

Definition exact_fitp [x : g; p : part] : bool :=
  (andb (arity x) =d (size_part p) (fitp x p)).

(* An intermediate notion, for part converse : simple fit, plus an *)
(* explicit range check for the hub arity.                         *)
Definition tight_fitp [x : g; up : prange * part] : bool :=
  let (u, p) = up in (andb (u (arity x)) (fitp x p)).

(* Simple properties of fitp (that do not require geometrical properties),  *)
(* that is, list functions, comparison, meet, and split.                    *)

Lemma fitp_drop : (n : nat; p : part; x : g)
  (fitp x p) -> (fitp (iter n face x) (drop_part n p)).
Proof.
Move=> n; Elim: n => [|n Hrec] p x //; Rewrite: -iter_f.
By Case: p => [|s h p| h f1 p|h f1 f2 p| h f1 f2 f3 p] //=;
   Rewrite: ?andbA; Case/andP; Auto.
Qed.

Lemma fitp_cat : (x : g; p1, p2 : part)
  (fitp x (cat_part p1 p2)) =
   (andb (fitp x p1) (fitp (iter (size_part p1) face x) p2)).
Proof.
Move=> x p1 p2.
Elim: p1 x => [|s h p1 Hrec|h f1 p1 Hrec|h f1 f2 p1 Hrec|h f1 f2 f3 p1 Hrec] x //=;
  Rewrite: -?andbA f_iter -iter_f -Hrec //.
Qed.

Lemma fitp_rot : (n : nat; p : part) (leq n (size_part p)) ->
  (x : g) (exact_fitp x p) = (exact_fitp (iter n face x) (rot_part n p)).
Proof.
Move=> n p Hn x; Rewrite: /exact_fitp size_rot_part arity_iter_face.
Case: ((arity x) =P (size_part p)) => //= [Hx].
Rewrite: /rot_part -{1 p}(cat_take_drop_part n) !fitp_cat andbC.
Congr andb; Congr fitp.
  Congr [m](iter m face x); Move: (congr size_part (cat_take_drop_part n p)).
  Rewrite: -(leq_add_sub Hn) size_cat_part size_drop_part; Apply: (!addn_injr).
Rewrite: -iter_plus addnI size_drop_part addnC (leq_add_sub Hn) -Hx.
By Rewrite iter_face_arity.
Qed.

Lemma fitp_catrev : (x : g; p1, p2 : part)
  (fitp x (catrev_part p1 p2)) =
    (andb (fitp x (rev_part p1)) (fitp (iter (size_part p1) face x) p2)).
Proof. By Move=> *; Rewrite: catrev_part_eq fitp_cat size_rev_part. Qed.

(* Comparison and meet.                                                      *)

Remark Epr : (m, n : nat)
  (m =d n) = (Cases m of (6) => (Pr66 n)| (7) => (Pr77 n) | (8) => (Pr88 n)
                       | _ => m =d n end).
Proof. By Do 9 Case=> //. Qed.

Lemma fitp_cmp : (p : part; x : g) (fitp x p) ->
  (q : part) (fitp x q) = (cmp_part p q (fitp x q)).
Proof.
By Elim=> [|sp hp p Hrec|hp f1p p Hrec|hp f1p f2p p Hrec|hp f1p f2p f3p p Hrec] x;
  First [Move=> H; Simpl in H; Case/and3P: H => [Hs Hh Hp] | By Clear; Case];
  Try Case/andP: Hp => [Hf1 Hp];
  Try Case/andP: Hp => [Hf2 Hp];
  Try Case/andP: Hp => [Hf3 Hp];
  Case=> [ | sq hq q | hq f1q q | hq f1q f2q q | hq f1q f2q f3q q];
  Rewrite: //= 1?Epr 1?(mem_cmp_range Hs) -1?(eqP Hs) //;
  Rewrite: (mem_cmp_range Hh) (Hrec ? Hp);
  Rewrite: 1?(mem_cmp_range Hf1) 1?(mem_cmp_range Hf2) 1?(mem_cmp_range Hf3);
  Try (First [Case (cmp_range sp sq) | Case sp | Case sq]; Rewrite: //=);
  Case: (cmp_range hp hq); Rewrite: /= ?andbF //;
  Try (Case: (cmp_range f1p f1q); Rewrite: /= ?andbF //);
  Try (Case: (cmp_range f2p f2q); Rewrite: /= ?andbF //);
  Try (Case: (cmp_range f3p f3q); Rewrite: /= ?andbF //);
  Case (cmp_part p q); Rewrite: /= ?andbF.
Qed.

Lemma fitp_meet : (p, q : part; x : g)
  (fitp x p) -> (fitp x q) -> (fitp x (meet_part p q)).
Proof.
By Elim=> [|sp hp p Hrec|hp f1p p Hrec|hp f1p f2p p Hrec|hp f1p f2p f3p p Hrec];
  First [Move=> q x H; Simpl in H; Case/and3P: H => [Hsp Hhp Hp] | By Case];
  Try Case/andP: Hp => [Hf1p Hp];
  Try Case/andP: Hp => [Hf2p Hp];
  Try Case/andP: Hp => [Hf3p Hp];
  Case: q => [ | sq hq q | hq f1q q | hq f1q f2q q | hq f1q f2q f3q q];
  Rewrite: /= -?(eqP Hsp) ?Hsp ?Hhp ?Hf1p ?Hf2p ?Hf3p //;
  Case/and3P=> [Hsq Hhq Hq];
  Try Case/andP: Hq => [Hf1q Hq];
  Try Case/andP: Hq => [Hf2q Hq];
  Try Case/andP: Hq => [Hf3q Hq];
  Rewrite: (Hrec ? ? Hp Hq) ?Hsq ?Hf1q ?Hf2q ?Hf3q !mem_meet_range.
Qed.

Lemma exact_fitp_meet : (p, q : part; x : g)
  (exact_fitp x p) -> (fitp x q) -> (exact_fitp x (meet_part p q)).
Proof.
Move=> p q x; Rewrite: /exact_fitp size_meet_part.
By Case ((arity x) =d (size_part p)); LeftBy Apply: (!fitp_meet).
Qed.

End FitPart.

(* Part location sematics: a constructor function is valid wrt a location if *)
(* it only affects the validity of the range at that location.               *)
(* This definition appears here because we need to quantify over the map.    *)

Definition part_update [fp : prange -> part -> part; i : subpart_loc] : Prop :=
  (r : prange; p : part) 
    (and (size_part (fp r p)) = (S (size_part p))
         (g : hypermap; x : g; Hx : (fitp x (fp r p))) 
           (and (r (arity (i g x)))
                (r' : prange; Hr' : (r' (arity (i g x)))) (fitp x (fp r' p)))).

Lemma updatePs : (h : prange) (part_update [r](Pcons r h) Pspoke).
Proof.
Move=> h r p; Split; Move=> //= g x; Move/andP=> [Hr Hp].
By Split; RightBy Move=> r' Hr'; Rewrite Hr'.
Qed.

Lemma updatePh : (s : prange) (part_update [r](Pcons s r) Phat).
Proof.
Move=> s r p; Split; Move=> //= g x; Move/and3P=> [Hs Hr Hp].
By Split; RightBy Move=> r' Hr'; Rewrite: Hs Hr'.
Qed.

Lemma updateP6h : (f1 : prange) (part_update [r](Pcons6 r f1) Phat).
Proof.
Move=> f1 r p; Split; Move=> //= g x; Move/and3P=> [Hs Hr Hp].
By Split; RightBy Move=> r' Hr'; Rewrite: Hs Hr'.
Qed.

Lemma updateP6f1 : (h : prange) (part_update [r](Pcons6 h r) Pfan1).
Proof.
Move=> h r p; Split; Move=> //= g x; Move/and4P=> [Hs Hh Hr Hp].
By Split; RightBy Move=> r' Hr'; Rewrite: Hs Hh Hr'.
Qed.

Lemma updateP7h : (f1, f2 : prange) (part_update [r](Pcons7 r f1 f2) Phat).
Proof.
Move=> f1 f2 r p; Split; Move=> //= g x; Move/and3P=> [Hs Hr Hp].
By Split; RightBy Move=> r' Hr'; Rewrite: Hs Hr'.
Qed.

Lemma updateP7f1 : (h, f2 : prange) (part_update [r](Pcons7 h r f2) Pfan1).
Proof.
Move=> h f2 r p; Split; Move=> //= g x; Move/and4P=> [Hs Hh Hr Hp].
By Split; RightBy Move=> r' Hr'; Rewrite: Hs Hh Hr'.
Qed.

Lemma updateP7f2 : (h, f1 : prange) (part_update [r](Pcons7 h f1 r) Pfan2).
Proof.
Move=> h f1 r p; Split; Move=> //= g x; Move/and5P=> [Hs Hh Hf1 Hr Hp].
By Split; RightBy Move=> r' Hr'; Rewrite: Hs Hh Hf1 Hr'.
Qed.

Lemma updateP8h : (f1, f2, f3 : prange) (part_update [r](Pcons8 r f1 f2 f3) Phat).
Proof.
Move=> f1 f2 f3 r p; Split; Move=> //= g x; Move/and3P=> [Hs Hr Hp].
By Split; RightBy Move=> r' Hr'; Rewrite: Hs Hr'.
Qed.

Lemma updateP8f1 : (h, f2, f3 : prange) (part_update [r](Pcons8 h r f2 f3) Pfan1).
Proof.
Move=> h f2 f3 r p; Split; Move=> //= g x; Move/and4P=> [Hs Hh Hr Hp].
By Split; RightBy Move=> r' Hr'; Rewrite: Hs Hh Hr'.
Qed.

Lemma updateP8f2 : (h, f1, f3 : prange) (part_update [r](Pcons8 h f1 r f3) Pfan2).
Proof.
Move=> h f1 f3 r p; Split; Move=> //= g x; Move/and5P=> [Hs Hh Hf1 Hr Hp].
By Split; RightBy Move=> r' Hr'; Rewrite: Hs Hh Hf1 Hr'.
Qed.

Lemma updateP8f3 : (h, f1, f2 : prange) (part_update [r](Pcons8 h f1 f2 r) Pfan3).
Proof.
Split; Move=> //= g x; Case/and5P=> [Hs Hh Hf1 Hf2]; Move/andP=> [Hr Hp].
By Split; RightBy Move=> r' Hr'; Rewrite: Hs Hh Hf1 Hf2 Hr'.
Qed.

Section FitMirrorPart.

(* Properties of fitp that do depend on geometrical assumptions. They are *)
(* all grouped here, although fitp_pcons_ and fitp_split depend only on   *)
(* the pentagonal property, while fitp_mirror doesn't depend on it.       *)

Variable g : hypermap.
Hypothesis Hg: (plain_cubic g).
Local De2 := (plain_eq Hg).
Local Dn3 := (cubic_eq Hg).

Tactic Definition PopAnd Hn :=
  Match Context With [|- (andb ?1 ?) = ?] ->
    Case Hn: ?1; Rewrite: /= ?andbF // ?andbT.

Lemma fitp_mirror : (p : part; x : g)
  (exact_fitp x (mirror_part p)) = (!exact_fitp (mirror g) x p).
Proof.
Def Dars: ars := [n; g'; x] (arity (edge (iter n face (!edge g' x)))).
Def: Darsg := [n; x] (erefl (ars n g x)).
Move: {Darsg} (Darsg (2)) (Darsg (3)) (Darsg (4)) (Darsg (5)).
Rewrite: {2 4 6 8 ars}Dars /=; Move=> Dars2 Dars3 Dars4 Dars5.
Step Ears2: (x : g) (ars (2) (mirror g) x) = (ars (2) g x).
  Move=> x; Rewrite:  {1 ars}Dars arity_mirror /= /comp arity_face.
  Rewrite: -{(node x)}Enode -{1 x}Eedge Dn3 !(finv_f (Iface g)).
  Rewrite: -{1 (face (edge x))}Eface De2.
  By Rewrite: -{1 (face (face (edge x)))}Eedge Dn3 arity_face -Dars2.
Step Earsf: (n, m : nat; x : g) m =d (arity (edge x)) -> (leq n m) ->
              (ars n (mirror g) (face x)) = (ars (subn m n) g x).
  Move=> n m x Dm Hnm; Rewrite: {1 ars}Dars /= -{1 x}De2 /comp Eedge.
  Rewrite: -arity_face in Dm; Rewrite: (iter_finv (Iface g)) -(eqP Dm) //.
  Rewrite: iter_f /= -{(iter (subn m n) face (edge x))}De2 Eedge.
  By Rewrite: (order_finv (Iface g)) arity_face Dars.
Step Ears: (x : g) (arity (!edge (mirror g) (!face g x))) = (arity (edge x)).
  By Move=> x; Rewrite: arity_mirror /= /comp -{1 x}De2 Eedge arity_face.
Move: {Earsf}Ears Ears2 (Earsf (3)) (Earsf (4)) (Earsf (5)).
Rewrite: {1 3 5 7 ars}Dars /=; Move=> Ears Ears2 Ears3 Ears4 Ears5.
Step Hgars: (g' : hypermap; x : g'; p : part; h0 : prange)
  (fitp x p) -> (p = Pnil \/ (next_hat h0 p (ars (2) ? x))).
  Move=> g' x p h0; Rewrite Dars.
  Case Dp: p; First [By Left | By Case/and3P; Right].
Move=> p x; Rewrite: /exact_fitp size_mirror_part arity_mirror /mirror_part.
Pose h0 := (get_hat p); Pose h0hx := (h0 (ars (2) ? x)); Symmetry.
Case: ((arity x) =P (size_part p)) => // [Hax].
Pose sz0 := [q](size_part q) =d (0); Pose q := Pnil.
Transitivity (andb (andb (fitp x q) (!fitp (mirror g) x p)) (orb (sz0 p) h0hx)).
  Case Hxp: (!fitp (mirror g) x p); Rewrite: ~{Hax}//= ~/h0hx ~/h0.
  Case: (Hgars (mirror g) x p Pr59 Hxp) => [Dp | Hh0x]; LeftBy Rewrite Dp.
  By Rewrite: Dars /= Ears2 /= in Hh0x; Apply esym; Apply/orP; Right.
Step Eqp: (next_hat h0 q) = (next_hat h0 p) By Rewrite: /h0; Case p.
Step Hq0: (implb (sz0 q) (next_hat h0 q (ars (2) ? x)) =d h0hx) By Apply: set11.
ClearBody h0; Move: q Eqp Hq0; Rewrite: -{1 2 3 x}iter_face_arity ~Hax.
Elim: p => [|s h p Hrec|h f1 p Hrec|h f2 f1 p Hrec|h f3 f2 f1 p Hrec] q;
( Rewrite: /= ?andbT //; Pose y := (iter (size_part p) face x);
  Case=> [] Hq0; Rewrite: Ears Ears2; Apply: (etrans ? (Hrec ? ? ?));
  Rewrite: // -/y /= -Dars2 -?Dars3 -?Dars4 -?Dars5 -?andbA; PopAnd Hyq; PopAnd Hs;
  Rewrite: ?(Ears3 ? ? Hs) ?(Ears4 ? ? Hs) ?(Ears5 ? ? Hs) //;
  Rewrite: /subn /= (finv_f (Iface g)) andbC;
  Rewrite: -(andbC h0hx) -?andbA {(andb h0hx)}lock; Repeat BoolCongr;
  Rewrite: andbC -lock andbA andbC; PopAnd Hyp; (Transitivity h0hx;
  [(Case: (Hgars ? ? ? h0 Hyq) => [Dq | Hh0q]; RightBy Rewrite: Hh0q andbT);
    By Rewrite: {1 q}Dq /= in Hq0; Rewrite: (eqP Hq0) andbb
  |(Case: (Hgars ? ? ? h0 Hyp) => [Dp | Hh0p]; LeftBy Rewrite: /y Dp /= andbT);
    Rewrite: Dars /= Ears2 in Hh0p; Rewrite: Hh0p /=;
    By Move: Hh0p; Rewrite: /y; Case p])).
Qed.

Lemma fitp_sym : (p : part) (cmp_part p (mirror_part p)) = Psubset ->
  (x : g) (!exact_fitp (mirror g) x p) = (exact_fitp x p).
Proof.
Move=> p Hp x; Apply/idP/idP; Move/andP=> [Exp Hxp].
  Rewrite: -{1 p}mirror_mirror_part fitp_mirror /exact_fitp size_mirror_part.
  By Rewrite: Exp (fitp_cmp Hxp) Hp.
By Rewrite: -fitp_mirror /exact_fitp size_mirror_part Exp (fitp_cmp Hxp) Hp.
Qed.

End FitMirrorPart.

Section FitConversePart.

Variable g : hypermap.
Hypothesis Hg: (plain_cubic_pentagonal g).
Local HgF : (pentagonal g) := Hg.
Local De2 := (plain_eq Hg).
Local Dn3 := (cubic_eq Hg).

Definition inv_face2 [x : g] : g := (edge (node (edge (node x)))).

Lemma fitp_converse : (p : part; x : g) (exact_fitp x p) ->
  (tight_fitp (inv_face2 (edge (face (face x)))) (converse_part p)).
Proof.
Pose t59 := [h]Cases h of Pr59 => true | _ => false end.
Step Et59: (h : prange; A : Set; r1, r2 : A)
   (Cases h of Pr59 => r1 | _ => r2 end) = (if (t59 h) then r1 else r2).
  By Move=> h; Case h.
Step eEnf : (y : g) (edge y) = (node (face y)).
  By Move=> y; Rewrite: -{2 y}De2 Eedge.
Step fEnne : (y : g) (face y) = (node (node (edge y))).
  By Move=> y; Rewrite: eEnf Dn3.
Move=> p1 x H; Case: {H}(andP H) => [Exp1 Hxp1]; Rewrite: /converse_part.
Pose effx := (edge (face (face x))).
Step Hrq4: let (h45, q4) = (conv_part4 p1) in
  (h45 (arity (edge (face (face (edge (face (face effx))))))))
  /\ (q5 : part) (fitp (face (face effx)) q5) -> (fitp (face effx) (q4 q5)).
  Case: p1 Hxp1 {Exp1}; Try By Simpl; Split.
  Move=> h34 h p2 H; Simpl in H; Case/and3P: H => [Hh34 _ Hfxp2].
  Rewrite: fEnne -arity_face Enode fEnne De2 -eEnf fEnne /effx De2 -eEnf.
  Rewrite: -{1 (edge (face x))}[y](iter_face_subn (ltnW (ltnW (HgF y)))).
  Pose n := (arity (edge (face x))).
  Rewrite: -iter_plus addnI addnC /addn iter_plus.
  Rewrite: {1 Pcons}lock /= !Eface -eEnf -lock.
  Step En: (arity (edge (node (edge (face x))))) = n.
    By Rewrite: -arity_face Enode.
  Rewrite: -{(edge x)}Enode arity_face -{(node (edge x))}Enode -fEnne in Hh34.
  Case: p2 Hfxp2 => [|s4 f41 p|f41 h45 p|f41 f42 h45 p|h' f1 f2 f3 p]; 
    Rewrite: /= ?Et59 -/n; Try By Split.
      Move/and3P=> [Hs4 Hf41 _].
      Case (t59 f41).
        By Rewrite: Et59 if_same /=; Split; RightBy Rewrite: /= En Hs4 Enode Hh34.
      Case: s4 Hs4 => /= [] Ds4;
        By Try Rewrite: En -(eqP Ds4) set11 ?Enode Hh34 ?Hf41 /= ?HgF /=; Split.
    Move/and4P=> [Dn Hf41 Hh45 _].
    By Rewrite: En -(eqP Dn) !Enode set11 Hh34 Hf41; Split.
  Move/and5P=> [Dn Hf41 Hf42 Hh45 _].
  By Rewrite: En -(eqP Dn) !Enode set11 Hh34 Hf41 Hf42; Split.
Move: (conv_part4 p1) Hrq4 => [h45 q4] [Hh45 Hq4].
Move: (drop_part (2) p1) (fitp_drop (2) Hxp1) => p3 Hxp3; Simpl in Hxp3.
Step Huq5: let (u, q5) = (conv_part5 h45 p3) in
  (u (arity effx)) /\ (fitp (face (face effx)) q5).
  Case: p3 Hxp3 => [|u s5 p|h f p|s5 s6 s7 p|h f1 f2 f3 p] /=; Try By Split.
    By Rewrite: -/effx Hh45 /= andbT; Move/and3P=> [Hu Hs5 _]; Split.
  Rewrite: -/effx Hh45 !HgF /= andbT; Move/andP=> [Hu Hs57].
  By Rewrite: !andbA andbC -!andbA in Hs57; Case (andP Hs57); Split.
Move: {p3 h45 Hxp3 Hh45}(conv_part5 h45 p3) Huq5 => [u q5] [Hu Hq5].
Move: {q4 q5 Hq4 Hq5}(q4 q5) (Hq4 ? Hq5) => q Hq.
Move: (drop_part (3) p1) (fitp_drop (3) Hxp1) => p4 Hxp4; Simpl in Hxp4.
Step Hh23q12: let (h23, q12) = (conv_part12 p4) in
      (h23 (arity (edge (face (face (edge effx))))))
    /\ (q3 : part) (fitp effx q3) -> (fitp (inv_face2 effx) (q12 q3)).
  Pose ef3x := (edge (face (face (face x)))); Pose n := (arity ef3x).
  Step Es1: (arity (edge (inv_face2 effx))) = (arity (edge (face (face ef3x)))).
    By Symmetry; Rewrite: 2!fEnne -arity_face Enode /ef3x /inv_face2 !De2 -eEnf.
  Step Es2: (edge (face (inv_face2 effx))) = (face ef3x).
    By Rewrite: /inv_face2 Enode De2 -{(node effx)}Enode /effx -fEnne.
  Rewrite: {1}/effx De2; Pose ef4x := (edge (face (face (face (face x))))).
  Step Ef21: (arity (edge (face (face ef4x))))
            = (arity (edge (iter (subn n (2)) face ef3x))).
    Rewrite: /ef4x 3!fEnne -/ef3x -arity_face Enode De2 Dn3.
    Rewrite: -{1 ef3x}iter_face_arity /n -(leq_add_sub (HgF ef3x)) -/n /=.
    By Rewrite: Eface -eEnf.
  Case: p4 Hxp4 => [|s2 s1 p|s1 h12 p|s1 h12 f21 p|h f1 f2 f3 p];
    Try (By Simpl; Split); Case: p; Rewrite: /= ?Et59 ?if_same /=; Try By Split.
    Move=> h23 f21 p; Case/and5P=> [Hs2 Hs1 Hh23 Hf21 _] {p}; Rewrite: !Et59 /=.
    Case (t59 f21).
      Rewrite: Et59 if_same /=; Split; LeftDone.
      By Rewrite: !HgF Es1 Es2 /ef3x Hs1 arity_face Hs2 /inv_face2 !Enode /=.
    Case: s2 Hs2; Simpl; First [By Split | Rewrite: Es1 Es2 arity_face -/ef3x -/n];
      Move=> Dn; Split; Rewrite: // -(eqP Dn) set11 !HgF /inv_face2 !Enode;
      By Rewrite: Ef21 -(eqP Dn) /= in Hf21; Rewrite: Hf21 /ef3x Hs1 /=.
    Rewrite: -/ef3x -/ef4x Es1 Es2 !HgF arity_face /=.
    Move=> h23 f21 p; Case/and5P=> [Dn Hs1 Hh12 Hh23]; Case/andP=> [Hf21 _] {p}.
    Rewrite: Ef21 -(eqP Dn) /= in Hf21.
    By Split; RightBy Rewrite: Dn Hs1 Hh12 Hf21 /inv_face2 !Enode /=.
  Rewrite: -/ef3x -/ef4x Es1 Es2 !HgF arity_face /=.
  Move=> h23 f22 p; Move/and5P=> [Dn Hs1 Hh12 Hf21]; Move/and3P=> [Hh23 Hf22 _]{p}.
  Rewrite: Ef21 -(eqP Dn) /= in Hf22.
  By Split; RightBy Rewrite: Dn Hs1 Hh12 Hf21 Hf22 /inv_face2 !Enode /=.
Move: {p4 Hxp4}(conv_part12 p4) Hh23q12 => [h23 q12] [Hh23 Hq12].
Move: (drop_part (5) p1) (size_drop_part (5) p1)  (fitp_drop (5) Hxp1) => p6 Ep6.
Step Exp6: (arity x) = (addn (5) (size_part p6)).
  By Rewrite: Ep6 -(eqP Exp1) leq_add_sub.
Simpl; Clear Exp1 Ep6; Move=> Hxp6.
Rewrite: -2!arity_face {1}/inv_face2 !Enode Hu /=; Apply Hq12; Clear Hq12 q12.
Case: p6 Hxp6 Exp6; Rewrite: // /=.
  By Move=> _ Ex5; Rewrite: Hh23 /effx De2 !arity_face Ex5 /=.
Move=> f31 h p7; Move/and3P=> [Hf31 _ Hp7] {h}; Case: p7 Hp7 => //=.
  By Move=> _ Ex6; Rewrite: Hh23 /effx De2 !arity_face Ex6 /=.
Move=> f32 h p8; Move/and3P=> [Hf32 _ Hp8] {h}; Case: p8 Hp8 => //=.
  Move=> _ Ex7; Rewrite: !Et59.
  Case (t59 f31); Case (t59 f32);
    By Rewrite: /= Hh23 /effx De2 !arity_face Ex7 ?Hf31 ?Hf32 /=.
Move=> f33 h p9; Move/andP=> [Hf33 _] {h}; Case: p9 => //=.
By Move=> Ex8; Rewrite: Hh23 /effx De2 !arity_face Hf31 Hf32 Hf33 Ex8 /=.
Qed.

End FitConversePart.

Section FitSplitPart.

Variable g : hypermap.
Hypothesis HgF : (pentagonal g).

Lemma fitp_pcons_ : (x : g; n : nat) (fitp x (pcons_ n)).
Proof. By Move=> x n; Elim: n x => [|n Hrec] x; Rewrite: //= !HgF Hrec. Qed.

Lemma exact_fitp_pcons_ : (x : g) (exact_fitp x (pcons_ (arity x))).
Proof. By Move=> x; Rewrite: /exact_fitp fitp_pcons_; Elim (arity x). Qed.

Definition fitc [i : subpart_loc; j, k : nat; x : g] : bool :=
  (ltn k (arity (i g (iter j face x)))).

Lemma fitp_split : (i : subpart_loc; j, k : nat; p : part)
    (good_split i j k p) -> (lo : bool; x : g)
  (exact_fitp x (split_part i j k lo p)) =
     (andb (addb lo (fitc i j k x)) (exact_fitp x p)).
Proof.
Move=> i j k p Hp lo x; Rewrite: /exact_fitp size_split_part andbCA; Congr andb.
Move: Hp; Rewrite: /split_part /good_split.
Step Hupdate:  (pc : prange -> part -> part) (part_update pc i) ->
  (p' : part; r : prange)
     (size_part (drop_part j p)) = (size_part (pc r p')) ->
     ((y : g) (fitp y (drop_part j p)) = (fitp y (pc r p'))) ->
     (good_rsplit k r) ->
  let p'' = (cat_part (take_part j p) (pc (split_range k lo r) p')) in
  let aijx = (arity (i g (iter j face x))) in
  (fitp x p'') = (andb (addb lo (ltn k aijx)) (fitp x p)).
  Move=> pc Hpc p' r Ep' Hp' Hkr.
  Move: (Hpc r p') (Hpc (split_range k lo r) p') => [Erp Hrp] [Erp' Hrp'].
  Rewrite: -{2 p}(cat_take_drop_part j) /= !fitp_cat; BoolCongr.
  Step []: j = (size_part (take_part j p)).
    Apply (!addn_injr (size_part (drop_part j p))).
    Rewrite: -size_cat_part cat_take_drop_part size_drop_part leq_add_sub //.
    By Rewrite: ltnW // ltn_lt0sub -size_drop_part Ep' Erp.
  Rewrite: Hp'; Apply/idP/idP.
    Move/(Hrp' ? ?)=> [Hx Hr]; Rewrite: fit_split_range // in Hx.
    By Move/andP: Hx => [Hcx Hx]; Rewrite: Hcx Hr.
  Case/andP=> [Hcx]; Move/(Hrp ? ?)=> [Hx Hr]; Apply Hr.
  By Rewrite: fit_split_range // Hcx.
Case: (drop_part j p) Hupdate => [|s h p'|h f1 p'|h f1 f2 p'|h f1 f2 f3 p'];
  Case: i => // [] Hupdate.
By Apply: (Hupdate ? (updatePs h)).
By Apply: (Hupdate ? (updatePh s)).
Case: s Hupdate => // [] Hupdate.
  By Apply: (Hupdate ? (updateP6f1 h)) => //= [y]; Rewrite: !HgF.
  By Apply: (Hupdate ? (updateP7f1 h Pr59)) => //= [y]; Rewrite: !HgF.
  By Apply: (Hupdate ? (updateP8f1 h Pr59 Pr59)) => //= [y]; Rewrite: !HgF.
Case: s Hupdate => // [] Hupdate.
  By Apply: (Hupdate ? (updateP7f2 h Pr59)) => //= [y]; Rewrite: !HgF.
  By Apply: (Hupdate ? (updateP8f2 h Pr59 Pr59)) => //= [y]; Rewrite: !HgF.
Case: s Hupdate => // [] Hupdate.
  By Apply: (Hupdate ? (updateP8f3 h Pr59 Pr59)) => //= [y]; Rewrite: !HgF.
By Apply: (Hupdate ? (updateP6h f1)).
By Apply: (Hupdate ? (updateP6f1 h)).
By Apply: (Hupdate ? (updateP7h f1 f2)).
By Apply: (Hupdate ? (updateP7f1 h f2)).
By Apply: (Hupdate ? (updateP7f2 h f1)).
By Apply: (Hupdate ? (updateP8h f1 f2 f3)).
By Apply: (Hupdate ? (updateP8f1 h f2 f3)).
By Apply: (Hupdate ? (updateP8f2 h f1 f3)).
By Apply: (Hupdate ? (updateP8f3 h f1 f2)).
Qed.

End FitSplitPart.

Unset Implicit Arguments.
