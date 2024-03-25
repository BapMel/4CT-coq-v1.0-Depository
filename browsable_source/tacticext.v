(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Set Implicit Arguments.

(* Syntax extensions for tactics, which shorten considerably our proof     *)
(* scripts. These extensions fall in three categories:                     *)
(*  - Tagging constructs that give control over reduction and rewriting.   *)
(*  - Proof layout improvemnents: a Step tactic to introduce proof steps,  *)
(*    and Done, LeftDone, RightDone, By, LeftBy and RightBy tactics to     *)
(*    close subgoals.                                                      *)
(*  - Name and context management improvements: exteneded versions of the  *)
(*    Clear, Move, Case, Elim, Apply, Injection and Rewrite tactics, and   *)
(*    a new Def: tactic. These extensions also include a more uniform way  *)
(*    of selecting occurences, and a facility for inserting a "view" prior *)
(*    to case analysis (this is actually defined in boolprop.v).           *)
(*    The Rewrite: tactic allows multiple and repeat rewrites, and the     *)
(*    Move:, Case: and Elim: tactics have an equation generation facility. *)
(* An effort has been made to keep the generated tactic script clean, so   *)
(* no special pretty-printing extensions are needed.                       *)

(* Tactic grammar debugging. *)

Grammar tactic tactic : ast :=
  explode_ast [ "ExplodeAst" tactic($tac) ] ->
    let (UNMATCHABLE) = [$tac] in [(EXPLODE)].

(*   We also provide here implicit-argument shorthand forms for six common *)
(* equality lemmas, syntax for picking apart options, and a Congr tactic   *)
(* that tries to shoehorn congruence on a goal.                            *)

Definition erefl := refl_equal.
Definition esym := sym_eq.
Definition nesym := sym_not_eq.
Definition etrans := trans_eq.
Definition congr := f_equal.
Definition congr2 := f_equal2.

Grammar constr if_is_pat : ast :=
  if_is_pat_id [tactic:identarg($var)] -> [(QUALID $var)]
| if_is_pat_contruct ["(" tactic:identarg($var) if_is_pat_list($pats) ")"] ->
  [(PATTCONSTRUCT (QUALID $var) ($LIST $pats))]
with if_is_pat_list : ast list :=
  cons_if_is_pat_wild ["_" if_is_pat_list($pats)] -> [(QUALID _) ($LIST $pats)]
| cons_if_is_pat [if_is_pat($pat) if_is_pat_list($pats)] -> [$pat ($LIST $pats)]
| last_if_is_pat_wild ["_"] -> [(QUALID _)]
| last_if_is_pat [if_is_pat($pat)] -> [$pat].

Grammar constr constr1 : ast :=
  ifSome ["if" constr($opt) "is" if_is_pat($pat)
          "then" constr($some) "else" constr($none)] ->
  [(CASES "SYNTH" (TOMATCH $opt)
      (EQN $some $pat)
      (EQN $none (QUALID _)))].

Syntax constr
  level 1:
    pp_ifSome3 [<<(CASES $_ (TOMATCH $opt)
     (EQN $some (PATTCONSTRUCT <<Some>> $var))
     (EQN $none (PATTCONSTRUCT <<None>>)))>>]
    -> [ [<hov 0> [<hov 0> "if " $opt:E [1 4] "is (Some " $var ")"]
                      [1 2] "then " $some:E [1 2] "else " $none:E] ].

(* Pretty-printing annotations. Usage :                                       *)
(*     (pretty e) or e :: pretty                                              *)
(* when e is of type t, generates the term (of type (pretty_printed t))       *)
(*     (Pretty t e)                                                           *)
(* which (by default) prints as                                               *)
(*     (pretty e :: t)                                                        *)
(* This default is obviously meant to be overridden, by matching against t in *)
(* the pretty-printing rules.                                                 *)

Inductive pretty_printed [A : Type] : Set := Pretty : A -> (pretty_printed A).
Implicits Pretty [].
Grammar constr constr10 : constr :=
  pretty_form ["pretty" constr9($e)] -> [(Pretty ? $e)]
with constr9 : constr :=
  pretty_coerce [constr8($e) "::" "pretty"] -> [(Pretty ? $e)].
Syntax constr level 10 :
  pp_pretty_call [(Pretty $t $e)] -> [[<hv 2> "pretty " (PPDEFAULT $e $t)]].
Syntax constr level 9 :
  pp_pretty_default_arg [<<(PPDEFAULT $e $t)>>] -> [$e:L [1 0] ":: " $t:L].

(* Generic support for printing bracketed operator forms.                    *)

Syntax constr level 10:
    pp_opform [<<(OPFORM $op $arg1 ($LIST $args))>>] ->
    [ "(" $op [<hv 0>  " " $arg1:L (APPTAIL ($LIST $args)) ")"] ]
  | pp_opform0 [<<(OPFORM $op)>>] ->
    ["(" $op ")"]
  | pp_expopform [<<(EXPOPFORM $op $arg1 ($LIST $args))>>] ->
    [ "(!" $op [<hv 0>  " " $arg1:L (APPTAIL ($LIST $args)) ")"] ]
  | pp_expopform0 [<<(EXPOPFORM $op)>>] ->
    ["(!" $op ")"].

(* Ast forms for passing separators in printing forms                       *)
Syntax constr level 0:
  pp_sep_no  [<<(SEP NO)>>] -> [ ]
| pp_sep_spc [<<(SEP SPC)>>] -> [" "]
| pp_sep_cut [<<(SEP CUT)>>] -> [[0 0]]
| pp_sep_brk [<<(SEP BRK)>>] -> [[1 0]].

(* We provide two strengths of term tagging :                               *)
(*  - (nosimpl t) simplifies to t EXCEPT in a definition; more precisely,   *)
(*    given Definition foo := (nosimpl bar), foo (or (foo t')) will NOT be  *)
(*    expanded by the Simpl tactic unless it is in a forcing context (e.g., *)
(*    in Cases (foo t') of ... (foo t') will be reduced if this enables the *)
(*    reduction of the Cases). Note that (nosimpl bar) is a syntax macro for*)
(*    a term that beta-iota reduces to bar; hence Unfold foo will replace   *)
(*    foo by bar, and Fold foo will replace bar by foo. A final warning:    *)
(*    nosimpl only works if no reduction is apparent in t; in particular    *)
(*    Definition foo [x] := (nosimpl t) will usually not work.              *)
(*  - (locked t) is provably equal to t, but is not convertible to t; it    *)
(*    provides support for abstract data types, and selective rewriting.    *)
(*    The equation t == (locked t) is provided as a lemma, but it should    *)
(*    only be used for selective rewriting (see below). For ADTs, the       *)
(*    Unlock tactic should be used to remove locking; its syntax is         *)
(*      Unlock [['{' <positive-integer>+ '}'] <ident>]*                     *)
(*    and it simultaneously unfolds the occurrences specified by its        *)
(*    arguments, and removes all explicit locks in the resulting expansion. *)
(* A different 'mark' construct is used below for the implementation of     *)
(* Elim equations.                                                          *)

Grammar constr constr0 : constr :=
  hold_term_simpl ["(" "nosimpl" lconstr($term) ")"] ->
    [ Cases tt of tt => $term end ].

Syntax constr
  level 0:
    pp_nosimpl [<<(CASES $_ (TOMATCH <<tt>>) (EQN $term $_))>>] ->
      [ (OPFORM nosimpl $term) ]
  | pp_nosimpl_appl [<<(CASES $_ (TOMATCH <<tt>>)
                          (EQN (APPLIST ($LIST $terms)) $_))>>] ->
      [ (OPFORM nosimpl ($LIST $terms)) ].

Lemma master_key : unit. Proof. Exact tt. Qed.

Definition locked [A : Type] : A -> A :=
  Cases master_key of tt => [x]x end.

Grammar tactic simple_tactic : ast :=
  unlock_tactic ["Unlock" unlock_occ_list($occs)] ->
    let $lockocc = [(UNFOLD (QUALIDARG locked))] in
    let $utac = [(Reduce (REDEXP (Unfold ($LIST $occs) $lockocc)) (CLAUSE))] in
    [<:tactic:<$utac; Case master_key>>]
with unlock_occ_list : ast list :=
  cons_unlock_occ [unlock_occ($occ) unlock_occ_list($occs)] ->
  [$occ ($LIST $occs)]
| no_unlock_occs [ ] -> [ ]
with unlock_occ : ast :=
  num_unlock_occ ["{" unlock_num_list($nums) "}" qualidarg($qid)] ->
  [(UNFOLD $qid ($LIST $nums))]
| no_num_unlock_occ [qualidarg($qid)] ->
  [(UNFOLD $qid)]
with unlock_num_list : ast list :=
  cons_unlock_num [prim:number($n) unlock_num_list($nums)] -> [$n ($LIST $nums)]
| last_unlock_num [prim:number($n)] -> [$n].

Lemma lock : (A : Type; x : A) x == (locked x). Proof. Unlock; Split. Qed.

Definition mark_predicate [A : Type; x : A] : A := x.

(* Tactics for closing subgoal on a single line.                           *)
(* Syntax :                                                                *)
(*    Done                                                                 *)
(*    'By' <tactic>                                                        *)
(*    <tactic-expr> ';' 'LeftDone'                                         *)
(*    <tactic-expr> ';' 'LeftBy' <tactic>                                  *)
(*    <tactic-expr> ';' 'RightDone'                                        *)
(*    <tactic-expr> ';' 'RightBy' <tactic>                                 *)
(* The <tactic> non-terminal allows tactic sequences on the right of 'By', *)
(* 'LeftBy', and 'RightBy'. Note that 'By' cannot be inserted before an    *)
(* alternative; one must write, e.g., By Case b; [t1 | t2]. rather than    *)
(* Case b; By [t1 | t2].                                                   *)

(* Needed for locked predicates, in particular for dataSet. *)
Lemma not_locked_false_eq_true : ~ (locked false) = true.
Proof. Unlock; Discriminate. Qed.

Tactic Definition Done :=
  Solve [Trivial | Repeat Split | Contradiction | Intros;
   First [Discriminate | Case not_locked_false_eq_true; Assumption
         | Apply esym; Trivial]].

Grammar tactic simple_tactic : tactic :=
  close_branch [ "By" tactic($tac) ] -> [$tac; Done].

Grammar tactic tactic_expr : tactic :=
  left_branch_done [ tactic_expr($tac1) ";" "LeftDone" ] ->
    [$tac1; [Done | Idtac]]
| left_branch_by [ tactic_expr($tac1) ";" "LeftBy" tactic($tac2) ] ->
    [$tac1; [$tac2; Done | Idtac]]
| right_branch_done [ tactic_expr($tac1) ";" "RightDone" ] ->
    [$tac1; [Idtac | Done]]
| right_branch_by [ tactic_expr($tac1) ";" "RightBy" tactic($tac2) ] ->
    [$tac1; [Idtac | $tac2; Done]].

(* The Step tactic is sugar for an inverted Cut/Intro.                     *)
(* Syntax :                                                                *)
(*   'Step' <intro-pattern> ':' <term> ['By' <tactic>]                     *)
(* The simplest form of this tactic, Step <name>: <term>, generates a      *)
(* subgoal <term>, and adds an assumption  <name> : <term> for the current *)
(* goal. The <term> goal is generated BEFORE the main goal, so that the    *)
(* proof script can be laid out as follows :                               *)
(*   Step S23 : assertion.                                                 *)
(*     proof of assertion.                                                 *)
(*   resume main proof, with an assumption S23 : assertion in the context. *)
(* If present, the 'By' part should provide a proof of <term> (up to Done).*)
(* In the general form, the ``step name'' can be any intro pattern, so one *)
(* can write                                                               *)
(*     Step [Ha Hb] : Pa /\ Pb.                                            *)
(* for conjunctive steps (to factor inductions/rewrites);                  *)
(*     Step [Ha | Hb | Hc] : Ca \/ Cb \/ Cc.                               *)
(* to introduce explicity a case analysis;                                 *)
(*     Step [x Hx] : (EX x | (P x)).                                       *)
(*  or Step [x Hx] : {x : A | (P x)}.                                      *)
(* to introduce the construction of some value;                            *)
(*     Step [ ] : v2 = v1.                                                 *)
(* to replace v1 by v3 and prove the equation immediately.                 *)
(*     Step x : t.                                                         *)
(* to construct an intermediate value of any type t when building a        *)
(* definition with the tactic engine (proof_step is transparent to cater   *)
(* to that case).                                                          *)

Definition proof_step [Pstep, Pgoal : Type; X : Pstep; F : Pstep -> Pgoal]
                     : Pgoal := (F X).
Implicits proof_step [2].

Grammar tactic simple_tactic : ast :=
  proof_step
    [ "Step" simple_intropattern($pattern)
        ":" command:command($goal) step_tactic($tactic) ] ->
  let $intros = [(Intros (INTROPATTERN (LISTPATTERN $pattern)))] in
  [<:tactic:<Apply (proof_step $goal); [$tactic | $intros]>>]
with step_tactic : tactic :=
  step_by_tactic [ "By" tactic($tactic) ] -> [$tactic; Done]
| no_step_by_tactic [ ] -> [Idtac].

(* Later in the development, we use grammar rules to unconditionally     *)
(* add implicit arguments to an identifier, so that it exhibits ML-style *)
(* polymorphism (e.g., one can write (maps size some_sequence), even     *)
(* though "size" is polymorphic). However, these arguments should be     *)
(* stripped in pattern contexts, so we define a variant of the constrarg *)
(* entry that does this. We also add the notation (!f) to refer to the   *)
(* stripped f explicitly in other contexts.                              *)

Grammar tactic constrarg_noexp : ast :=
  constr_noexp_var [ identarg($var) ] -> [(COMMAND (QUALID $var))]
| constr_noexp_term [ constrarg($term) ] -> [$term].

Grammar constr constr10 : constr :=
  strip_implicits ["!" global($var)] -> [($var :: ?)].

(* A variant of the Clear tactic that deletes a list of assumptions from    *)
(* the context RIGHT to LEFT, that is, in the order that is consistent with *)
(* the other tactics (Intros, Generalize, and all the extensions defined    *)
(* below. The syntax is:                                                    *)
(*   'Clear' ':' <ident>+                                                   *)
(*   'Clear'                                                                *)
(* The second "defective" form, where no assumption is given, is equivalent *)
(* equivalent to "Intros _", that is, it simply pops the first premise from *)
(* the goal and then deletes it. The same concept applies to several other  *)
(* extended commands below; the defective form always means "intro ONE      *)
(* assumption, and operate on it".                                          *)

Grammar tactic clear_list_tac : ast :=
  mk_clear_list_tac [ clear_list($hyps) ] -> [(Clear (CLAUSE ($LIST $hyps)))]
with clear_list : ast list :=
  clear_hyps [idmetahyp($hyp) clear_list($hyps)] -> [($LIST $hyps) $hyp]
| clear_hyp  [idmetahyp($hyp)] -> [$hyp]
with opt_clear_list : ast list :=
  some_clear_list [clear_list($hyps)] -> [($LIST $hyps)]
| no_clear_list [ ] -> [ ].

Grammar tactic simple_tactic : tactic :=
  clear_right_to_left ["Clear" ":" clear_list_tac($clear)] -> [$clear]
| intro_then_clear ["Clear"] -> [Intros _].

(* The extended "Move" tactic is the main workhorse in our scripts. It is  *)
(* the basic command for managing the assumption context; it can perform   *)
(* all the basic operations, such as creating, renaming, deleting,         *)
(* splitting, etc. It provides a coherent package of operation that        *)
(* subsumes Intros, Generalize, Clear, LetTac, Pattern, Move, Rename, and  *)
(* several other tactics. The syntax is                                    *)
(*   'Move' [<view>] [<gens>] [<clear>] ['=>' <intros>]                    *)
(*       where  <gens> ::= [<ident>]  ':' <gen>+                           *)
(*               <gen> ::= [<clear> | '{}' | <occ>] <term>                 *)
(*            <intros> ::= [<simpl>] <intro>* ['*']                        *)
(*             <intro> ::= <intro-pattern> [<clear>] [<simpl>]             *)
(*             <clear> ::= '{' <ident>+ '}'                                *)
(*               <occ> ::= '{' <integer>+ '}'                              *)
(*              <view> ::= '/' <term>                                      *)
(*             <simpl> ::= '/=' | '//' | '//='                             *)
(* with the restriction that the <intros> part after an '=>' may not be    *)
(* entirely empty (there should be at least a <simpl>, <intro> or '*'.     *)
(*   In a nutshell, a Move first generalizes all the <term>s in the <gens> *)
(* then performs all the introductions specified in the <intros>, and in   *)
(* between it removes all the assumptions whose name appears in the        *)
(* <clear>s, or is EQUAL to one of the <gen> terms. Thus we have a single  *)
(* facility for moving assumptions to and from the goal, and splitting     *)
(* them as well since we allow general intro patterns on the right of =>.  *)
(*   All these operations are performed in a consistent order: first the   *)
(* generalizations (right to left), then all the clears collated from the  *)
(* left of '=>', RIGHT to LEFT also (see the Clear: tactic above), then    *)
(* the <intro>s, left to right, interspersed with the remaining <clear>s,  *)
(* which are therefore performed left to right (however, the list for each *)
(* individual <clear> is deleted right to left).                           *)
(*    The <clear> part of a <gen> should be used to delete variables that  *)
(* occurred only in the generalized term, or in irrelevant hypotheses      *)
(* also deleted in the same <clear>; conversely, '{}' (the empty <clear>)  *)
(* prevents the deletion of the following term (which is the default if    *)
(* this term is a simple identifier). Thus "Move: {}x" and "Move: (x)"     *)
(* are both equivalent to "Generalize x", while "Move: x" is equivalent    *)
(* to "Generalize x; Clear x". Note that '{}' should always appear before  *)
(* global lemma and constructor names, since attempting to delete them is  *)
(* an error. The <clear> after the <gens> should be used to delete other   *)
(* irrelevant hypotheses, variables or definition. The <clear> after an    *)
(* <intro> can be used to delete a variable whose only occurrences were in *)
(* premises deleted by the intro (using '_' patterns).                     *)
(*    The <simpl> annotations can be used to further simplify or even to   *)
(* solve the goal: a '/=' triggers an intermediate Simpl, while '//'       *)
(* attemps to use 'Done' to eliminate trivial subgoals, and '//=' does     *)
(* both. The optional <clear> that precedes a <simpl> is performed after   *)
(* the simplification, so it can for instance delete irrelevant fields of  *)
(* a record after simplification, of assumptions that were used to solve   *)
(* the trivial cases. Likewise, the <simpl> that precedes the intros is    *)
(* performed before the left hand side <clear>s (this becomes more useful  *)
(* for the extended Case and Elim tactics introduced below).               *)
(*    The trailing '*' in <intros> triggers a naked Intros, which can be   *)
(* useful to reintroduce hypotheses under the same names, e.g., after some *)
(* common term has been generalised and/or decomposed.                     *)
(*    The <occ> part of a <gen> is used to specify that only certain       *)
(* occurrences of the <term> should be generalized. When it is present,    *)
(* the <term> is never cleared, even if it is a simple identifier. As with *)
(* the primitive Pattern tactic, <occ> can be either a list of positive or *)
(* of negative integers, specifying which occurrences of the <term> should *)
(* or should not be generalized, respectively.                             *)
(*    The <view>, when present, specifies a term that is applied to the    *)
(* first term before it is generalized (or to the first premise of the     *)
(* goal, in the "defective" case). This "application" can actually use     *)
(* one of the boolean reflection lemmas, so the actual implementation of   *)
(* this feature is in file boolprop.v. Note, finally, that the occurrence  *)
(* list of the viewed term, if present at all, should be empty.            *)
(*   If the optional <ident> before the ':' is present, an additional      *)
(* equality t = t is generalized before the first term t, and only the     *)
(* second t in t = t is generalized. The equation is introduced as <ident> *)
(* right after the first pattern in the intros (which should always be     *)
(* present). Note that t is not cleared, even if it is an identifier (any  *)
(* <clear> is ignored), and that the equation is actually (v t) = ... if a *)
(* view v is present.                                                      *)
(*   If the <gens> part is omitted, then the first term to be generalized  *)
(* is obtained by introducing the first premise of the goal (we will refer *)
(* to this case as the "defective" form in the following). If no <view> is *)
(* present, then this is almost a noop, and so Move=> is basically an      *)
(* extension of Intros. This syntax really becomes useful if a <view> is   *)
(* given. Note however that even the naked Move tactic is not quite a      *)
(* noop: it exposes the first abstraction in the goal.                     *)

Tactic Definition GeneralizePattern :=
  Apply [A : Type; P : A -> Type; H : (x : A)(P x)]H.

Lemma generalize_eq_pattern : (A : Set; P : A -> Type; x : A)
  ((eqvar : A)(x = eqvar) -> (P eqvar)) -> (P x).
Proof. Auto. Qed.

Lemma generalize_eqT_pattern : (A : Type; x : A; P : A -> Type)
  ((eqvar : A)(x == eqvar) -> (P eqvar)) -> (P x).
Proof. Auto. Qed.

Tactic Definition GeneralizeEqPattern  :=
  First [Apply generalize_eq_pattern | Apply generalize_eqT_pattern].

Grammar tactic simpl_tac : tactic :=
  slash_simpl_done ["/" "="] -> [Simpl; Try Done]
| slash_done ["/"] -> [Try Done]
| slash_simpl ["="] -> [Simpl].

Grammar tactic ext_intros_post : tactic :=
   ext_intros_simpl_clear ["{" clear_list_tac($t2) "}" "/" simpl_tac($t1)] ->
   [$t1; $t2]
|  ext_intros_simpl ["/" simpl_tac($t)] -> [$t]
|  ext_intros_clear ["{" clear_list_tac($t) "}"] -> [$t].

Grammar tactic ext_intros_tac : ast :=
  mk_ext_intros_itac [ext_intros($ei)] ->
  case [$ei] of
    (EI (IP) (T $t)) -> [$t]
  | (EI (IP ($LIST $ips)) $t2o) ->
    let $t1 = [(Intros (INTROPATTERN (LISTPATTERN ($LIST $ips))))] in
    case [$t2o] of (T $t2) -> [<:tactic:<$t1; $t2>>] | $_ -> [$t1] esac
  esac
with ext_intros : ast :=
  cons_ext_ipat_post
    [simple_intropattern($ip1) ext_intros_post($t2) ext_intros_tac($t3)] ->
  [(EI (IP $ip1) (T <:tactic:<$t2; $t3>>))]
| cons_ext_ipat_nopost [simple_intropattern($ip1) ext_intros($ei)] ->
  let (EI (IP ($LIST $ips)) $t2o) = [$ei] in
  [(EI (IP $ip1 ($LIST $ips)) $t2o)]
| last_ext_ipat_post [simple_intropattern($ip1) ext_intros_post($t2)] ->
  [(EI (IP $ip1) (T $t2))]
| last_ext_ipat_nopost [simple_intropattern($ip1)] ->
  [(EI (IP $ip1) (T))]
| ext_intros_all ["*"] ->
  [(EI (IP) (T (Intros)))].

Grammar tactic ext_simpl_intros_tacs : ast :=
  ext_simpl_and_intros ["/" simpl_tac($s) ext_intros_tac($i)] ->
  [(I (S $s) $i)]
| ext_simpl_no_intros ["/" simpl_tac($s)] ->
  [(I (S $s))]
| ext_no_simpl_intros [ext_intros_tac($i)] ->
  [(I (S) $i)].

Grammar tactic ext_simpl_intros_opt_tacs : ast :=
  some_ext_intros_tac ["=>" ext_simpl_intros_tacs($si)] -> [$si]
| no_ext_intros_tac [ ] -> [(I (S)) ].

Grammar tactic ext_move_intros_eq_tac : ast :=
  make_ext_move_intros_eq [ext_intros($ei)] ->
   case [$ei] of
     (EI (IP) (T $t)) ->
     [<:tactic:<Intro; Intros ext_eq_name; $t>>] (* Intros *)
   | (EI (IP $ip1 ($LIST $ips)) $t2o) ->
     let $lip = [(LISTPATTERN $ip1 (IDENTIFIER ext_eq_name) ($LIST $ips))] in
     let $t1 = [(Intros (INTROPATTERN $lip))] in
     case [$t2o] of (T $t2) -> [<:tactic:<$t1; $t2>>] | $_ -> [$t1] esac
  esac.

Grammar tactic ext_move_simpl_intros_eq_opt_tacs : ast :=
  ext_move_simpl_and_intros_eq
    ["=>" "/" simpl_tac($s) ext_move_intros_eq_tac($i)] ->
  [(I (S $s) $i)]
| ext_move_no_simpl_intros_eq
    ["=>" ext_move_intros_eq_tac($i)] ->
  [(I (S) $i)]
| ext_move_simpl_no_intros_eq
    ["=>" "/" simpl_tac($s)] ->
  [(I (S $s))]
| ext_move_no_intros_eq
    [] ->
  [(I (S) <:tactic:<Intro; Intros ext_eq_name>>)].

Grammar tactic ext_occ : ast list :=
  cons_ext_occ [pure_numarg($num) ext_occ($occ)] -> [$num ($LIST $occ)]
| last_ext_occ [pure_numarg($num)] -> [$num].

Grammar tactic opt_ext_occ : ast list :=
  some_ext_occ [ext_occ($occ)] -> [($LIST $occ)]
| no_ext_occ [] -> [].

Grammar tactic ext_gen_term : ast :=
  ext_gen_term_var [identarg($id)] -> 
  [(GT (PATTERN (COMMAND (QUALID $id))) (INHYP $id))]
| ext_gen_term_novar [constrarg($term)] ->
  [(GT (PATTERN $term))].

Grammar tactic ext_gen : ast :=
  ext_gen_clear ["{" clear_list($ids2) "}" ext_gen_term($gt)] -> 
  let (GT $pat ($LIST $ids1)) = [$gt] in
  [(GT $pat ($LIST $ids1) ($LIST $ids2))]
| ext_gen_occ ["{" opt_ext_occ($occ) "}" constrarg_noexp($term)] ->
  [(GT (PATTERN $term ($LIST $occ)))]
| ext_gen_plain [ext_gen_term($gt)] ->
  [$gt].

Grammar tactic ext_gens : ast :=
  ext_gens_merge_cons [ext_gens_cons($egc)] ->
  case [$egc] of
    (EGC (PATTERN $term) $t1o (G ($LIST $g)) ($LIST $clr)) ->
      [(EG $t1o (G $term ($LIST $g)) ($LIST $clr))]
  | (EGC $pat (T ($LIST $t1o)) (G ($LIST $g)) ($LIST $clr)) ->
      let (T ($LIST $t2o)) = case [(Generalize ($LIST $g))] of
        (Generalize) -> [(T)]
      | $t2 -> [(T $t2)]
      esac in
      let $t3 = [(Reduce (REDEXP (Pattern $pat)) (CLAUSE))] in
      let $t4 = [<:tactic:<GeneralizePattern>>] in
      let $t = case [(T ($LIST $t1o) ($LIST $t2o))] of
        (T)         -> [<:tactic:<$t3; $t4>>]
      | (T $t1)     -> [<:tactic:<$t1; $t3; $t4>>]
      | (T $t1 $t2) -> [<:tactic:<$t1; $t2; $t3; $t4>>]
      esac in
      [(EG (T $t) (G) ($LIST $clr))]
  | $eg -> [$eg]
  esac
with ext_gens_cons : ast :=
  ext_gens_cons_clear
    ["{" clear_list($ids2) "}" ext_gen_term($gt) ext_gens($eg)] ->
  let (EG ($LIST $egl)) = [$eg] in
  let (GT $pat ($LIST $ids1)) = [$gt] in
  [(EGC $pat ($LIST $egl) ($LIST $ids1) ($LIST $ids2))]
| ext_gen_last_clear ["{" clear_list($ids2) "}"] ->
  [(EG (T) (G) ($LIST $ids2))]
| ext_gens_occ
    ["{" opt_ext_occ($occ) "}" constrarg_noexp($term) ext_gens($eg)] ->
  let (EG ($LIST $egl)) = [$eg] in
  [(EGC (PATTERN $term ($LIST $occ)) ($LIST $egl))]
| ext_gens_plain [ext_gen_term($gt) ext_gens($eg)] ->
  let (EG ($LIST $egl)) = [$eg] in
  let (GT $pat ($LIST $ids1)) = [$gt] in
  [(EGC $pat ($LIST $egl) ($LIST $ids1))]
| ext_gens_end [ ] ->
  [(EG (T) (G))].

Grammar tactic simple_tactic : ast :=
  move_gens
    ["Move" ":" ext_gen($gt) ext_gens($eg) ext_simpl_intros_opt_tacs($si)] ->
  let (GT $pat ($LIST $ids2)) = [$gt] in
  let (EG (T ($LIST $t1o)) (G ($LIST $g)) ($LIST $ids1)) = [$eg] in
  let (T ($LIST $t24o)) = case [$pat] of
    (PATTERN $term) ->
    [(T (Generalize $term ($LIST $g)))]
  | $_ ->
    let $t3 = [(Reduce (REDEXP (Pattern $pat)) (CLAUSE))] in
    let $t4 = [<:tactic:<GeneralizePattern>>] in
    case [(Generalize ($LIST $g))] of
        (Generalize) -> [(T $t3 $t4)]
      | $t2 -> [(T $t2 $t3 $t4)]
    esac
  esac in
  let (I (S ($LIST $s)) ($LIST $t6o)) = [$si] in
  let (T ($LIST $t5o)) = case [(CLAUSE ($LIST $ids1) ($LIST $ids2))] of
    (CLAUSE) -> [(T ($LIST $s))]
  | $clause -> [(T ($LIST $s) (Clear $clause))]
  esac in
  case [(T ($LIST $t1o) ($LIST $t24o) ($LIST $t5o) ($LIST $t6o))] of
    (T $t1)                     -> [$t1]
  | (T $t1 $t2)                 -> [<:tactic:<$t1; $t2>>]
  | (T $t1 $t2 $t3)             -> [<:tactic:<$t1; $t2; $t3>>]
  | (T $t1 $t2 $t3 $t4)         -> [<:tactic:<$t1; $t2; $t3; $t4>>]
  | (T $t1 $t2 $t3 $t4 $t5)     -> [<:tactic:<$t1; $t2; $t3; $t4; $t5>>]
  | (T $t1 $t2 $t3 $t4 $t5 $t6) -> [<:tactic:<$t1; $t2; $t3; $t4; $t5; $t6>>]
  | (T $t1 $t2 $t3 $t4 $t5 $t6 $t7) ->
                              [<:tactic:<$t1; $t2; $t3; $t4; $t5; $t6; $t7>>]
  esac
| move_eq_gens
    ["Move" identarg($eqname) ":" ext_gen($gt) ext_gens($eg)
      ext_move_simpl_intros_eq_opt_tacs($si)] ->
  let (GT $pat ($LIST $_)) = [$gt] in
  let (EG (T ($LIST $t1o)) (G ($LIST $g)) ($LIST $ids1)) = [$eg] in
  let (T ($LIST $t24o)) = 
    let $t3 = [(Reduce (REDEXP (Pattern $pat)) (CLAUSE))] in
    let $t4 = [<:tactic:<GeneralizeEqPattern>>] in
    case [(Generalize ($LIST $g))] of
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
| move_clear_intros
    ["Move" "{" clear_list_tac($t1) "}" ext_simpl_intros_opt_tacs($si)] ->
  case [$si] of
    (I (S $s) $t2) -> [<:tactic:<Hnf; $s; $t1; $t2>>]
  | (I (S) (Intros)) -> [<:tactic:<Hnf; $t1; Intros>>]
  | (I (S) $t2) -> [<:tactic:<$t1; $t2>>]
  | (I (S $s)) ->  [<:tactic:<Hnf; $s; $t1>>]
  | (I (S)) -> [<:tactic:<Hnf; $t1>>]
  esac
| move_intros
    ["Move" "=>" ext_simpl_intros_tacs($si)] ->
  case [$si] of
    (I (S $s) $t2) -> [<:tactic:<Hnf; $s; $t2>>]
  | (I (S) (Intros)) -> [<:tactic:<Hnf; Intros>>]
  | (I (S) $t2) -> [<:tactic:<$t2>>]
  | (I (S $s)) ->  [<:tactic:<Hnf; $s>>]
  esac
| move_noop
    ["Move"] ->
  [<:tactic:<Hnf>>].

(* The Def: tactic is more a simplification than an extension of the old   *)
(* Let tactic : it provides control over the name of the equation and the  *)
(* substituted occurrences, but doesn't provide for substitution in the    *)
(* context. Syntax :                                                       *)
(*     Def [<eq-name>] ':' <var> [':' <term>] ':=' [<occ>] <term>          *)
(* If the equation name is omitted, then no equation is generated; in this *)
(* case the <var> can be a destructuring pattern (normally conjuctive); if *)
(* <eq-name> is present then <var> must be a single identifier. The Move:  *)
(* tactic above should be preferred for creating destructuring equations,  *)
(* since it puts the original value on the left hand side, whereas Def:    *)
(* puts it on the right hand side -- Def: is really just a  variant of     *)
(* Move: that emphasizes `definition' rather than destructuring/renaming.  *)
(*   The optional `: <term>' is syntactic sugar for a cast; the <occ> part *)
(* is used to specify which occurrences should be captured by the Def.     *)
(*   Finally, this derived Def is almost as broken as the primitive one    *)
(* when <term> is a proof-term, with one (important) improvement: nameless *)
(* Let:s are implemented with  Generalize <term>; Intros <var>, so they    *)
(* work properly for proof-terms.                                          *)

Lemma generalize_def_pattern : (A : Set; x : A; P : A -> Type)
  ((y : A)(y = x) -> (P y)) -> (P x).
Proof. Auto. Qed.

Lemma generalize_defT_pattern : (A : Type; x : A; P : A -> Type)
  ((y : A)(y == x) -> (P y)) -> (P x).
Proof. Auto. Qed.

Tactic Definition GeneralizeDefPattern :=
  First [Apply generalize_def_pattern | Apply generalize_defT_pattern].

Grammar tactic simple_tactic : ast :=
  intro_abstraction
    [ "Def" ":" simple_intropattern($varpat) def_value($valpat)]
  -> let $itac = [(Intros (INTROPATTERN (LISTPATTERN $varpat)))] in
     let $ptac = [(Reduce (REDEXP (Pattern $valpat)) (CLAUSE))] in
     let $gtac = case [$valpat] of
       (PATTERN $term) -> [(Generalize $term)]
     | $_ -> [<:tactic:<$ptac; GeneralizePattern>>]
     esac in [<:tactic:<$gtac; $itac>>]
| intro_definition
    [ "Def" identarg($eqname) ":" identarg($var) def_value($valpat) ]
  -> let $ipat = [(LISTPATTERN (IDENTIFIER $var) (IDENTIFIER $eqname))] in
     let $itac = [(Intros (INTROPATTERN $ipat))] in
     let $ptac = [(Reduce (REDEXP (Pattern $valpat)) (CLAUSE))] in
     [<:tactic:<$ptac; GeneralizeDefPattern; $itac>>]
with def_value : ast :=
  untyped_def_value [ ":=" def_valpat($valpat) ] -> [$valpat]
| typed_def_value [ ":" constr:constr($vtype) ":=" def_valpat($valpat) ] ->
    let (PATTERN (COMMAND $val) ($LIST $occ)) = [$valpat] in
    [(PATTERN (COMMAND (CAST $val $vtype)) ($LIST $occ))]
with def_valpat : ast :=
  def_valpat_occ ["{" ext_occ($occ) "}" constrarg_noexp($term)] ->
  [(PATTERN $term ($LIST $occ))]
| def_valpat_occ [constrarg_noexp($term)] ->
  [(PATTERN $term)].

(* The extended Case is very similar to the extended Move; in fact, in   *)
(* many instances, the two tactics are interchangeable. The Case keyword *)
(* emphsizes case analysis, so it should be preferred when this is the   *)
(* intended operation (as opposed to simply shuffling assumptions).      *)
(*   The most obvious difference between Case and Move is that Case      *)
(* destructures its first term (or the top premise, in the defective     *)
(* case), even when the intros part is empty. If there are intros, then  *)
(* the first pattern must not be a variable.                             *)
(*   A second, more subtle difference, is that the Clear/Simpl is done   *)
(* after the Case on the fist argument, rather than immediately after    *)
(* the generalization, so it can delete variables that might have been   *)
(* substituted by a dependent Case, simplify, or resolve trivial goals.  *)
(*   A third difference is an explicit syntax for dependent elimination: *)
(* a '/' in the <gen>s that separates the dependent parameters (on the   *)
(* left of the '/' from the generalized/destructured terms (on the right *)
(* and possibly defaulting to the top premise). The dependent            *)
(* generalizations on the left hand side can be used to specify exactly  *)
(* which occurrences of the dependent parameters shoud be substituted    *)
(* by the case analysis, and to delete them together with relevant       *)
(* variables, just as "normal" generalizations. If an equation name is   *)
(* present, an equation if generated for the first dependent term. The   *)
(* Case, however, always destructures the first "normal" term on the     *)
(* right hand side of the '/' (or the top premise if there are none).    *)
(*   Thus the general syntax for Case is                                 *)
(*   'Case' [<view>] [<deps> ['/' <dep>*]] [<clear>] ['=>' <intros>]     *)
(* with the restriction that the first <intro-pattern> in <intros> may   *)
(* not be a variable (and <intros> must not be empty, as for Move).      *)
(* Note that the naked "Case" is allowed and useful: it destructures the *)
(* top premise.                                                          *)

Recursive Tactic Definition IntrosUntilName id :=
  Intro; First [Rename id into id | IntrosUntilName id].

Tactic Definition CaseWithEq eqname :=
 GeneralizeEqPattern; Intros unnamed_case_term eqname; Generalize eqname;
 Case unnamed_case_term; Clear eqname unnamed_case_term.

Tactic Definition DestructTop :=
  Intros defective_term; Case defective_term; Clear defective_term.

Definition protect_ctx [A : Type; u : A] : A := [v := u]v.

Tactic Definition CaseWithDepEq name term base pat_tac :=
  Pose eqdep_var := (protect_ctx term);
  Assert name := (erefl eqdep_var); Generalize name;
  pat_tac; Unfold eqdep_var protect_ctx in EqDepBody;
  Replace (EqDepBody eqdep_var term)
     with (protect_ctx [z](EqDepBody z z) term); RightDone;
  Unfold EqDepBody; Lazy Delta [protect_ctx] Beta; Lazy Zeta;
  Clear EqDepBody name eqdep_var; Case base.

Grammar tactic bare_intros_tac : ast :=
  some_bare_intros [one_intropattern($ip)] -> [(Intros $ip)]
| no_bare_intros [ ] -> [<:tactic:<Idtac>>].

Grammar tactic disj_intro_tacs : ast list :=
  some_disj_intro_tacs ["|" bare_intros_tac($t1) disj_intro_tacs($ts)] ->
  [$t1 ($LIST $ts)]
| no_disj_intro_tacs ["|" bare_intros_tac($t1)] -> [$t1].

Grammar tactic ext_novar_intro : ast :=
  one_intro_disj ["[" bare_intros_tac($t) "]" ] -> [$t]
| more_disj_tactics [ "[" bare_intros_tac($t1) disj_intro_tacs($ts) "]"] ->
  [(TACLIST $t1 ($LIST $ts))].

Grammar tactic opt_post_ext_intros_tac : tactic :=
  post_ext_intros [ext_intros_post($t1) ext_intros_tac($t2)] -> [$t1; $t2]
| post_no_ext_intros [ext_intros_post($t)] -> [$t]
| no_post_ext_intros [ext_intros_tac($t)] -> [$t].

Grammar tactic ext_case_intros : ast :=
  ext_case_many_intros
    [ext_novar_intro($t1) opt_post_ext_intros_tac($t2)] ->
  [(D (S) $t1 $t2)]
| ext_case_single_intro
    [ext_novar_intro($t1)] ->
  [(D (S) $t1)]
| ext_case_all_intro
    ["*"] ->
  [(D (S) (Intros))]
| ext_case_simpl_many_intros
    ["/" simpl_tac($s) ext_novar_intro($t1) opt_post_ext_intros_tac($t2)] ->
  [(D (S $s) $t1 $t2)]
| ext_case_simpl_single_intro
    ["/" simpl_tac($s) ext_novar_intro($t1)] ->
  [(D (S $s) $t1)]
| ext_case_simpl_all_intro
    ["/" simpl_tac($s) "*"] ->
  [(D (S $s) (Intros))]
| ext_case_simpl_no_intro
    ["/" simpl_tac($s)] ->
  [(D (S $s))].

Grammar tactic ext_case_opt_intros : ast :=
  ext_case_some_intros ["=>" ext_case_intros($td)] -> [$td]
| ext_case_no_intros [ ] -> [(D (S))].

Grammar tactic ext_dgens : ast :=
  ext_dgens_merge_cons [ext_dgens_cons($egc)] ->
  case [$egc] of
    (EGC $pat $t1o (D (P ($LIST $pats)) $bpat ($LIST $ise)) ($LIST $clr)) ->
    let $dep = [(D (P $pat ($LIST $pats)) $bpat (ISEVAR) ($LIST $ise))] in
    [(EG $t1o $dep ($LIST $clr))]
  | (EGC (PATTERN $term) $t1o (G ($LIST $g)) ($LIST $clr)) ->
    [(EG $t1o (G $term ($LIST $g)) ($LIST $clr))]
  | (EGC $pat (T ($LIST $t1o)) (G ($LIST $g)) ($LIST $clr)) ->
    let (T ($LIST $t2o)) = case [(Generalize ($LIST $g))] of
      (Generalize) -> [(T)]
    | $t2 -> [(T $t2)]
    esac in
    let $t3 = [(Reduce (REDEXP (Pattern $pat)) (CLAUSE))] in
    let $t4 = [<:tactic:<GeneralizePattern>>] in
    let $t = case [(T ($LIST $t1o) ($LIST $t2o))] of
      (T)         -> [<:tactic:<$t3; $t4>>]
    | (T $t1)     -> [<:tactic:<$t1; $t3; $t4>>]
    | (T $t1 $t2) -> [<:tactic:<$t1; $t2; $t3; $t4>>]
    esac in
    [(EG (T $t) (G) ($LIST $clr))]
  | $eg -> [$eg]
  esac
with ext_dgens_cons : ast :=
  ext_dgens_cons_clear
    ["{" clear_list($ids2) "}" ext_gen_term($gt) ext_dgens($eg)] ->
  let (EG ($LIST $egl)) = [$eg] in
  let (GT $pat ($LIST $ids1)) = [$gt] in
  [(EGC $pat ($LIST $egl) ($LIST $ids1) ($LIST $ids2))]
| ext_dgens_last_clear ["{" clear_list($ids2) "}"] ->
  [(EG (T) (G) ($LIST $ids2))]
| ext_dgens_occ
    ["{" opt_ext_occ($occ) "}" constrarg_noexp($term) ext_dgens($eg)] ->
  let (EG ($LIST $egl)) = [$eg] in
  [(EGC (PATTERN $term ($LIST $occ)) ($LIST $egl))]
| ext_dgens_plain [ext_gen_term($gt) ext_dgens($eg)] ->
  let (EG ($LIST $egl)) = [$eg] in
  let (GT $pat ($LIST $ids1)) = [$gt] in
  [(EGC $pat ($LIST $egl) ($LIST $ids1))]
| ext_dgens_dep_gen ["/" ext_gens_cons($egc)] ->
  case [$egc] of
    (EG (T) (G) ($LIST $clr)) ->
     let $var = [defective_premise] in
     let $term = [(COMMAND (QUALID $var))] in
     let $dep = [(D (P) (PATTERN $term) (ISEVAR))] in
     let $t1 = [<:tactic:<Intros $var>>] in
     [(EG (T $t1) $dep ($LIST $clr) (INHYP $var))]
  | (EGC $pat $t1o $gen ($LIST $clr)) ->
     let $dep = [(D (P) $pat (ISEVAR))] in
     let $to = case [$gen] of
       (G) -> [$t1o]
     | (G ($LIST $g)) ->
       let $t2 = [(Generalize ($LIST $g))] in
       case [$t1o] of
         (T $t1) -> [(T <:tactic:<$t1; $t2>>)]
       | (T)     -> [(T $t2)]
       esac
     esac in
     [(EG $to $dep ($LIST $clr))]
  esac
| ext_dgens_end [ ] ->
  [(EG (T) (G))].

Grammar tactic simple_tactic : ast :=
  case_gens
    ["Case" ":" ext_gen($gt) ext_dgens($eg) ext_case_opt_intros($ds)] ->
  let (GT $pat ($LIST $ids2)) = [$gt] in
  let (EG (T ($LIST $t1o)) $gen ($LIST $ids1)) = [$eg] in
  let (D (S ($LIST $t5o)) ($LIST $t78o)) = [$ds] in
  let (T ($LIST $t58o)) = case [(CLAUSE ($LIST $ids1) ($LIST $ids2))] of
    (CLAUSE) -> [(T ($LIST $t5o) ($LIST $t78o))]
  | $clause -> [(T ($LIST $t5o) (Clear $clause) ($LIST $t78o))]
  esac in
  case [$gen] of
    (G ($LIST $g)) ->
    let (T ($LIST $t2o)) = case [(Generalize ($LIST $g))] of
      (Generalize) -> [(T)] | $t2 -> [(T $t2)] esac in
    let (T ($LIST $t34o)) = case [$pat] of
      (PATTERN $term) ->
      [(T (Case $term (BINDINGS)))]
    | (PATTERN $term ($LIST $_)) -> 
      [(T (Reduce (REDEXP (Pattern $pat)) (CLAUSE)) (Case $term (BINDINGS)))]
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
    let $t3a =
      [(Reduce (REDEXP (Pattern $pat ($LIST $pats) $bpat)) (CLAUSE))] in 
    let $t4a =
      let (PATTERN $bterm ($LIST $_)) = [$bpat] in
      [(Case $bterm (BINDINGS))] in
    case [(T ($LIST $t1o) $t3a $t4a ($LIST $t58o))] of
      (T $t1 $t2)                 -> [<:tactic:<$t1; $t2>>]
    | (T $t1 $t2 $t3)             -> [<:tactic:<$t1; $t2; $t3>>]
    | (T $t1 $t2 $t3 $t4)         -> [<:tactic:<$t1; $t2; $t3; $t4>>]
    | (T $t1 $t2 $t3 $t4 $t5)     -> [<:tactic:<$t1; $t2; $t3; $t4; $t5>>]
    | (T $t1 $t2 $t3 $t4 $t5 $t6) -> [<:tactic:<$t1; $t2; $t3; $t4; $t5; $t6>>]
    | (T $t1 $t2 $t3 $t4 $t5 $t6 $t7) ->
                                  [<:tactic:<$t1; $t2; $t3; $t4; $t5; $t6; $t7>>]
    esac
  esac
| case_eq_gens
    ["Case" constrarg_binding_list($eqnamel) ":" ext_gen($gt) ext_dgens($eg)
     ext_case_opt_intros($ds)] ->
  let (B (COMMAND (QUALID $eqname)) (BINDINGS)) = [(B ($LIST $eqnamel))] in
  let (GT $pat ($LIST $_)) = [$gt] in
  let (EG (T ($LIST $t1o)) $gen ($LIST $ids1)) = [$eg] in
  let (T ($LIST $t6o)) = case [(CLAUSE ($LIST $ids1))] of
    (CLAUSE) -> [(T)]
  | $clause -> [(T (Clear $clause))]
  esac in
  let (T ($LIST $t58o)) = case [$ds] of
    (D (S ($LIST $t5o))) ->
    [(T ($LIST $t5o) ($LIST $t6o) <:tactic:<IntrosUntilName $eqname>>)]
  | (D (S ($LIST $t5o)) (Intros)) ->
    [(T ($LIST $t5o) ($LIST $t6o) (Intros))]
  | (D (S ($LIST $t5o)) $t7) ->
    [(T ($LIST $t5o) ($LIST $t6o) $t7 <:tactic:<Intros $eqname>>)]
  | (D (S ($LIST $t5o)) $t7 $t8) ->
    [(T ($LIST $t5o) ($LIST $t6o) $t7 <:tactic:<Intros $eqname; $t8>>)]
  esac in
  case [$gen] of
    (G ($LIST $g)) ->
    let (T ($LIST $t2o)) = case [(Generalize ($LIST $g))] of
      (Generalize) -> [(T)] | $t2 -> [(T $t2)] esac in
    let (PATTERN $term ($LIST $_)) = [$pat] in
    let $t3a = [(Reduce (REDEXP (Pattern $pat)) (CLAUSE))] in  
    let $t34a = [<:tactic:<$t3a; CaseWithEq $eqname>>] in
    case [(T ($LIST $t1o) ($LIST $t2o) $t34a ($LIST $t58o))] of
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
    let $dpat = [(PATTERN (COMMAND (QUALID eqdep_var)) 2)] in
    let $isepat = [(APPLIST (META 1) (ISEVAR) (ISEVAR) ($LIST $ise))] in
    let $t2a =
      [(Reduce (REDEXP (Pattern $dpat $pat ($LIST $pats) $bpat)) (CLAUSE))] in
    let $t4a = [<:tactic:<Pose EqDepBody := ?1>>] in
    let $t34a = [<:tactic:<Match Context With [|- $isepat] -> $t4a>>] in
    let $t24a =
     let (PATTERN $bterm ($LIST $_)) = [$bpat] in
     [<:tactic:<CaseWithDepEq $eqname $term $bterm ($t2a; $t34a)>>] in
    case [(T ($LIST $t1o) $t24a ($LIST $t58o))] of
      (T $t1 $t2)                 -> [<:tactic:<$t1; $t2>>]
    | (T $t1 $t2 $t3)             -> [<:tactic:<$t1; $t2; $t3>>]
    | (T $t1 $t2 $t3 $t4)         -> [<:tactic:<$t1; $t2; $t3; $t4>>]
    | (T $t1 $t2 $t3 $t4 $t5)     -> [<:tactic:<$t1; $t2; $t3; $t4; $t5>>]
    | (T $t1 $t2 $t3 $t4 $t5 $t6) -> [<:tactic:<$t1; $t2; $t3; $t4; $t5; $t6>>]
    esac
  esac
| case_clear_intros
    ["Case" "{" clear_list_tac($t3a) "}" ext_case_opt_intros($ds)] ->
  let (D (S ($LIST $t2o)) ($LIST $t45o)) = [$ds] in
  case [(T <:tactic:<DestructTop>> ($LIST $t2o) $t3a ($LIST $t45o))] of
    (T $t1 $t2)                 -> [<:tactic:<$t1; $t2>>]
  | (T $t1 $t2 $t3)             -> [<:tactic:<$t1; $t2; $t3>>]
  | (T $t1 $t2 $t3 $t4)         -> [<:tactic:<$t1; $t2; $t3; $t4>>]
  | (T $t1 $t2 $t3 $t4 $t5)     -> [<:tactic:<$t1; $t2; $t3; $t4; $t5>>]
  esac 
| case_intros
    ["Case" "=>" ext_case_intros($ds)] ->
  let (D (S ($LIST $t2o)) ($LIST $t34o)) = [$ds] in
  case [(T <:tactic:<DestructTop>> ($LIST $t2o) ($LIST $t34o))] of
    (T $t1 $t2)                 -> [<:tactic:<$t1; $t2>>]
  | (T $t1 $t2 $t3)             -> [<:tactic:<$t1; $t2; $t3>>]
  | (T $t1 $t2 $t3 $t4)         -> [<:tactic:<$t1; $t2; $t3; $t4>>]
  esac 
| naked_case
    ["Case"] ->
  [<:tactic:<DestructTop>>].

(* Yet another similar extension for Elim. Up to the change of keywords,   *)
(* its syntax is identical to that of the extended Case.                   *)
(*   'Elim' [<view>] [<deps> ['/' <dep>*]] [<clear>] ['=>' <intros>]       *)
(* again with the restriction that <intros> may not begin with a variable. *)
(*   As its name implies, the Elim tactic differs from the Case tactic in  *)
(* that it invokes an appropriate induction principle on the first term,   *)
(* rather than just doing case analysis. This is always done, hence the    *)
(* restriction that <intros> may not start with a variable.                *)
(*   There are two more subtle differences with Case. First, the <view>    *)
(* term is used to provide an alternative induction principle (e.g.,       *)
(* reverse induction on lists), rather than a function or a boolean        *)
(* reflection lemma as for Case or Move. Second, the equation does not     *)
(* relate the inductive value with the initial value of the term (which    *)
(* would be useless). Instead, it justs provides a shorthand for the       *)
(* inductive term (or the first dependent parameter, in the dependent      *)
(* case). It therefore introduces a new variable, reusing the name of the  *)
(* term if it was a cleared variable, or otherwise using a default name    *)
(* (the latter case should not appear in final scripts, but could be       *)
(* useful for debugging).                                                  *)

Tactic Definition UnprotectHyprecs :=
  Repeat (Pattern 2 protect_ctx; Unfold 1 protect_ctx).

Lemma make_elim_eq : (A : Set; x : A) {y : A | y = x}.
Proof. By Move=> A x; Exists x. Qed.

Tactic Definition ElimTop :=
  Intros defective_term; Elim defective_term; Clear defective_term.

Tactic Definition ElimTopUsing ind :=
  Intros defective_term; Elim defective_term using ind; Clear defective_term.

Grammar tactic elim_view : tactic :=
  elim_view ["/" constrarg($u)] -> [$u].

Grammar tactic simple_tactic : ast :=
  elim_view_gens
    ["Elim" elim_view($view) ":" ext_gen($gt) ext_dgens($eg)
      ext_case_opt_intros($ds)] ->
  let (GT $pat ($LIST $ids2)) = [$gt] in
  let (EG (T ($LIST $t1o)) $gen ($LIST $ids1)) = [$eg] in
  let (D (S ($LIST $t5o)) ($LIST $t78o)) = [$ds] in
  let (T ($LIST $t58o)) = case [(CLAUSE ($LIST $ids1) ($LIST $ids2))] of
    (CLAUSE) -> [(T ($LIST $t5o) ($LIST $t78o))]
  | $clause -> [(T ($LIST $t5o) (Clear $clause) ($LIST $t78o))]
  esac in
  case [$gen] of
    (G ($LIST $g)) ->
    let (T ($LIST $t2o)) = case [(Generalize ($LIST $g))] of
      (Generalize) -> [(T)] | $t2 -> [(T $t2)] esac in
    let (T ($LIST $t34o)) = case [$pat] of
      (PATTERN $term) ->
      [(T (Elim $term (BINDINGS) $view (BINDINGS)))]
    | (PATTERN $term ($LIST $_)) -> 
      [(T (Reduce (REDEXP (Pattern $pat)) (CLAUSE))
          (Elim $term (BINDINGS) $view (BINDINGS)))]
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
    let $t3a =
      [(Reduce (REDEXP (Pattern $pat ($LIST $pats) $bpat)) (CLAUSE))] in
    let $t4a =
      let (PATTERN $bterm ($LIST $_)) = [$bpat] in
      [(Elim $bterm (BINDINGS) $view (BINDINGS))] in
    case [(T ($LIST $t1o) $t3a $t4a ($LIST $t58o))] of
      (T $t1 $t2)                 -> [<:tactic:<$t1; $t2>>]
    | (T $t1 $t2 $t3)             -> [<:tactic:<$t1; $t2; $t3>>]
    | (T $t1 $t2 $t3 $t4)         -> [<:tactic:<$t1; $t2; $t3; $t4>>]
    | (T $t1 $t2 $t3 $t4 $t5)     -> [<:tactic:<$t1; $t2; $t3; $t4; $t5>>]
    | (T $t1 $t2 $t3 $t4 $t5 $t6) -> [<:tactic:<$t1; $t2; $t3; $t4; $t5; $t6>>]
    | (T $t1 $t2 $t3 $t4 $t5 $t6 $t7) ->
                                  [<:tactic:<$t1; $t2; $t3; $t4; $t5; $t6; $t7>>]
    esac
  esac
| elim_view_eq_gens
    ["Elim" elim_view($view) identarg($eqname) ":" ext_gen($gt) ext_dgens($eg)
     ext_case_opt_intros($ds)] ->
  let (GT $pat1 ($LIST $ids2)) = [$gt] in
  let (EG (T ($LIST $t1o)) $gen ($LIST $ids1)) = [$eg] in
  let (D (S ($LIST $t4o)) $t6a ($LIST $t8o)) = case [$ds] of
    (D $s) -> [(D $s (Intros))]
  | (D $s (Intros)) -> [(D $s (Intros) (Intros))]
  | $_ -> [$ds]
  esac in
  let (T ($LIST $t45o)) = case [(CLAUSE ($LIST $ids1) ($LIST $ids2))] of
    (CLAUSE) -> [(T ($LIST $t4o))]
  | $clause -> [(T ($LIST $t4o) (Clear $clause))]
  esac in
  let (PATTERN $base1 ($LIST $_)) = [$pat1] in
  let $varname = case [(C ($LIST $ids2))] of
    (C (INHYP $id) ($LIST $_)) -> [$id]
  | $_ -> [elim_term]
  esac in
  let (PIT $base $epat (P ($LIST $ise)) ($LIST $t2o)) = case [$gen] of
    (G) ->
    [(PIT $base1 (Pattern $pat1) (P))]
  | (G ($LIST $g)) ->  
    [(PIT $base1 (Pattern $pat1) (P) (Generalize ($LIST $g)))]
  | (D (P ($LIST $pats)) $bpat ($LIST $ise)) ->
    let (PATTERN $bterm ($LIST $_)) = [$bpat] in
    [(PIT $bterm (Pattern $pat1 ($LIST $pats) $bpat) (P ($LIST $ise)))]
  esac in
  let $t3a = 
    let $t3a1 = [(Reduce (REDEXP $epat) (CLAUSE))] in
    let $pat3 = [(APPLIST (META 1) (ISEVAR) ($LIST $ise))] in
    let $t3a2 = [<:tactic:<Replace ?1 with (protect_ctx ?1); RightDone>>] in
    let $t3a12 = [<:tactic:<$t3a1; Match Context With [|- $pat3] -> $t3a2>>] in
    let $t3a3 = [(Elim $base (BINDINGS) $view (BINDINGS))] in
    [<:tactic:<$t3a12; $t3a3; UnprotectHyprecs>>] in
  let $t7a =
    let $pat7 = [(APPLIST (QUALID protect_ctx) (ISEVAR) (META 1) ($LIST $ise))] in
    let $t7a1 = [<:tactic:<Move: (make_elim_eq ?1) => [$varname $eqname]>>] in
    [<:tactic:<Match Context With [|- $pat7] -> $t7a1; Unfold protect_ctx>>] in
  case [(T ($LIST $t1o) ($LIST $t2o) $t3a ($LIST $t45o) $t6a $t7a ($LIST $t8o))]
  of
    (T $t1 $t2 $t3)                -> [<:tactic:<$t1; $t2; $t3>>]
  | (T $t1 $t2 $t3 $t4)            -> [<:tactic:<$t1; $t2; $t3; $t4>>]
  | (T $t1 $t2 $t3 $t4 $t5)        -> [<:tactic:<$t1; $t2; $t3; $t4; $t5>>]
  | (T $t1 $t2 $t3 $t4 $t5 $t6)    -> [<:tactic:<$t1; $t2; $t3; $t4; $t5; $t6>>]
  | (T $t1 $t2 $t3 $t4 $t5 $t6 $t7) ->
                                 [<:tactic:<$t1; $t2; $t3; $t4; $t5; $t6; $t7>>]
  | (T $t1 $t2 $t3 $t4 $t5 $t6 $t7 $t8) ->
                            [<:tactic:<$t1; $t2; $t3; $t4; $t5; $t6; $t7; $t8>>]
  esac
| elim_noview_gens
    ["Elim" ":" ext_gen($gt) ext_dgens($eg)
      ext_case_opt_intros($ds)] ->
  let (GT $pat ($LIST $ids2)) = [$gt] in
  let (EG (T ($LIST $t1o)) $gen ($LIST $ids1)) = [$eg] in
  let (D (S ($LIST $t5o)) ($LIST $t78o)) = [$ds] in
  let (T ($LIST $t58o)) = case [(CLAUSE ($LIST $ids1) ($LIST $ids2))] of
    (CLAUSE) -> [(T ($LIST $t5o) ($LIST $t78o))]
  | $clause -> [(T ($LIST $t5o) (Clear $clause) ($LIST $t78o))]
  esac in
  case [$gen] of
    (G ($LIST $g)) ->
    let (T ($LIST $t2o)) = case [(Generalize ($LIST $g))] of
      (Generalize) -> [(T)] | $t2 -> [(T $t2)] esac in
    let (T ($LIST $t34o)) = case [$pat] of
      (PATTERN $term) ->
      [(T (Elim $term (BINDINGS)))]
    | (PATTERN $term ($LIST $_)) -> 
      [(T (Reduce (REDEXP (Pattern $pat)) (CLAUSE))
          (Elim $term (BINDINGS)))]
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
    let $t3a =
      [(Reduce (REDEXP (Pattern $pat ($LIST $pats) $bpat)) (CLAUSE))] in
    let $t4a =
      let (PATTERN $bterm ($LIST $_)) = [$bpat] in
      [(Elim $bterm (BINDINGS))] in
    case [(T ($LIST $t1o) $t3a $t4a ($LIST $t58o))] of
      (T $t1 $t2)                 -> [<:tactic:<$t1; $t2>>]
    | (T $t1 $t2 $t3)             -> [<:tactic:<$t1; $t2; $t3>>]
    | (T $t1 $t2 $t3 $t4)         -> [<:tactic:<$t1; $t2; $t3; $t4>>]
    | (T $t1 $t2 $t3 $t4 $t5)     -> [<:tactic:<$t1; $t2; $t3; $t4; $t5>>]
    | (T $t1 $t2 $t3 $t4 $t5 $t6) -> [<:tactic:<$t1; $t2; $t3; $t4; $t5; $t6>>]
    | (T $t1 $t2 $t3 $t4 $t5 $t6 $t7) ->
                                  [<:tactic:<$t1; $t2; $t3; $t4; $t5; $t6; $t7>>]
    esac
  esac
| elim_noview_eq_gens
    ["Elim" constrarg_binding_list($eqnamel) ":" ext_gen($gt) ext_dgens($eg)
     ext_case_opt_intros($ds)] ->
  let (B (COMMAND (QUALID $eqname)) (BINDINGS)) = [(B ($LIST $eqnamel))] in
  let (GT $pat1 ($LIST $ids2)) = [$gt] in
  let (EG (T ($LIST $t1o)) $gen ($LIST $ids1)) = [$eg] in
  let (D (S ($LIST $t4o)) $t6a ($LIST $t8o)) = case [$ds] of
    (D $s) -> [(D $s (Intros))]
  | (D $s (Intros)) -> [(D $s (Intros) (Intros))]
  | $_ -> [$ds]
  esac in
  let (T ($LIST $t45o)) = case [(CLAUSE ($LIST $ids1) ($LIST $ids2))] of
    (CLAUSE) -> [(T ($LIST $t4o))]
  | $clause -> [(T ($LIST $t4o) (Clear $clause))]
  esac in
  let (PATTERN $base1 ($LIST $_)) = [$pat1] in
  let $varname = case [(C ($LIST $ids2))] of
    (C (INHYP $id) ($LIST $_)) -> [$id]
  | $_ -> [elim_term]
  esac in
  let (PIT $base $epat (P ($LIST $ise)) ($LIST $t2o)) = case [$gen] of
    (G) ->
    [(PIT $base1 (Pattern $pat1) (P))]
  | (G ($LIST $g)) ->  
    [(PIT $base1 (Pattern $pat1) (P) (Generalize ($LIST $g)))]
  | (D (P ($LIST $pats)) $bpat ($LIST $ise)) ->
    let (PATTERN $bterm ($LIST $_)) = [$bpat] in
    [(PIT $bterm (Pattern $pat1 ($LIST $pats) $bpat) (P ($LIST $ise)))]
  esac in
  let $t3a = 
    let $t3a1 = [(Reduce (REDEXP $epat) (CLAUSE))] in
    let $pat3 = [(APPLIST (META 1) (ISEVAR) ($LIST $ise))] in
    let $t3a2 = [<:tactic:<Replace ?1 with (protect_ctx ?1); RightDone>>] in
    let $t3a12 = [<:tactic:<$t3a1; Match Context With [|- $pat3] -> $t3a2>>] in
    let $t3a3 = [(Elim $base (BINDINGS))] in
    [<:tactic:<$t3a12; $t3a3; UnprotectHyprecs>>] in
  let $t7a =
    let $pat7 = [(APPLIST (QUALID protect_ctx) (ISEVAR) (META 1) ($LIST $ise))] in
    let $t7a1 = [<:tactic:<Move: (make_elim_eq ?1) => [$varname $eqname]>>] in
    [<:tactic:<Match Context With [|- $pat7] -> $t7a1; Unfold protect_ctx>>] in
  case [(T ($LIST $t1o) ($LIST $t2o) $t3a ($LIST $t45o) $t6a $t7a ($LIST $t8o))]
  of
    (T $t1 $t2 $t3)                -> [<:tactic:<$t1; $t2; $t3>>]
  | (T $t1 $t2 $t3 $t4)            -> [<:tactic:<$t1; $t2; $t3; $t4>>]
  | (T $t1 $t2 $t3 $t4 $t5)        -> [<:tactic:<$t1; $t2; $t3; $t4; $t5>>]
  | (T $t1 $t2 $t3 $t4 $t5 $t6)    -> [<:tactic:<$t1; $t2; $t3; $t4; $t5; $t6>>]
  | (T $t1 $t2 $t3 $t4 $t5 $t6 $t7) ->
                                 [<:tactic:<$t1; $t2; $t3; $t4; $t5; $t6; $t7>>]
  | (T $t1 $t2 $t3 $t4 $t5 $t6 $t7 $t8) ->
                            [<:tactic:<$t1; $t2; $t3; $t4; $t5; $t6; $t7; $t8>>]
  esac
| elim_view_clear_intros
    ["Elim" elim_view($view) "{" clear_list_tac($t3a) "}"
      ext_case_opt_intros($ds)] ->
  let (D (S ($LIST $t2o)) ($LIST $t45o)) = [$ds] in
  case [(T <:tactic:<ElimTopUsing $view>> ($LIST $t2o) $t3a ($LIST $t45o))] of
    (T $t1 $t2)                 -> [<:tactic:<$t1; $t2>>]
  | (T $t1 $t2 $t3)             -> [<:tactic:<$t1; $t2; $t3>>]
  | (T $t1 $t2 $t3 $t4)         -> [<:tactic:<$t1; $t2; $t3; $t4>>]
  | (T $t1 $t2 $t3 $t4 $t5)     -> [<:tactic:<$t1; $t2; $t3; $t4; $t5>>]
  esac 
| elim_view_intros
    ["Elim" elim_view($view) ext_case_opt_intros($ds)] ->
  let (D (S ($LIST $t2o)) ($LIST $t34o)) = [$ds] in
  case [(T <:tactic:<ElimTopUsing $view>> ($LIST $t2o) ($LIST $t34o))] of
    (T $t1 $t2)                 -> [<:tactic:<$t1; $t2>>]
  | (T $t1 $t2 $t3)             -> [<:tactic:<$t1; $t2; $t3>>]
  | (T $t1 $t2 $t3 $t4)         -> [<:tactic:<$t1; $t2; $t3; $t4>>]
  esac 
| elim_noview_clear_intros
    ["Elim" "{" clear_list_tac($t3a) "}" ext_case_opt_intros($ds)] ->
  let (D (S ($LIST $t2o)) ($LIST $t45o)) = [$ds] in
  case [(T <:tactic:<ElimTop>> ($LIST $t2o) $t3a ($LIST $t45o))] of
    (T $t1 $t2)                 -> [<:tactic:<$t1; $t2>>]
  | (T $t1 $t2 $t3)             -> [<:tactic:<$t1; $t2; $t3>>]
  | (T $t1 $t2 $t3 $t4)         -> [<:tactic:<$t1; $t2; $t3; $t4>>]
  | (T $t1 $t2 $t3 $t4 $t5)     -> [<:tactic:<$t1; $t2; $t3; $t4; $t5>>]
  esac 
| elim_noview_intros
    ["Elim" "=>" ext_case_intros($ds)] ->
  let (D (S ($LIST $t2o)) ($LIST $t34o)) = [$ds] in
  case [(T <:tactic:<ElimTop>> ($LIST $t2o) ($LIST $t34o))] of
    (T $t1 $t2)                 -> [<:tactic:<$t1; $t2>>]
  | (T $t1 $t2 $t3)             -> [<:tactic:<$t1; $t2; $t3>>]
  | (T $t1 $t2 $t3 $t4)         -> [<:tactic:<$t1; $t2; $t3; $t4>>]
  esac 
| naked_elim
    ["Elim"] ->
  [<:tactic:<ElimTop>>].

(* The extended Apply is really a variant of Refine that allows initial    *)
(* generalizations, a subsequent list of intros and clears, and tries to   *)
(* guess the number of missing assumptions (up to 5).                      *)
(* Syntax:                                                                 *)
(*   'Apply' ':' <term> <gen>* [<clear>] ['=>' <intros>]                   *)
(*   'Apply' <view> [<view>] ['=>' <intros>]                               *)
(* The ":" form tries to add 0 to 5 wildcards to the term to match the     *)
(* goal; the single-<view> tries to interpose one of the six boolean       *)
(* reflection introduction lemmas; the double-<view> form attempts to      *)
(* to reduce the equality of two boolean expressions to the equivalence of *)
(* some properties they reflect. The latter two forms will be dealt with   *)
(* in boolprop.v.                                                          *)
(*   As with Case and Elim, the <intros> part should always start with a   *)
(* disjunctive pattern, with as many branches as there are goals generated *)
(* by the Apply; the rest of the intros (if present) is common to all the  *)
(* branches.                                                               *)
(*   We also define a congruence helper tactic, "Congr". Syntax:           *)
(*     Congr <term>                                                        *)
(* It attempt to refine the goal by a congruence over <term>, adding up to *)
(* 4 arguments on the left, one on the right, and binary congruence as a   *)
(* last resort. It's a grammar rule, so that <term> may contain wildcards. *)

Grammar tactic ext_apply_tac : tactic :=
  make_ext_apply_tac [command:command($lemma)] ->
  [First [
    Refine $lemma
  | Refine ($lemma ?)
  | Refine ($lemma ? ?)
  | Refine ($lemma ? ? ?)
  | Refine ($lemma ? ? ? ?)
  | Refine ($lemma ? ? ? ? ?)]].

Grammar tactic simple_tactic : ast :=
  ext_apply ["Apply" ":" ext_apply_tac($t3a) ext_gens($eg)
                   ext_case_opt_intros($ds)] ->
  let (EG (T ($LIST $t1o)) (G ($LIST $g)) ($LIST $ids1)) = [$eg] in
  let (T ($LIST $t2o)) = case [(Generalize ($LIST $g))] of
    (Generalize) -> [(T)]
  | $t2 -> [(T $t2)]
  esac in
  let (D (S ($LIST $t4o)) ($LIST $t67o)) = [$ds] in
  let (T ($LIST $t45o)) = case [(CLAUSE ($LIST $ids1))] of
    (CLAUSE) -> [(T ($LIST $t4o))]
  | $clause -> [(T ($LIST $t4o) (Clear $clause))]
  esac in
  case [(T ($LIST $t1o) ($LIST $t2o) $t3a ($LIST $t45o) ($LIST $t67o))] of
    (T $t1)                     -> [$t1]
  | (T $t1 $t2)                 -> [<:tactic:<$t1; $t2>>]
  | (T $t1 $t2 $t3)             -> [<:tactic:<$t1; $t2; $t3>>]
  | (T $t1 $t2 $t3 $t4)         -> [<:tactic:<$t1; $t2; $t3; $t4>>]
  | (T $t1 $t2 $t3 $t4 $t5)     -> [<:tactic:<$t1; $t2; $t3; $t4; $t5>>]
  | (T $t1 $t2 $t3 $t4 $t5 $t6) -> [<:tactic:<$t1; $t2; $t3; $t4; $t5; $t6>>]
  | (T $t1 $t2 $t3 $t4 $t5 $t6 $t7) ->
                              [<:tactic:<$t1; $t2; $t3; $t4; $t5; $t6; $t7>>]
  esac.

Grammar tactic simple_tactic : tactic :=
  congr_tactic ["Congr" command:command($fun)] ->
  [First [ Refine (congr $fun ?)
         | Refine (congr ($fun ?) ?)
         | Refine (congr [congr_var]($fun congr_var ?) ?)
         | Refine (congr ($fun ? ?) ?)
         | Refine (congr ($fun ? ? ?) ?)
         | Refine (congr ($fun ? ? ? ?) ?)
         | Refine (congr2 $fun ? ?)]].

(* Similar extensions for Injection. Syntax:                               *)
(*   'Injection' [':' [<clear>] <term> <gen>*] [<clear>] ['=>' <intros>]   *)
(* There's no support for equations or term selection, as this would not   *)
(* make sense; however the defective case is supported, as is Injection on *)
(* a non-variable. We don't define the naked Injection, however, because   *)
(* this would override the core grammar.                                   *)

Tactic Definition InjectionTop :=
  Intros defective_premise; Injection defective_premise; Clear defective_premise.

Grammar tactic opt_clear : ast list :=
  some_clear ["{" clear_list($ids) "}"] -> [($LIST $ids)]
| no_clear [ ] -> [ ].

Grammar tactic simple_tactic : ast :=
  injection_clear_var
    ["Injection" ":" opt_clear($ids2) identarg($var) ext_gens($eg)
      ext_simpl_intros_opt_tacs($si)] ->
  let (EG (T ($LIST $t1o)) (G ($LIST $g)) ($LIST $ids1)) = [$eg] in
  let (T ($LIST $t2o)) = case [(Generalize ($LIST $g))] of
    (Generalize) -> [(T)] | $t2 -> [(T $t2)] esac in
  let $t3a = [<:tactic:<Injection $var>>] in
  let $t5a = [(Clear (CLAUSE ($LIST $ids1) (INHYP $var) ($LIST $ids2)))] in
  let (I (S ($LIST $t4o)) ($LIST $t6o)) = [$si] in
  case [(T ($LIST $t1o) ($LIST $t2o) $t3a ($LIST $t4o) $t5a ($LIST $t6o))] of
    (T $t1 $t2 $t3 $t4 $t5 $t6) -> [<:tactic:<$t1; $t2; $t3; $t4; $t5; $t6>>]
  | (T $t1 $t2 $t3 $t4 $t5) -> [<:tactic:<$t1; $t2; $t3; $t4; $t5>>]
  | (T $t1 $t2 $t3 $t4)     -> [<:tactic:<$t1; $t2; $t3; $t4>>]
  | (T $t1 $t2 $t3)         -> [<:tactic:<$t1; $t2; $t3>>]
  | (T $t1 $t2)             -> [<:tactic:<$t1; $t2>>]
  esac
| injection_term
    ["Injection" ":" opt_clear($ids2) constrarg($term) ext_gens($eg)
      ext_simpl_intros_opt_tacs($si)] ->
  let (EG (T ($LIST $t1o)) (G ($LIST $g)) ($LIST $ids1)) = [$eg] in
  let $t2a = [(Generalize $term ($LIST $g))] in
  let $t3a = [<:tactic:<InjectionTop>>] in
  let (I (S ($LIST $t4o)) ($LIST $t6o)) = [$si] in
  let (T ($LIST $t5o)) = case [(CLAUSE ($LIST $ids1) ($LIST $ids2))] of
    (CLAUSE) -> [(T)] | $clause -> [(T (Clear $clause))]
  esac in 
  case [(T ($LIST $t1o) $t2a $t3a ($LIST $t4o) ($LIST $t5o) ($LIST $t6o))] of
    (T $t1 $t2 $t3 $t4 $t5 $t6) -> [<:tactic:<$t1; $t2; $t3; $t4; $t5; $t6>>]
  | (T $t1 $t2 $t3 $t4 $t5) -> [<:tactic:<$t1; $t2; $t3; $t4; $t5>>]
  | (T $t1 $t2 $t3 $t4)     -> [<:tactic:<$t1; $t2; $t3; $t4>>]
  | (T $t1 $t2 $t3)         -> [<:tactic:<$t1; $t2; $t3>>]
  | (T $t1 $t2)             -> [<:tactic:<$t1; $t2>>]
  esac
| injection_clear_top
    ["Injection" "{" clear_list_tac($t3a) "}" ext_simpl_intros_opt_tacs($si)] ->
  let (I (S ($LIST $t2o)) ($LIST $t4o)) = [$si] in
  case [(T <:tactic:<InjectionTop>> ($LIST $t2o) $t3a ($LIST $t4o))] of
    (T $t1 $t2 $t3 $t4)     -> [<:tactic:<$t1; $t2; $t3; $t4>>]
  | (T $t1 $t2 $t3)         -> [<:tactic:<$t1; $t2; $t3>>]
  | (T $t1 $t2)             -> [<:tactic:<$t1; $t2>>]
  esac
| injection_top_intros
    ["Injection" "=>" ext_simpl_intros_tacs($si)] ->
  let (I (S ($LIST $t2o)) ($LIST $t3o)) = [$si] in
  case [(T <:tactic:<InjectionTop>> ($LIST $t2o) ($LIST $t3o))] of
    (T $t1 $t2 $t3)         -> [<:tactic:<$t1; $t2; $t3>>]
  | (T $t1 $t2)             -> [<:tactic:<$t1; $t2>>]
  | (T $t1)                 -> [<:tactic:<$t1>>]
  esac.

(* The Rewrite: tactic performs a sequence of Rewrite, Simpl, Unfold, and  *)
(* Fold tactics, along with relevant Pattern and Clear tactics.            *)
(* Syntax :                                                                *)
(*  'Rewrite:' <rwstep>+ ['~' <clear>] ['in' <ident>+ ['*']]               *)
(* where  <rwstep> ::= [<mult>] <rewrite> | <rwsimpl> | <unfold> | <fold>  *)
(*   and <rewrite> ::= '~' <ident> | '~' <clear> <term> | [<rwocc>] <term> *)
(*   and    <mult> ::= '-' | ['-' | <integer>] ('!' | '?')                 *)
(*   and   <rwocc> ::= '{' <integer>* <term> '}'                           *)
(*   and <rwsimpl> ::= ['~' <clear>] <simpl>                               *)
(*   and  <unfold> ::= ['~' | '{ <integer>+ '}' ] '/' <ident>              *)
(*   and    <fold> ::= '-' [<rwocc>] '/' <term>                            *)
(* The optional <mult> before a <rewrite> specifies both the orientation   *)
(* and the repetition of the rule. If it consists of or starts with a '-'  *)
(* sign (including, if the <integer> is negative) then the <term> equation *)
(* is used right to left. The <integer>, if present, specifies how many    *)
(* times the rewrite should be done; if it is followed by '!' then this    *)
(* count is exact; with '?', the rewrites are only Try'ed. A '?' without a *)
(* count means "as many times as possible" while '!' means "at least once, *)
(* and as many times as possible".                                         *)
(*   Much as for the other extended tactics above, one can select specific *)
(* occurrences for rewriting, or delete variables or assumptions that      *)
(* become irrelevant after a rewrite. There are two differences, however:  *)
(* one must specify the exact term to rewrite, when specifying occurrences *)
(* (this is due to limitations of the underlying core tactics, but is at   *)
(* time a convenient way of specifying the parameters of the rule); and,   *)
(* as clears are less common in rewrites, and to avoid confusion with the  *)
(* <rwocc> construct, the <clear> construct is always preceded by a '~'.   *)
(* If the <term> is a variable, it will only be deleted if the '~' is      *)
(* specified; in that case the <clear> can be omitted. Thus Rewrite: ~Dx   *)
(* rewrites and then deletes Dx, while Rewrite: ~{x}Dx rewrites Dx and     *)
(* then deletes both Dx and x (in that order).                             *)
(*   The <rwsimpl> term construct is similar to the <simpl> construct in   *)
(* <intro>, but with a leading '~' before the <clear>.                     *)
(*   The <fold> and <unfold> constructs offer similar interfaces to the    *)
(* primitive Fold and Unfold tactics (however the <clear> construct is not *)
(* supported because it is not useful with these commands). In <unfold>,   *)
(* a '~' specifies that the unfolded constant is deleted, and one does not *)
(* repeat the constant name to be unfolded when specifying occurrences;    *)
(* unlike the primitive Unfold, this extended unfold supports negative     *)
(*  occurrences. In <fold>, one must specify the term to be folded when    *)
(* specifying occurrences; this form actually uses the Change tactic       *)
(* rather than the Fold tactic, so it is more reliable than a plain Fold   *)
(* (it will succeed whenever the two terms are convertible; however, it    *)
(* does perform beta simplification).                                      *)
(*   The non-empty sequence of rewrite steps may be followed by a final    *)
(* '~'-flagged <clear>, and the name of assumptions to which the sequence  *)
(* sequence of steps should apply (by default, steps apply to the goal).   *)
(* This works by temporarily moving assumptions to the goal, hence steps   *)
(* may be used to help resolve rule conditions; however the assumptions    *)
(* will appear unmodified in the context of condiiton subgoals. Beware     *)
(* also that the Rewrite cannot be used on definitions generates by Pose   *)
(* (only Simpl wiil work on these). The optional "*" at the end indicates  *)
(* that the steps should also apply to the goal; this is especially useful *)
(* for rewriting in dependent assumptions.                                 *)
(*   A final trick: it is possible to select the redex occurrence without  *)
(* writing down the entire redex in the script by using the lock rule to   *)
(* remove potential redexes, e.g., Rewrite: {-3 plus}lock plus_sym -!lock  *)
(* will commute the third sum in the current goal (the final "-!lock" can  *)
(* often be factored across multiple rewrites).                            *)

Tactic Definition SwapPattern :=
  Match Context With [|- (?1 ?2)] -> Change ([x; P](P x) ?2 ?1).

Tactic Definition FoldPattern term :=
  Match Context With [|- (?1 ?2)] -> Change (?1 term); Lazy Beta.

Tactic Definition HideGoal :=
  Match Context With [|- ?1] -> Pose GoalMarker := ?1.

Tactic Definition MarkGoal :=
  (Match Context With [|- ?1] -> Change (protect_ctx ?1));
  Pose GoalMarker := protect_ctx; Unfold protect_ctx in GoalMarker;
  Simpl in GoalMarker.

(* We need to reintoduce the assumptions only in the main branch.         *)

Tactic Definition RevealGoal ctac :=
  First [Clear GoalMarker | ctac; Intros; Unfold GoalMarker; Clear GoalMarker].
 
Tactic Definition DoMany tac := tac; Repeat tac.

Grammar tactic rwocc : ast :=
  mrewrite_clear_deps ["{" opt_ext_occ($occ) constrarg_noexp($term) "}"] ->
  [(Reduce (REDEXP (Pattern (PATTERN $term ($LIST $occ)))) (CLAUSE))].

Grammar tactic ext_rwrule : ast :=
  ext_clear_var_rule ["~" "{" clear_list($ids) "}" identarg($rname)] ->
  [(RWC (P) (COMMAND (QUALID $rname)) (INHYP $rname) ($LIST $ids))]
| ext_clear_term_rule ["~" "{" clear_list($ids) "}" constrarg($rule)] ->
  [(RWC (P) $rule ($LIST $ids))]
| ext_cvar_rule ["~" identarg($rname)] ->
  [(RWC (P) (COMMAND (QUALID $rname)) (INHYP $rname))]
| ext_rwocc_rule [ rwocc($pat) constrarg_noexp($rule)] ->
  [(RWC (P $pat) $rule)]
| ext_rw_rule [constrarg_noexp($rule)] ->
  [(RWC (P) $rule)].

Grammar tactic ext_rewrite_mult : ast :=
  times_rule [prim:number($n) "!"] -> [(TIMES $n)]
| atmost_times_rule [prim:number($n) "?"] -> [(ATMOST $n)]
| many_times_rule ["!"] -> [(MANY)]
| maybe_rule ["?"] -> [(SOME)].

Grammar tactic ext_rewrite_no_tilde : ast :=
  ext_rewrite_mult_pos_no_tilde [ ext_rewrite_mult($m) ext_rwrule($r) ] ->
    let (RWC $pat $rule ($LIST $clr)) = [$r] in
    let $t2 = [(RewriteLR $rule (BINDINGS))] in
    let $t12 = case [$pat] of
      (P $t1) -> [<:tactic:<$t1; $t2>>]
    | (P) -> [$t2]
    esac in
    let $t = case [$m] of
      (MANY) -> [<:tactic:<DoMany ($t12)>>]
    | (SOME) -> [<:tactic:<Repeat $t12>>]
    | (TIMES $n) -> [(DO $n $t12)]
    | (ATMOST $n) -> [(DO $n <:tactic:<Try $t12>>)]
    esac in [(XRW $t ($LIST $clr))]
| ext_rewrite_rl_mult_no_tilde ["-" ext_rewrite_mult($m) ext_rwrule($r) ] ->
    let (RWC $pat $rule ($LIST $clr)) = [$r] in
    let $t2 = [(RewriteRL $rule (BINDINGS))] in
    let $t12 = case [$pat] of
      (P $t1) -> [<:tactic:<$t1; $t2>>]
    | (P) -> [$t2]
    esac in
    let $t = case [$m] of
      (MANY) -> [<:tactic:<DoMany ($t12)>>]
    | (SOME) -> [<:tactic:<Repeat $t12>>]
    | (TIMES $n) -> [(DO $n $t12)]
    | (ATMOST $n) -> [(DO $n <:tactic:<Try $t12>>)]
    esac in [(XRW $t ($LIST $clr))]
| ext_fold_occ_no_tilde ["-" rwocc($t1) "/" constrarg_noexp($term)] ->
  [(XRW <:tactic:<$t1; FoldPattern $term>>)]
| ext_rewrite_rl_occ_no_tilde ["-" rwocc($t1) constrarg_noexp($rule)] ->
  [(XRW (TACTICLIST $t1 (RewriteRL $rule (BINDINGS))))]
| ext_rewrite_rl_no_tilde ["-" ext_rwrule($r)] ->
  let (RWC (P) $rule ($LIST $clr)) = [$r] in
  [(XRW (RewriteRL $rule (BINDINGS)) ($LIST $clr))]
| ext_unfold_no_tilde ["-" "/" constrarg_noexp($term)] ->
  [(XRW (Reduce (REDEXP (Fold $term)) (CLAUSE)))]
| ext_simpl_no_tilde ["/" simpl_tac($t)] ->
  [(XRW $t)]
| ext_unfold_no_tilde ["/" identarg($id)] ->
  [(XRW (Reduce (REDEXP (Unfold (UNFOLD (QUALIDARG $id)))) (CLAUSE)))]
| ext_unfold_occ_no_tilde ["{" ext_occ($occ) "}" "/" identarg($id)] ->
  let $qid = [(QUALIDARG $id)] in
  let $t1 = [(Reduce (REDEXP (Unfold (UNFOLD $qid ($LIST $occ)))) (CLAUSE))] in
  let $p2 = [(PATTERN (COMMAND (QUALID $id)) ($LIST $occ))] in
  let $t2 = [(Reduce (REDEXP (Pattern $p2)) (CLAUSE))] in
  let $t3 = [(Reduce (REDEXP (Unfold (UNFOLD $qid 1))) (CLAUSE))] in
  [(XRW <:tactic:<First[$t1 | $t2; SwapPattern; $t3]>>)]
| ext_rewrite_occ_no_tilde
    ["{" ext_occ($occ) constrarg_noexp($term)"}" constrarg_noexp($rule)] ->
  let $t1 = [(Reduce (REDEXP (Pattern (PATTERN $term ($LIST $occ)))) (CLAUSE))] in
  let $t2 = [(RewriteLR $rule (BINDINGS))] in
  [(XRW <:tactic:<$t1; $t2>>)]
| ext_rewrite_term_no_tilde
    ["{" constrarg_noexp($term) "}" constrarg_noexp($rule)] ->
  let $t1 = [(Reduce (REDEXP (Pattern (PATTERN $term))) (CLAUSE))] in
  let $t2 = [(RewriteLR $rule (BINDINGS))] in
  [(XRW <:tactic:<$t1; $t2>>)]
| ext_rewrite_rule_no_tilde [constrarg_noexp($rule)] ->
  [(XRW (RewriteLR $rule (BINDINGS)))].

Grammar tactic ext_rewrite_tilde_no_clear : ast :=
  ext_rewrite_tilde_var_no_clear [identarg($id)] ->
  [(XRW (RewriteLR (COMMAND (QUALID $id)) (BINDINGS)) (INHYP $id))]
| ext_unfold_tilde_no_clear ["/" identarg($id)] ->
  [(XRW (Reduce (REDEXP (Unfold (UNFOLD (QUALIDARG $id)))) (CLAUSE)) (INHYP $id))].

Grammar tactic ext_rewrite_after_clear : ast :=
  ext_rewrite_var_after_clear [identarg($id)] ->
  [(XRW (RewriteLR (COMMAND (QUALID $id)) (BINDINGS)) (INHYP $id))]
| ext_rewrite_rule_after_clear [constrarg($rule)] ->
  [(XRW (RewriteLR $rule (BINDINGS)))]
| ext_simpl_after_clear ["/" simpl_tac($t)] ->
  [(XRW $t)].

Grammar tactic ext_rewrite_location : ast :=
  cons_ext_rewrite_location [identarg($id) ext_rewrite_location($loc)] ->
  let (XLOC $t0 (G ($LIST $g)) ($LIST $ids)) = [$loc] in
  [(XLOC $t0 (G (COMMAND (QUALID $id)) ($LIST $g)) ($LIST $ids) (INHYP $id))]
| last_ext_rewrite_location_mark [identarg($id) "*"] ->
  [(XLOC <:tactic:<MarkGoal>> (G (COMMAND (QUALID $id))) (INHYP $id))]
| last_ext_rewrite_location_hide [identarg($id)] ->
  [(XLOC <:tactic:<HideGoal>> (G (COMMAND (QUALID $id))) (INHYP $id))].

Grammar tactic ext_rewrite_tail : ast :=
  ext_rewrite_tail_chop [ext_rewrite_tail_long($mrw)] -> case [$mrw] of
    (MRW $loc $clr $t0 $t1 $t2 $t3 $t4 $t5 $t6 $t7 $t8 $t9 ($LIST $tacs)) ->
      let $tac =
        [<:tactic:<$t9; $t8; $t7; $t6; $t5; $t4; $t3; $t2; $t1; $t0>>]
      in [(MRW $loc $clr $tac ($LIST $tacs))]
  | $_ -> [$mrw]
  esac
with ext_rewrite_tail_long : ast :=
  ext_rewrite_tail_in_hyps ["in" ext_rewrite_location($loc)] ->
  [(MRW $loc (C))]
| ext_rewrite_tail_no_tilde [ext_rewrite_no_tilde($xrw) ext_rewrite_tail($mrw)] ->
  let (XRW $t1 ($LIST $ids1)) = [$xrw] in
  let (MRW $loc (C ($LIST $ids2)) ($LIST $tacs)) = [$mrw] in
  [(MRW $loc (C ($LIST $ids1) ($LIST $ids2)) ($LIST $tacs) $t1)]
| ext_rewrite_tail_tilde_no_clear
    ["~" ext_rewrite_tilde_no_clear($xrw) ext_rewrite_tail($mrw)] ->
  let (XRW $t1 ($LIST $ids1)) = [$xrw] in
  let (MRW $loc (C ($LIST $ids2)) ($LIST $tacs)) = [$mrw] in
  [(MRW $loc (C ($LIST $ids1) ($LIST $ids2)) ($LIST $tacs) $t1)]
| ext_rewrite_tail_clear_in_hyps
    ["~" "{" clear_list($ids) "}" "in" ext_rewrite_location($loc)] ->
  [(MRW $loc (C ($LIST $ids)))]
| ext_rewrite_tail_after_clear
    ["~" "{" clear_list($ids2) "}" ext_rewrite_after_clear($xrw)
     ext_rewrite_tail($mrw)] ->
  let (XRW $t1 ($LIST $ids1)) = [$xrw] in
  let (MRW $loc (C ($LIST $ids3)) ($LIST $tacs)) = [$mrw] in
  [(MRW $loc (C ($LIST $ids1) ($LIST $ids2) ($LIST $ids3)) ($LIST $tacs) $t1)]
| ext_rewrite_tail_final_clear ["~" "{" clear_list($ids) "}" ] ->
  [(MRW (XGOAL) (C ($LIST $ids)))]
| ext_rewrite_tail_end [ ] ->
  [(MRW (XGOAL) (C))].

Grammar tactic ext_rewrite_body : ast :=
  make_ext_rewrite_body [ext_rewrite_body_cons($mrw)] ->
  let (MRW $loc (C ($LIST $ids2)) ($LIST $tacs)) = [$mrw] in
  case [$loc] of
    (XLOC $t0 (G ($LIST $g)) ($LIST $ids1)) ->
    let $t1 = [(Generalize ($LIST $g))] in
    let $clr = [(Clear (CLAUSE ($LIST $ids1) ($LIST $ids2)))] in
    [(T <:tactic:<RevealGoal ($clr)>> ($LIST $tacs) <:tactic:<$t0; $t1>>)]
  | (XGOAL) ->
    case [(CLAUSE ($LIST $ids2))] of
      (CLAUSE) -> [(T ($LIST $tacs))]
    | $clause -> [(T (Clear $clause) ($LIST $tacs))]
    esac
  esac
with ext_rewrite_body_cons : ast :=
| ext_rewrite_body_no_tilde [ext_rewrite_no_tilde($xrw) ext_rewrite_tail($mrw)] ->
  let (XRW $t1 ($LIST $ids1)) = [$xrw] in
  let (MRW $loc (C ($LIST $ids2)) ($LIST $tacs)) = [$mrw] in
  [(MRW $loc (C ($LIST $ids1) ($LIST $ids2)) ($LIST $tacs) $t1)]
| ext_rewrite_body_tilde_no_clear
    ["~" ext_rewrite_tilde_no_clear($xrw) ext_rewrite_tail($mrw)] ->
  let (XRW $t1 ($LIST $ids1)) = [$xrw] in
  let (MRW $loc (C ($LIST $ids2)) ($LIST $tacs)) = [$mrw] in
  [(MRW $loc (C ($LIST $ids1) ($LIST $ids2)) ($LIST $tacs) $t1)]
| ext_rewrite_body_after_clear
    ["~" "{" clear_list($ids2) "}" ext_rewrite_after_clear($xrw)
     ext_rewrite_tail($mrw)] ->
  let (XRW $t1 ($LIST $ids1)) = [$xrw] in
  let (MRW $loc (C ($LIST $ids3)) ($LIST $tacs)) = [$mrw] in
  [(MRW $loc (C ($LIST $ids1) ($LIST $ids2) ($LIST $ids3)) ($LIST $tacs) $t1)].

Grammar tactic simple_tactic : ast :=
  make_ext_rewrite ["Rewrite" ":" ext_rewrite_body($tacs)] ->
  case [$tacs] of
    (T $t0 $t1 $t2 $t3 $t4 $t5 $t6 $t7 $t8 $t9 $t10) ->
      [<:tactic:<$t10; $t9; $t8; $t7; $t6; $t5; $t4; $t3; $t2; $t1; $t0>>]
  | (T $t0 $t1 $t2 $t3 $t4 $t5 $t6 $t7 $t8 $t9) ->
      [<:tactic:<$t9; $t8; $t7; $t6; $t5; $t4; $t3; $t2; $t1; $t0>>]
  | (T $t0 $t1 $t2 $t3 $t4 $t5 $t6 $t7 $t8) ->
      [<:tactic:<$t8; $t7; $t6; $t5; $t4; $t3; $t2; $t1; $t0>>]
  | (T $t0 $t1 $t2 $t3 $t4 $t5 $t6 $t7) ->
      [<:tactic:<$t7; $t6; $t5; $t4; $t3; $t2; $t1; $t0>>]
  | (T $t0 $t1 $t2 $t3 $t4 $t5 $t6) ->
      [<:tactic:<$t6; $t5; $t4; $t3; $t2; $t1; $t0>>]
  | (T $t0 $t1 $t2 $t3 $t4 $t5) -> [<:tactic:<$t5; $t4; $t3; $t2; $t1; $t0>>]
  | (T $t0 $t1 $t2 $t3 $t4) -> [<:tactic:<$t4; $t3; $t2; $t1; $t0>>]
  | (T $t0 $t1 $t2 $t3) -> [<:tactic:<$t3; $t2; $t1; $t0>>]
  | (T $t0 $t1 $t2) -> [<:tactic:<$t2; $t1; $t0>>]
  | (T $t0 $t1) -> [<:tactic:<$t1; $t0>>]
  | (T $t0) -> [$t0]
  esac.

(* A final (but crucial) facility for large-scale computational reflection. *)
(* This minimizes the amount of recomputation done by Coq.                  *)

Grammar tactic simple_tactic : tactic :=
  by_compute ["By" "Compute"] ->
  [By HideGoal; Compute in GoalMarker; Unfold GoalMarker].

Unset Implicit Arguments.


