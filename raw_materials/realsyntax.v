(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
(***********************************************************************)
(*  The library real syntax, adapted to setoid reals                   *)
(***********************************************************************)

Require real.

(***********************************************************************)
(* There are several differences with the library syntax:              *)
(*    - the math priorities are strictly adhered to:                   *)
(*      unary `-` binds tightest                                       *)
(*     '/' binds strictly tighter than '*', and does not associate     *)
(*     '*' binds tighter than `+` and binary `-`, and associates left  *)
(*     '+' and binary '-' have equal priorities, and associate left    *)
(*     `=` `<>` `<` `>` `<=` `>=` have the lowest priority and don't   *)
(*      associate. The double comparison syntax is not supported.      *)
(*    - the syntax for the sup function is                             *)
(*          sup E or sup {x | P(x)} where P(x) can be a comparison,    *)
(*          e.g., sup {x | x * x <= 2}                                 *)
(*    - <, >=, <, <>, /, and binary - are all strictly sugar, and are  *)
(*      expanded at parse time, e.g., x < y means ~(y <= x).           *)
(*    - the syntax for the inverse of x is 1/x. "1 divided by x" is    *)
(*      printed as its expansion, 1 * 1/x.                             *)
(*    - small integer constants (up to 10) are expanded at parse time, *)
(*      but larger ones are kept as calls to natr. This means that     *)
(*      x + 11 will print as x + (natr R [11]) (in a structure R);     *)
(*      it will print as x + 11 after a Simpl or an Eval.              *)
(*    - One can specify the structure interpreting integer constants,  *)
(*      e.g., 1%R means (real1 R).                                     *)
(*    - The syntax for escaping back to Gallina, [term1 ... termn]     *)
(*      is systematically used for calls with explicit arguments and   *)
(*      for integer constants (as in the call (natr R [11]) above).    *)
(*    - The pretty-printer doesn't generate useless brackets, e.g.,    *)
(*      around function arguments, and puts space around the operators *)
(*      (except in atomic fractions such as 3/4, 1/x, or -x/2).        *)
(***********************************************************************)

Grammar constr constr0 :=
  real_expr [ "`" real_expr($x) "`" ] -> [ $x ]
with real_expr : constr :=
  rexp_expr4 [ real_expr4($x) ] -> [ $x ]
| rexp_eq  [ real_expr4($x1) "="  real_expr4($x2) ] -> [  (eqr $x1 $x2) ]
| rexp_neq [ real_expr4($x1) "<>" real_expr4($x2) ] -> [ ~(eqr $x1 $x2) ]
| rexp_leq [ real_expr4($x1) "<=" real_expr4($x2) ] -> [  (leqr $x1 $x2) ]
| rexp_lt  [ real_expr4($x1) "<"  real_expr4($x2) ] -> [ ~(leqr $x2 $x1) ]
| rexp_geq [ real_expr4($x1) ">=" real_expr4($x2) ] -> [  (leqr $x2 $x1) ]
| rexp_gt  [ real_expr4($x1) ">"  real_expr4($x2) ] -> [ ~(leqr $x1 $x2) ]
with real_expr4 : constr :=
  rexp_add [ real_expr4($x1) "+" real_expr3($x2) ] -> [ (addr $x1 $x2) ]
| rexp_sub [ real_expr4($x1) "-" real_expr3($x2) ] -> [ (addr $x1 (oppr $x2)) ]
| rexp_expr3 [ real_expr3($x) ] -> [ $x ]
with real_expr3 : constr :=
  rexp_mul [ real_expr3($x1) "*" real_expr2($x2) ] -> [ (mulr $x1 $x2) ]
| rexp_expr2 [ real_expr2($x) ] -> [ $x ]
with real_expr2 : constr :=
  rexp_div [ real_expr1($x1) "/" real_expr1($x2) ] ->
  case [$x1] of
    (APPLIST (QUALID real1) $_) -> [(invr $x2)]
  | $_ ->  [ (mulr $x1 (invr $x2)) ]
  esac
| rexp_expr1 [ real_expr1($x) ] -> [ $x ]
with real_expr1 : constr :=
  rexp_sup [ "sup" real_set($set) ] -> [ (supr $set) ]
| rexp_opp [ "-" real_expr1($x) ] -> [ (oppr $x) ] 
| rexp_lit [ real_literal($x) ] -> [ $x ]
| rexp_expr0 [ real_expr0($x) ] -> [ $x ]
with real_expr0 : constr :=
| rexp_id [ global($c) ] -> [ $c ]
| rexp_escape [ "[" constr($e) "]" ] -> [ $e ]
| rexp_paren [ "(" real_expr4($x) ")" ] -> [ $x ]
| rexp_pair [ "(" real_expr4($x1) "," real_expr4($x2) ")" ] -> [ ($x1, $x2) ]
| rexp_implicit [ "?" ] -> [ ? ]
with real_expr0 : ast :=
  rexp_call [ "(" real_expr4($f) real_args($args) ")" ] ->
  [ (APPLIST $f ($LIST $args)) ]
| rexp_meta [ "?" prim:number($n) ] ->
  [ (META $n) ]
with real_args : ast list:=
  rargs_cons [ real_expr4($x) real_args($args) ] -> [ $x ($LIST $args) ]
| rargs_last [ real_expr4($x) ] -> [ $x ]
with real_set : constr :=
  rset_prop [ "{" prim:var($id) "|" real_expr($pred) "}" ] -> [ [$id]$pred ]
| rset_expr0 [ real_expr0($set) ] -> [ $set ]
with real_literal : constr :=
  rlit0 [ "0" real_cast($r) ] ->
  [ (real0 $r) ]
| rlit1 [ "1" real_cast($r) ] ->
  [ (real1 $r) ]
| rlit2 [ "2" real_cast($r) ] ->
  let $r1 = [ (real1 $r) ] in let $a1 = [ (addr $r1) ] in [ ($a1 $r1) ]
| rlit3 [ "3" real_cast($r) ] ->
  let $r1 = [ (real1 $r) ] in let $a1 = [ (addr $r1) ] in [ ($a1 ($a1 $r1)) ]
| rlit4 [ "4" real_cast($r) ] ->
  let $r1 = [ (real1 $r) ] in let $a1 = [ (addr $r1) ] in [ ($a1 ($a1 ($a1 $r1))) ]
| rlit5 [ "5" real_cast($r) ] ->
  let $r1 = [ (real1 $r) ] in let $a1 = [ (addr $r1) ] in
  [ ($a1 ($a1 ($a1 ($a1 $r1)))) ]
| rlit6 [ "6" real_cast($r) ] ->
  let $r1 = [ (real1 $r) ] in let $a1 = [ (addr $r1) ] in
  [ ($a1 ($a1 ($a1 ($a1 ($a1 $r1))))) ]
| rlit7 [ "7" real_cast($r) ] ->
  let $r1 = [ (real1 $r) ] in let $a1 = [ (addr $r1) ] in
  [ ($a1 ($a1 ($a1 ($a1 ($a1 ($a1 $r1)))))) ]
| rlit8 [ "8" real_cast($r) ] ->
  let $r1 = [ (real1 $r) ] in let $a1 = [ (addr $r1) ] in
  [ ($a1 ($a1 ($a1 ($a1 ($a1 ($a1 ($a1 $r1))))))) ]
| rlit9 [ "9" real_cast($r) ] ->
  let $r1 = [ (real1 $r) ] in let $a1 = [ (addr $r1) ] in
  [ ($a1 ($a1 ($a1 ($a1 ($a1 ($a1 ($a1 ($a1 $r1)))))))) ]
| rlit10 [ "10" real_cast($r) ] ->
  let $r1 = [ (real1 $r) ] in let $a1 = [ (addr $r1) ] in
  [ ($a1 ($a1 ($a1 ($a1 ($a1 ($a1 ($a1 ($a1 ($a1 $r1))))))))) ]
| rlit_nat [ nat:number($n) real_cast($r) ] -> [ (natr $r $n) ]
with real_cast : constr :=
  rcast_some ["%" constr0($r)] -> [ $r ]
| rcast_none [ ] -> [ ? ].

Syntax constr
  level 0:
    top_leqr [ (leqr $x1 $x2) ] -> 
    [ "`" [<hov 0> (REXP 5 <<(leqr $x1 $x2)>>)] "`" ]
  | top_ltr [ ~(leqr $x2 $x1) ] -> 
    [ "`" [<hov 0> (REXP 5 <<~(leqr $x2 $x1)>>)] "`" ]
  | top_eqr [ (eqr $x1 $x2) ] -> 
    [ "`" [<hov 0> (REXP 5 <<(eqr $x1 $x2)>>)] "`" ]
  | top_neqr [ ~(eqr $x1 $x2) ] ->
    [ "`" [<hov 0> (REXP 5 <<~(eqr $x1 $x2)>>)] "`" ]
  | top_addr [ (addr $x1 $x2) ] ->
    [ "`" [<hov 0> (REXP 4 <<(addr $x1 $x2)>>)] "`" ]
  | top_oppr [ (oppr $x) ] ->
    [ "`" [<hov 0> (REXP 1 <<(oppr $x)>>)] "`" ]
  | top_mulr [ (mulr $x1 $x2) ] ->
    [ "`" [<hov 0> (REXP 3 <<(mulr $x1 $x2)>>)] "`" ]
  | top_invr [ (invr $x) ] ->
    [ "`" [<hov 0> (REXP 2 <<(invr $x)>>)] "`" ]
  | top_supr [ (supr $pred) ] ->
    [ "`" [<hov 0> (REXP 1 <<(supr $pred)>>)] "`" ]
  | top_real0 [ (real0 $_) ] ->
    [ "`0`" ]
  | top_real1 [ (real1 $_) ] ->
    [ "`1`" ]
  ;
  level 10:
    top_explicit_oppr [ (oppr 1!$r) ] -> [ "oppr 1!" $r:L ]
  | top_explicit_invr [ (invr 1!$r) ] -> [ "invr 1!" $r:L ]
  | top_explicit_supr [ (supr 1!$r) ] -> [ "supr 1!" $r:L ]
  ;

  level 0:
  | rescape [<<(REXP $_ a $t)>>] ->
    [ "[" [<hov 0> $t] "]" ]
  | rcall [<<(REXP $_ (APPLIST $h ($LIST $t)))>>] ->
    [ (RCALL (APPLIST $h ($LIST $t)) ($LIST $t)) ]
  ;
  level 0:
    rcall_normal_arg [ <<(RCALL $x $y ($LIST $args))>> ] ->
    [ (RCALL $x ($LIST $args)) ] 
  | rcall_explicit_arg [ <<(RCALL $x (EXPL $_ $_) ($LIST $_))>> ] ->
    [ "[" [<hov 0> $x] "]" ]
  | rcall_all_normal [ <<(RCALL (APPLIST $f ($LIST $args)))>> ] ->
    [ "(" [<hov 0> (REXP 4 $f) [1 0] (RARGS ($LIST $args))] ")" ]
  ;
  level 0:
    rargs_cons [<<(RARGS $x ($LIST $args))>>] ->
    [ (RARG $x $x) [1 0] (RARGS ($LIST $args)) ] 
  | rargs_last [<<(RARGS $x)>>] -> [ (RARG $x $x) ]
  ;
  level 0:
    rarg_default [<<(RARG $x $_)>>] -> [ (REXP 4 $x) ]
  | rarg_addr [<<(RARG $x <<(addr $y $_)>>)>>] -> [ (RARG $x $y) ]
  | rarg_mulr [<<(RARG $x <<(mulr $y $_)>>)>>] -> [ (RARG $x $y) ]
  | rarg_oppr [<<(RARG $x <<(oppr $_)>>)>>] -> [ "(" [<hov 0> (REXP 4 $x)] ")" ]
  | rarg_explicit1 [<<(RARG $x <<($_ 1!$_)>>)>>] -> [ (REXP 0 $x) ]
  ;
  
  level 5:
    rexpr [<<(REXP 5 $x)>>] ->
    [ (REXP $x) ]
  | leqr [<<(REXP 5 <<(leqr $x1 $x2)>>)>>] -> 
    [ (REXP 4 $x1) [1 0] "<= " (REXP 4 $x2) ]
  | ltr [<<(REXP 5 <<~(leqr $x2 $x1)>>)>>] -> 
    [ (REXP 4 $x1) [1 0] "< "(REXP 4 $x2) ]
  | eqr [<<(REXP 5 <<(eqr $x1 $x2)>>)>>] -> 
    [ (REXP 4 $x1) [1 0] "= "(REXP 4 $x2) ]
  | neqr [<<(REXP 5 <<~(eqr $x1 $x2)>>)>>] ->
    [ (REXP 4 $x1) [1 0] "<> "(REXP 4 $x2) ]
  ;
  
  level 4:
    addr [<<(REXP $_ <<(addr $x1 $x2)>>)>>] ->
    [ (REXP 4 $x1):E " +" [1 0] (REXP 3 $x2):L ]
  | subr [<<(REXP $_ <<(addr $x1 (oppr $x2))>>)>>] ->
    [ (REXP 4 $x1):E " -" [1 0] (REXP 3 $x2):L ]
  ;

  level 3:
    mulr [<<(REXP $_ <<(mulr $x1 $x2)>>)>>] ->
    [ (REXP 3 $x1):E " *" [1 0] (REXP 2 $x2):L ]
  ;

  level 2: 
    divr [<<(REXP $_ <<(mulr $x1 (invr $x2))>>)>>] ->
    [ (REXP 1 $x1):L (RFBAR REXP $x1 (RFBAR REXP $x2 (RFBAR))) (REXP 1 $x2):L ]
  | invr [<<(REXP $_ <<(invr $x)>>)>>] ->
    [ "1" (RFBAR REXP $x (RFBAR)) (REXP 1 $x):L  ]
  ;
  level 3:
    div1r [<<(REXP $_ <<(mulr (real1 $_) (invr $x2))>>)>>] ->
    [ "1 *" [1 0] (REXP 2 <<(invr $x2)>>):E ]
  ;
  level 0:
    rfbar_space [<<(RFBAR $_ $_ $bar)>>] ->
    [ " /" [1 0] ]
  | rfbar_oppr [<<(RFBAR REXP <<(oppr $x)>> $bar)>>] ->
    [ (RFBAR REXP $x $bar) ]
  | rfbar_var [<<(RFBAR REXP ($VAR $_) $bar)>>] -> [ $bar ]
  | rfbar_secvar [<<(RFBAR REXP (SECVAR $_) $bar)>>] -> [ $bar ]
  | rfbar_const [<<(RFBAR REXP (CONST $_) $bar)>>] -> [ $bar ]
  | rfbar_mutconstruct [<<(RFBAR REXP (MUTCONSTRUCT $_ $_ $_) $bar)>>] -> [ $bar ]
  | rfbar_real0 [<<(RFBAR REXP <<(real0 $_)>> $bar)>>] -> [ $bar ]
  | rfbar_real1 [<<(RFBAR $_ <<(real1 $_)>> $bar)>>] -> [ $bar ]
  | rfbar_lit [<<(RFBAR $_ <<(addr (real1 $_) $x)>> $bar)>>] ->
    [ (RFBAR RLIT $x $bar) ]
  | rfbar_nospace [ <<(RFBAR)>> ] ->
    [ "/" ]
  ;

  level 1:
    oppr [<<(REXP $_ <<(oppr $x)>>)>>] -> [ "-" (REXP 1 $x):E ]
  | supr [<<(REXP $_ <<(supr $x)>>)>>] -> [ "sup " (RSET $x) ]
  | real0 [<<(REXP $_ <<(real0 $_)>>)>>] -> [ "0" ]
  | real1 [<<(REXP $_ <<(real1 $_)>>)>>] -> [ "1" ]
  | rliteral [<<(REXP $level <<(addr (real1 $_) $x)>>)>>] ->
    [ (RLIT $level $x <<(S O)>> $x) ]
  ;
  level 4:
    rlit_default [<<(RLIT $_ $x $_ $_)>>] ->
    [ "(" [<hov 0> "1 +" [1 0] (REXP 3 $x):L] ")" ]
  | rlit_default_expr4 [<<(RLIT 4 $x $_ $_)>>] ->
    [ "1 +" [1 0] (REXP 3 $x):L ]
  ;
  level 0:
    rlit_one [<<(RLIT $_ $_ $n <<(real1 $_)>>)>>] ->
    [ <<(S $n)>> ]
  | rlit_succ [<<(RLIT $level $x $n <<(addr (real1 $_) $y)>>)>>] ->
    [ (RLIT $level $x <<(S $n)>> $y) ]
  ;
  level 0:
    rset_expr0 [<<(RSET $x)>>] ->
    [ (REXP 0 $x):E ]
  | rset_pred [<<(RSET (LAMBDALIST $_ [$id]$pred))>>] ->
    [ "{" [<hov 0> $id " |" [1 0] (REXP 5 $pred)] "}" ]
  ;

  level 0:
    rvar [<<(REXP $_ ($VAR $id))>>] -> [ $id ]
  | rsecvar [<<(REXP $_ (SECVAR $name))>>] -> [ (SECVAR $name) ]
  | rconst [<<(REXP $_ (CONST $name))>>] -> [ (CONST $name) ]
  | rmutind [<<(REXP $_ (MUTIND $name $i))>>] -> [ (MUTIND $name $i) ]
  | rmutconstruct [<<(REXP $_ (MUTCONSTRUCT $name $i $j))>>] ->
    [ (MUTCONSTRUCT $name $i $j) ]
  | rpair [ <<(REXP <<(pair $_ $_ $x1 $x2)>>)>> ] ->
    [ "(" [<hov 0> (REXP 4 $x1) "," [1 0] (REXP 4 $x2)] ")" ] 
  ;
  level 0:
    rescape_nat_zero [<<(REXP $_ <<O>>)>>] -> [ "[0]" ]
  | rescape_nat_succ [<<(REXP $_ <<(S $n)>>)>>] ->
    [ "[" [<hov 0> <<(S $n)>>] "]" ]
  | rescape_explicit1 [ <<(REXP $_ <<($f 1!$x)>>)>> ] ->
    [ "[" [<hov 0> <<($f 1!$x)>>] "]" ]
  .









