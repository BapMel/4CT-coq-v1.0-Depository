(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require tacticext.
Require boolprop.
Require funs.
Require dataset.
Require natprop.
Require seq.
Require finset.
Require paths.
Require connect.

Set Implicit Arguments.

(* Minimal handling of signed integers:                                 *)
(*    - the additive group.                                             *)
(*    - comparison                                                      *)
(*    - increment/decrement                                             *)
(*    - halving/parity                                                  *)
(*    - multiplication (mostly for the construction of the reals)       *)
(*    - summations over finite domains, and over quotients in such      *)
(*      domains                                                         *)

Inductive znat : Set :=
  Zpos : nat -> znat
| Zneg : nat -> znat.

Syntax constr level 0 :
  pp_zpos [(Pretty $_ (Zpos $n))] -> [$n]
| pp_zneg [(Pretty $_ (Zneg $n))] -> ["-" <<(S $n)>>].

Grammar constr constr10 : constr :=
  znat_form ["Znat" znat_lit($z)] -> [$z]
with znat_lit : constr :=
  neg_znat_lit ["-" nat:number($n)] ->
  case [$n] of
   (APPLIST $_ $n') -> [(Zneg $n')]
  | $_ -> [(Zpos $n)]
  esac
| pos_znat_lit [nat:number($n)] ->
  [(Zpos $n)].

Fixpoint subnz [m : nat] : nat -> znat :=
  [n]Cases m n of
    (0) _ => (Zneg n)
  | (S m') (0) => (Zpos m')
  | (S m') (S n') => (subnz m' n')
  end.

Definition addz [z1, z2 : znat] : znat :=
  Cases z1 z2 of
    (Zpos n1) (Zpos n2) => (Zpos (addn n1 n2))
  | (Zpos n1) (Zneg n2) => (subnz n1 n2)
  | (Zneg n1) (Zneg n2) => (Zneg (S (addn n1 n2)))
  | (Zneg n1) (Zpos n2) => (subnz n2 n1)
  end.

Lemma zpos_addn : (n1, n2 : nat) (Zpos (addn n1 n2)) = (addz (Zpos n1) (Zpos n2)).
Proof. Done. Qed.

Definition zneg : nat -> znat := (subnz (1)).

Lemma znegI : (n : nat) (Zneg n) = (zneg (S n)).
Proof. Done. Qed.

Lemma add0z : (z : znat) (addz (Znat 0) z) = z.
Proof. By Case. Qed.

Lemma addzC : (z1, z2 : znat) (addz z1 z2) = (addz z2 z1).
Proof. By Move=> [n|n] [m|m]; Rewrite: /= 1?addnC. Qed.

Lemma addz0 : (z : znat) (addz z (Znat 0)) = z.
Proof. By Move=> *; Rewrite: addzC add0z. Qed.

Definition incz [z : znat] : znat :=
  Cases z of
    (Zpos n) => (Zpos (S n))
  | (Zneg (0)) => (Znat 0)
  | (Zneg (S n)) => (Zneg n)
  end.

Definition decz [z : znat] : znat :=
  Cases z of
    (Zneg n) => (Zneg (S n))
  | (Zpos (0)) => (Zneg (0))
  | (Zpos (S n)) => (Zpos n)
  end.

Lemma incz_def : (z : znat) (incz z) = (addz z (Znat 1)).
Proof. By Move=> z; Rewrite addzC; Case: z => [n|[|n]]. Qed.

Lemma decz_def : (z : znat) (decz z) = (addz z (Znat -1)).
Proof. By Move=> z; Rewrite addzC; Case: z => [[|n]|n]. Qed.

Lemma incz_dec : (x : znat) (incz (decz x)) = x.
Proof. By Case=> [[|n]|m]. Qed.

Lemma decz_inc : (x : znat) (decz (incz x)) = x.
Proof. By Case=> [n|[|m]]. Qed.

Lemma addzA : (z1, z2, z3 : znat)
  (addz z1 (addz z2 z3)) = (addz (addz z1 z2) z3).
Proof.
Step Hsub: (m, n, p: nat) (subnz (addn m n) p) = (addz (subnz m p) (Zpos n)).
  By Move=> m n; Elim: m => [|m Hrec] [|p] /=.
Step Hsub': (m, n, p: nat)
  (subnz m (S (addn n p))) = (addz (subnz m n) (Zneg p)).
  By Move=> m n p; Elim: m n => [|m Hrec] [|n]; Try Exact (Hrec n).
Move=> [n|n] [m|m] [p|p]; Rewrite: /= ?addnI ?addnS ?addnA //.
  By Rewrite: addnC Hsub addzC.
  By Rewrite: -Hsub addnC Hsub addzC.
  By Rewrite: -Hsub' addnC Hsub' addzC.
  By Rewrite: addnC Hsub' addzC.
Qed.

Lemma addzCA : (z1, z2, z3 : znat)
  (addz z1 (addz z2 z3)) = (addz z2 (addz z1 z3)).
Proof. By Move=> *; Rewrite: !addzA (addzC z1). Qed.

Definition oppz [z : znat] : znat :=
  Cases z of (Zpos (S n')) => (Zneg n') | (Zneg n) => (Zpos (S n)) | _ => z end.

Lemma oppz_opp : (z : znat) (oppz (oppz z)) = z.
Proof. By Move=> [[|n]|n]. Qed.

Lemma addz_opp : (z : znat) (addz z (oppz z)) = (Znat 0).
Proof. By Move=> [[|n]|n]; Try Elim n; Simpl. Qed.

Lemma addz_opp_inv : (z : znat) (monic (addz (oppz z)) (addz z)).
Proof. By Move=> z1 z2; Rewrite: addzA addz_opp add0z. Qed.

Lemma addz_inv : (z : znat) (monic (addz z) (addz (oppz z))).
Proof. Move=> z; Rewrite: -{1 z}oppz_opp; Apply: (!addz_opp_inv). Qed.

Lemma addz_inj : (z : znat) (injective (addz z)).
Proof. Exact [z](monic_inj (!addz_inv z)). Qed.

Lemma oppz_add : (z1, z2 : znat)
  (oppz (addz z1 z2)) = (addz (oppz z1) (oppz z2)).
Proof.
Move=> z1 z2; Apply (addz_inj 1!(addz z1 z2)).
By Rewrite: addz_opp -addzA (addzCA z2) addzA !addz_opp.
Qed.

Definition posz [z : znat] : bool :=
  if z is (Zpos (S _)) then true else false.

Lemma posz_add : (z1, z2 : znat)
  (posz (addz z1 z2)) -> (posz z1) \/ (posz z2).
Proof. By Move=> [[|n]|n] [[|m]|m]; Auto. Qed.

Lemma posz_cover : (z : znat) (or3 (posz z) z = (Znat 0) (posz (oppz z))).
Proof. By Move=> [[|n]|n]; [Constructor 2 | Constructor 1 | Constructor 3]. Qed.

Definition subz [z1, z2 : znat] : znat := (addz z1 (oppz z2)).

Lemma subzI : (z1, z2 : znat) (addz z1 (oppz z2)) = (subz z1 z2).
Proof. Done. Qed.

Lemma subz0 : (z : znat) (subz z (Znat 0)) = z.
Proof. By Move=> *; Rewrite: /subz /oppz addz0. Qed.

Lemma sub0z : (z : znat) (subz (Znat 0) z) = (oppz z).
Proof. By Move=> *; Rewrite: /subz add0z. Qed.

Lemma subzz : (z : znat) (subz z z) = (Znat 0).
Proof. By Move=> *; Rewrite: /subz addz_opp. Qed.

Lemma zpos_subn : (n1, n2 : nat)
  (Zpos (subn n1 n2)) =
     (if (leq n2 n1) then (subz (Zpos n1) (Zpos n2)) else (Znat 0)).
Proof.
Elim=> [|n1 Hrec] [|n2] //=; LeftBy Rewrite addn0.
By Rewrite: subSS Hrec ltnS; Case: n2 => //; Rewrite subz0.
Qed.

Lemma addz_subA : (z1, z2, z3 : znat)
  (addz z1 (subz z2 z3)) = (subz (addz z1 z2) z3).
Proof. By Move=> *; Rewrite: /subz addzA. Qed.

Lemma addz_subCA : (z1, z2, z3 : znat)
  (addz z1 (subz z2 z3)) = (addz z2 (subz z1 z3)).
Proof. By Move=> *; Rewrite: /subz addzCA. Qed.

Lemma addz_sub : (z1, z2 : znat) (addz z1 (subz z2 z1)) = z2.
Proof. By Move=> *; Rewrite: addz_subCA subzz addz0. Qed.

Lemma addz_sub2CA : (z1, z2, z3, z4 : znat)
  (addz (subz z1 z2) (subz z3 z4)) = (addz (subz z1 z4) (subz z3 z2)).
Proof. By Move=> *; Rewrite: addzC !addz_subA addzC addz_subCA addzC. Qed.

Lemma addz_sub2 : (z2, z1, z3 : znat)
  (addz (subz z1 z2) (subz z2 z3)) = (subz z1 z3).
Proof. By Move=> *; Rewrite: addz_sub2CA subzz addz0. Qed.

Lemma subz_add : (z1, z2 : znat) (subz (addz z1 z2) z1) = z2.
Proof. By Move=> *; Rewrite: -addz_subA addz_sub. Qed.

Lemma subz_sub : (z2, z1, z3 : znat)
  (subz (subz z1 z2) z3) = (subz z1 (addz z2 z3)).
Proof. By Move=> *; Rewrite: /subz oppz_add addzA. Qed.

Lemma subz_add2l : (z2, z1, z3 : znat)
  (subz (addz z2 z1) (addz z2 z3)) = (subz z1 z3).
Proof.  By Move=> *; Rewrite: -subz_sub subz_add. Qed.

Lemma subz_add2r : (z2, z1, z3 : znat)
  (subz (addz z1 z2) (addz z3 z2)) = (subz z1 z3).
Proof. By Move=> z2 z1 z3; Rewrite: -!(addzC z2) subz_add2l. Qed.

Lemma oppz_sub : (z1, z2 : znat) (oppz (subz z1 z2)) = (subz z2 z1).
Proof. By Move=> *; Rewrite: /subz oppz_add oppz_opp addzC. Qed.

Definition leqz [z1, z2 : znat] : bool := (negb (posz (subz z1 z2))).

Lemma leqzI : (z1, z2 : znat) (negb (posz (subz z1 z2))) = (leqz z1 z2).
Proof. Done. Qed.

Lemma leqzz : (z : znat) (leqz z z).
Proof. By Move=> *; Rewrite: /leqz subzz. Qed.

Lemma leqz_trans : (z2, z1, z3 : znat) 
  (leqz z1 z2) -> (leqz z2 z3) -> (leqz z1 z3).
Proof.
Move=> z2 z1 z3 Hz12 Hz23; Rewrite: /leqz -(addz_sub2 z2).
By Apply/idP; Case/posz_add; Apply: negP.
Qed.

Lemma leqz_add2l : (z2, z1, z3 : znat)
  (leqz (addz z2 z1) (addz z2 z3)) = (leqz z1 z3).
Proof. By Move=> *; Rewrite: /leqz subz_add2l. Qed.

Lemma leqz_add2r : (z2, z1, z3 : znat)
  (leqz (addz z1 z2) (addz z3 z2)) = (leqz z1 z3).
Proof. By Move=> *; Rewrite: /leqz subz_add2r. Qed.

Lemma leqz_add2 : (z1, z3 : znat) (leqz z1 z3) ->
                  (z2, z4 : znat) (leqz z2 z4) ->
  (leqz (addz z1 z2) (addz z3 z4)).
Proof.
Move=> z1 z3 Hz13 z2 z4 Hz24; Rewrite: /leqz -subz_sub addzC -addz_subA.
By Rewrite: addzC -addz_subA; Apply/idP; Case/posz_add; Apply: negP.
Qed.

Lemma leqz_opp2 : (z1, z2 : znat) (leqz (oppz z1) (oppz z2)) = (leqz z2 z1).
Proof. By Move=> *; Rewrite: {1}/leqz /subz oppz_opp addzC. Qed.

Lemma leqz_nat : (m, n : nat) (leqz (Zpos m) (Zpos n)) = (leq m n).
Proof.
Elim=> [|m Hrec] [|n] //; Rewrite: ltnS -Hrec.
By Case n; Rewrite: /leqz //= addn0.
Qed.

Lemma leq0z : (z : znat) (leqz (Znat 0) z) = (negb (posz (oppz z))).
Proof. By Move=> [[|n]|n]. Qed.

Lemma leq1z : (z : znat) (leqz (Znat 1) z) = (posz z).
Proof. By Move=> [[|[|n]]|n]. Qed.

Definition eqz [z1, z2 : znat] : bool :=
  Cases (subz z1 z2) of (Zpos (0)) => true | _ => false end.

Lemma eqzP : (reflect_eq eqz).
Proof.
Move=> z1 z2; Apply: introP => [Hz12 | Hz12 Dz1].
  Rewrite: -{1 z2}addz0; Apply (monic_move (addz_opp_inv z2)).
  Move: Hz12; Rewrite: addzC -/(subz z1 z2) /eqz.
  By Case: (subz z1 z2) => [[|n]|n].
By Rewrite: Dz1 /eqz subzz in Hz12.
Qed.

Canonical Structure znatData := (DataSet eqzP).

Lemma eqz_leq : (z1, z2 : znat) (z1 =d z2) = (andb (leqz z1 z2) (leqz z2 z1)).
Proof.
Move=> z1 z2; Apply/idP/idP; LeftBy Move/eqP=> Dz1; Rewrite: Dz1 leqzz.
Move/andP=> [Hz12 Hz21]; Rewrite: /leqz -oppz_sub /eqd /= /eqz in Hz21 Hz12 *.
By Case: (posz_cover (subz z1 z2)) Hz21 Hz12 => [Ez12]; Rewrite Ez12.
Qed.

Lemma leqz_inc : (z1, z2 : znat)
   (leqz z1 z2) = (orb z1 =d z2 (leqz (incz z1) z2)).
Proof.
Move=> z1 z2; Rewrite: /leqz incz_def addzC -addz_subA /eqd /= /eqz.
By Case: (subz z1 z2); Case.
Qed.

Lemma leqz_dec : (z1, z2 : znat)
   (leqz z1 z2) = (orb z1 =d z2 (leqz z1 (decz z2))).
Proof.
Move=> z1 z2; Rewrite: /leqz decz_def -subz_sub {2}/subz addzC /eqd /= /eqz.
By Case: (subz z1 z2); Case.
Qed.

Lemma leqz_inc2 : (x, y : znat) (leqz (incz x) (incz y)) = (leqz x y).
Proof. By Move=> *; Rewrite: !incz_def leqz_add2r. Qed.

Lemma leqz_dec2 : (x, y : znat) (leqz (decz x) (decz y)) = (leqz x y).
Proof. By Move=> *; Rewrite: !decz_def leqz_add2r. Qed.

Lemma leqz_dec_inc : (x, y : znat) (leqz (decz x) y) = (leqz x (incz y)).
Proof. By Move=> *; Rewrite: -leqz_inc2 incz_dec. Qed.

Lemma leqz_inc_dec : (x, y : znat) (leqz (incz x) y) = (leqz x (decz y)).
Proof. By Move=> *; Rewrite: -leqz_dec2 decz_inc. Qed.

Lemma leq_z_incz : (x : znat) (leqz x (incz x)).
Proof. By Move=> *; Rewrite: leqz_inc leqzz orbT. Qed.

Lemma leq_decz_z : (x : znat) (leqz (decz x) x).
Proof. By Move=> *; Rewrite: leqz_dec leqzz orbT. Qed.

Lemma leq_decz_incz : (x : znat) (leqz (decz x) (incz x)).
Proof. By Move=> *; Rewrite: leqz_dec decz_inc leq_decz_z orbT. Qed.

Lemma negb_leqz : (x, y : znat) (negb (leqz x y)) = (leqz (incz y) x).
Proof.
Move=> x y; Rewrite: {2}/leqz -oppz_sub incz_def -subz_sub /leqz.
By Case: (subz x y) => [[|[|n]]|m].
Qed.

(* Parity & halving.                                 *)

Definition oddz [z : znat] : bool :=
  Cases z of (Zpos n) => (odd n) | (Zneg m) => (negb (odd m)) end.

Lemma oddz_add : (z1, z2 : znat) (oddz (addz z1 z2)) = (addb (oddz z1) (oddz z2)).
Proof.
Step Hsnz : (m, n : nat) (oddz (subnz m n)) = (negb (addb (odd m) (odd n))).
  Elim=> //= [m Hrec] [|n] /=; LeftBy Rewrite: addbF negb_elim.
  Rewrite: Hrec -!addbT; Congr addb; Rewrite: -!addbA; Congr addb.
  By Rewrite: addbC -addbA addbC.
Move=> [m1|n1] [m2|n2] //=; Rewrite: ?odd_addn ?Hsnz //= -!addbT -!addbA //.
  By Rewrite: addbC -addbA.
By Congr addb; Rewrite: addbA addbC.
Qed.

Lemma oddz_double : (z : znat) (oddz (addz z z)) = false.
Proof. By Move=> *; Rewrite: oddz_add addbb. Qed.

Definition halfz [z : znat] : znat :=
  Cases z of (Zpos n) => (Zpos (half n)) | (Zneg m) => (Zneg (half m)) end.

Lemma oddz_bit : (b : bool) (oddz (Zpos b)) = b.
Proof. By Case. Qed.

Lemma halfz_double : (z : znat) (halfz (addz z z)) = z.
Proof. By Case=> *; Rewrite: /= -double_addnn ?half_double ?uphalf_double. Qed.

Lemma halfz_bit : (b : bool) (halfz (Zpos b)) = (Znat 0).
Proof. By Case. Qed.

Lemma odd_double_halfz : (z : znat)
  (addz (Zpos (oddz z)) (addz (halfz z) (halfz z))) = z.
Proof.
Case=> [n | m]; LeftBy Rewrite: /= -double_addnn odd_double_half.
Rewrite: {1 addz}lock /= -lock -double_addnn -add1n.
By Rewrite: -(addn_negb (odd m)) -addnA odd_double_half; Case (odd m).
Qed.

Lemma halfz_add_double : (z1, z2 : znat)
  (halfz (addz z1 (addz z2 z2))) = (addz (halfz z1) z2).
Proof.
Move=> z1 z2; Rewrite: -{1 z1}odd_double_halfz -!addzA -(addzCA z2).
Rewrite: [z](addzA z z2); Case: (oddz z1) (addz (halfz z1) z2) => [|] [m|n] //=;
 By Rewrite: ?add0n -double_addnn ?half_double ?uphalf_double.
Qed.

Lemma leqz_halfr : (x, y : znat) (leqz x (halfz y)) = (leqz (addz x x) y).
Proof.
Move=> x y; Rewrite: -{2 y}odd_double_halfz; Move: {y}(oddz y) (halfz y) => b y.
Rewrite: /leqz (addzC (Zpos b)) -!subz_sub -addz_subA addzC -addz_subA.
By Case: (subz x y) b => [[|n]|[|m]] [|] //=; Rewrite: addnI addnS.
Qed.

Lemma leqz_halfl : (x, y : znat) (leqz (halfz x) y) = (leqz x (incz (addz y y))).
Proof.
Move=> x y; Rewrite: -(leqz_inc2 x) -negb_leqz !incz_def addzC -!addzA addzCA.
By Rewrite: addzA -incz_def -leqz_halfr negb_leqz leqz_inc2.
Qed.

(* Multiplication.                                           *)

Definition mulz [m1, m2 : znat] : znat :=
  Cases m1 of
    (Zpos (0)) => m1
  | (Zpos (S n)) => (iter n (addz m2) m2)
  | (Zneg n) => (oppz (iter n (addz m2) m2))
  end.

Lemma mulz0 : (m : znat) (mulz m (Znat 0)) = (Znat 0).
Proof. By Move=> [[|n]|n] //=; Elim: n => // [n Hrec]; Rewrite: -iter_f. Qed.

Lemma mul0z : (m : znat) (mulz (Znat 0) m) = (Znat 0). Proof. Done. Qed.

Lemma mulz_oppl : (m1, m2 : znat) (mulz (oppz m1) m2) = (oppz (mulz m1 m2)).
Proof. By Move=> [[|n]|n] //= m2; Rewrite: oppz_opp. Qed.

Lemma oppz_cases : (P : znat -> Prop)
  (Hopp : (m : znat) (P m) -> (P (oppz m)); Hpos : (n : nat) (P (Zpos n)))
  (m : znat) (P m).
Proof.
Move=> P Hopp Hpos m; Rewrite: -(oppz_opp m).
Case: m => [n|n] //; Auto; Apply Hopp; Apply: Hpos.
Qed.

Lemma mulz_oppr : (m1, m2 : znat) (mulz m1 (oppz m2)) = (oppz (mulz m1 m2)).
Proof.
Move=> m1; Elim/oppz_cases: m1; LeftBy Move=> m1 Hrec m2; Rewrite: !mulz_oppl Hrec.
By Move=> [[|n]|n] //= m2; Elim: n => [|n Hrec] //=; Rewrite: Hrec oppz_add.
Qed.

Lemma mulz_nat : (n1, n2 : nat)
  (mulz (Zpos n1) (Zpos n2)) = (Zpos (iter n1 (addn n2) (0))).
Proof.
By Move=> [|n1] n2 //=; Elim: n1 => [|n1 Hrec] /=; Rewrite: ?addn0 ?Hrec.
Qed.

Lemma mulzC : (m1, m2 : znat) (mulz m1 m2) = (mulz m2 m1).
Proof.
Move=> m1; Elim/oppz_cases: m1 => [m1 Hm1 | n1] m2.
  By Rewrite: mulz_oppl mulz_oppr Hm1.
Elim/oppz_cases: m2 => [m2 Hm2 | n2].
  By Rewrite: mulz_oppl mulz_oppr Hm2.
Rewrite: !mulz_nat; Congr Zpos.
Elim: n1 n2 => [|n1 Hrec1] /= n2; LeftBy Elim: n2 => //= [n2 []].
Rewrite: ~Hrec1; Elim: n2 => //= [n2 []]//.
By Rewrite: !addSn addnCA.
Qed.

Lemma mulzA : (m1, m2, m3 : znat) (mulz m1 (mulz m2 m3)) = (mulz (mulz m1 m2) m3).
Proof.
Move=> m1 m2 m3; Elim/oppz_cases: m1 => [m1 Hm1 | n1].
  By Rewrite: !mulz_oppl Hm1.
Elim/oppz_cases: m2 => [m2 Hm2 | n2].
  By Rewrite: mulz_oppr !mulz_oppl mulz_oppr Hm2.
Elim/oppz_cases: m3 => [m3 Hm3 | n3]; LeftBy Rewrite: !mulz_oppr Hm3.
Rewrite: !mulz_nat; Congr Zpos.
Elim: n1 n2 => [|n1 Hrec1] /= n2; LeftBy Elim: n2 => //= [n2 []].
Rewrite: {4}/addn iter_plus ~Hrec1.
By Elim: {1 3}n2 => // [n Hrec] //=; Rewrite: -addnA Hrec.
Qed.

Lemma mulzCA : (m1, m2, m3 : znat) (mulz m1 (mulz m2 m3)) = (mulz m2 (mulz m1 m3)).
Proof. By Move=> m1 m2 m3; Rewrite: !mulzA (mulzC m1). Qed.

Lemma mul1z : (m : znat) (mulz (Znat 1) m) = m. Proof. Done. Qed.
Lemma mulz1 : (m : znat) (mulz m (Znat 1)) = m.
Proof. By Move=> *; Rewrite mulzC. Qed.

Lemma mulz_addr : (m, m1, m2 : znat)
  (mulz m (addz m1 m2)) = (addz (mulz m m1) (mulz m m2)).
Proof.
Move=> m m1 m2; Elim/oppz_cases: m => [m Hm | n].
  By Rewrite: !mulz_oppl -oppz_add Hm.
Case: n => //=; Elim=> [|n Hrec] //=.
By Rewrite: Hrec -!addzA; Congr addz; Rewrite addzCA.
Qed.

Lemma leqz_pmul2l : (m, m1, m2 : znat) (posz m) ->
  (leqz (mulz m m1) (mulz m m2)) = (leqz m1 m2).
Proof.
Move=> m m1 m2 Hm; Congr negb; Rewrite: {1}/subz -mulz_oppr -mulz_addr subzI.
Rewrite: -oppz_sub; Case: m Hm {m1 m2}(subz m2 m1) => [[|n]|n] // _ [n'|n'].
  By Rewrite: mulz_oppr mulzC mulz_nat; Case n'.
By Rewrite: {mulz}lock /= -lock mulz_nat.
Qed.

(* A small theory of summations over finite subsets. *)

Section ZnatSums.

Variable d : finSet.

Definition sumz [f : d -> znat; a : (set d)] : znat :=
  (foldr [x](addz (f x)) (Znat 0) (filter a (enum d))).

Lemma sumz0 : (f : d -> znat) (sumz f set0) = (Znat 0).
Proof. By Move=> *; Rewrite: /sumz filter_set0. Qed.

Lemma eq_sumz_r : (a, b : (set d)) a =1 b ->
  (f : d -> znat) (sumz f a) = (sumz f b).
Proof. By Move=> a b Eab f; Rewrite: /sumz (eq_filter Eab). Qed.

Lemma eq_sumz_l : (f, g : d -> znat; a : (set d))
  ((x : d) (a x) -> (f x) = (g x)) -> (sumz f a) = (sumz g a).
Proof.
Move=> f g a Efg; Rewrite: /sumz; Elim: (enum d) => //= [x s Hrec].
By Case Hx: (a x) => //=; Rewrite: Hrec Efg.
Qed.

Lemma eq_sumz : (f, g : d -> znat) f =1 g -> (sumz f) =1 (sumz g).
Proof. Move=> f g Efg a; Apply: eq_sumz_l => [x _]; Apply: Efg. Qed.

Lemma sumz_sub : (f, g : d -> znat; a : (set d))
  (sumz [x](subz (f x) (g x)) a) = (subz (sumz f a) (sumz g a)).
Proof.
Move=> f g a; Rewrite: /sumz.
Elim: (filter a (enum d)) => [|x p Hrec] //=; Rewrite: Hrec.
By Rewrite: addzC addz_sub2CA addz_subA addzC addz_subA subz_sub.
Qed.

Definition zconst [n : nat] : d -> znat := [_](Zpos n).

Lemma zconstI : (n : nat) ([_](Zpos n)) = (zconst n).
Proof. Done. Qed.

Lemma sumz_const : (n : nat; a : (set d))
  (sumz (zconst n) a) = (Zpos (mult n (card a))).
Proof.
Move=> n a; Rewrite: /sumz /card count_filter mult_sym.
By Elim: {a}(filter a (enum d)) => [|x p Hrec]; Rewrite: /= ?Hrec //.
Qed.

Lemma sumz_opp : (f : d -> znat; a : (set d))
  (sumz [x](oppz (f x)) a) = (oppz (sumz f a)).
Proof.
Move=> f a; Apply: (etrans ? (etrans (sumz_sub (zconst (0)) f a) ?)).
  By Apply eq_sumz; Move=> x; Rewrite sub0z.
By Rewrite: -sub0z sumz_const /=.
Qed.

Lemma sumz_add : (f, g : d -> znat; a : (set d))
  (sumz [x](addz (f x) (g x)) a) = (addz (sumz f a) (sumz g a)).
Proof.
Move=> f g a;  Apply: (etrans ? (etrans (sumz_sub f [x](oppz (g x)) a) ?)).
  By Apply eq_sumz; Move=> x; Rewrite: /subz oppz_opp.
By Rewrite: sumz_opp /subz oppz_opp.
Qed.

Lemma sumz_setID : (b : (set d); f : d -> znat; a : (set d))
  (sumz f a) = (addz (sumz f (setI a b)) (sumz f (setD a b))).
Proof.
Move=> b f a; Rewrite: /sumz; Elim: (enum d) => [|x p Hrec] //=.
Rewrite: {1}/setD andbC {1}/setI /id; Case (a x); Rewrite: //= Hrec.
By Case (b x); Rewrite: /= -?addzA -?(addzCA (f x)).
Qed.

Lemma sumz_set1 : (f : d -> znat; x : d) (sumz f (set1 x)) = (f x).
Proof.
Move=> f x; Move: (count_set1_enum x) (filter_enum (set1 x) x).
Rewrite: /sumz count_filter.
Case: (filter (set1 x) (enum d)) => [|y[|z p]] // _.
By Rewrite: /= set11 /setU1 orbF addz0; Move/eqP=> Dy; Rewrite Dy.
Qed.

Lemma sumz_roots : (e : (rel d)) (connect_sym e) -> (f : d -> znat) 
  (sumz [x](sumz f (connect e x)) (roots e)) = (sumz f d).
Proof.
Move=> e He f; Pose a := (!setA d); Rewrite: (sumz_setID a) addzC.
Rewrite: -(!eq_sumz_r set0) // sumz0 add0z.
Step Ha: (closed e a) By Done.
Elim: {a}(S (card a)) {-2}a (ltnSn (card a)) Ha => [|n Hrec] a //.
Case: (pickP a) => [x Hx | Ha0] Hn Ha.
  Rewrite: (sumz_setID (set1 (root e x))) (sumz_setID (connect e x) f a).
  Congr addz.
    Apply: (etrans (eq_sumz_r ? ?) (etrans (sumz_set1 ? (root e x)) ?)).
      Move=> y; Rewrite: /setI andbC; Case: ((root e x) =P y) => // [[]].
      By Rewrite: (roots_root He) /= -(closed_connect Ha (connect_root e x)).
    Apply: eq_sumz_r => [y]; Rewrite: -(same_connect He (connect_root e x)).
    Rewrite: /setI andbC; Case Hxy: (connect e x y); RightDone.
    By Rewrite: -(closed_connect Ha Hxy).
  Apply: (etrans (eq_sumz_r ? ?) (Hrec ? ? ?)).
      Move=> y; Rewrite: /setD /setI.
      Case Hy: (roots e y); Rewrite: /= ?andbF //.
      By Rewrite: -{1 y}(eqP Hy) (sameP eqP (rootPx He x y)).
    Rewrite: ltnS -(cardIC (connect e x)) in Hn.
    Apply: (leq_trans ? Hn); Rewrite: -add1n; Apply leq_add2.
      Rewrite: ltnNge leqn0; Apply/set0Pn; Exists x.
      By Rewrite: /setI Hx connect0.
    By Apply: subset_leq_card; Apply/subsetP=> [y]; Rewrite: /setD andbC.
  Move=> y z Hyz; Rewrite: /setD (Ha ? ? Hyz) !(He x).
  By Rewrite: (same_connect He (connect1 Hyz)).
Rewrite: (eq_sumz_r Ha0) -(!eq_sumz_r set0) ?sumz0 //.
By Move=> y; Rewrite: /setI Ha0 andbF.
Qed.

Lemma posz_sum : (f : d -> znat; a : (set d))
  (posz (sumz f a)) -> (EX x | (a x) & (posz (f x))).
Proof.
Move=> f a; Rewrite: /sumz; Elim: (enum d) => [|x p Hrec] //=.
By Case Hx: (a x) => //=; Case/posz_add; LeftBy Exists x.
Qed.

Lemma sumz_perm : (h : d -> d) (injective h) ->
                  (a : (set d)) (fclosed h a) ->
  (f : d -> znat) (sumz [x](f (h x)) a) = (sumz f a).
Proof.
Move=> h Hh a Ha f; Pose ea := (filter a (enum d)).
Step Ea: a =1 (maps h ea).
  Move=> x; Apply/idP/mapsP=> [Hx | [y Hy []]].
    Exists (finv h x); RightBy Apply f_finv.
    By Rewrite: /ea filter_enum (fclosed1 Ha) f_finv.
  By Move: Hy; Rewrite: /ea filter_enum (fclosed1 Ha).
Rewrite: ~{Ha Ea}(eq_sumz_r Ea f) {1}/sumz -/ea. 
Step Uea: (uniq ea) By Exact (uniq_filter ? (uniq_enum d)).
Elim: {a}ea Uea => [|x p Hrec]; Rewrite: /= ?sumz0 //.
Move/andP=> [Hx Up]; Rewrite: ~{Hrec Up}(Hrec Up).
Apply: (etrans ? (esym (sumz_setID (set1 (h x)) ? ?))); Congr addz.
  Rewrite: -(!eq_sumz_r (set1 (h x))) ?sumz_set1 // /setU1 /setI.
  By Move=> y; Case ((h x) =d y); Rewrite: ?andbF.
Apply: eq_sumz_r=> [y]; Rewrite: /setD /setU1.
By Case: ((h x) =P y) => [[]|_]; LeftBy Rewrite: (mem_maps Hh) (negbE Hx).
Qed.

End ZnatSums.

Unset Implicit Arguments.
