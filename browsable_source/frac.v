(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require tacticext.
Require boolprop.
Require funs.
Require dataset.
Require natprop.
Require znat.

Set Implicit Arguments.

(* The rationals, used only for constructing the reals and    *)
(* proving that the real axioms are categorical. We don't use *)
(* setoid rewriting here, because most identities are strict. *)

(* Scale factor product.                                      *)

Definition muld [n1, n2 : nat] : nat := (addn n1 (iter n1 (addn n2) n2)).

Lemma mul0d: (n : nat) (muld (0) n) = n. Proof. Done. Qed.
Lemma muld0 : (n : nat) (muld n (0)) = n. Proof. By Elim=> // *; Congr S. Qed.

Lemma muldC : (n1, n2 : nat) (muld n1 n2) = (muld n2 n1).
Proof.
Move=> n1; Rewrite: /muld; Elim=> /= [|n2 Hrec]; LeftBy Apply: muld0.
Rewrite: addnCA addSn -~Hrec-addSn; Congr addn.
By Elim: n1 => //= [n1 Hrec]; Rewrite: Hrec addnCA !addSn addnS.
Qed.

Lemma muldA : (n1, n2, n3 : nat) (muld n1 (muld n2 n3)) = (muld (muld n1 n2) n3).
Proof.
Rewrite: {-2}/muld; Move=> n1 n2 n3; Elim: n1 => //= [n1 Hrec]; Rewrite: addnI.
Rewrite: addSn addnCA ~Hrec -!addnA addnCA -addSn; Congr addn.
Rewrite: (addnCA n1) !iter_plus addnCA /muld -!addnA; Do 2 NatCongr.
By Elim: {1 4}n2 => //= [n []]; Rewrite: -addnA.
Qed.

(* integer scaling *)

Definition scalez [d : nat; m : znat] : znat := (iter d (addz m) m).

Lemma scalez_pos : (d, n : nat) (scalez d (Zpos n)) = (Zpos (iter d (addn n) n)).
Proof. By Move=> d n; Elim: d => //= [d Hrec]; Rewrite Hrec. Qed.

Lemma scalez0 : (d : nat) (scalez d (Znat 0)) = (Znat 0).
Proof. By Elim=> //= [d Hrec]; Rewrite Hrec. Qed.

Lemma scalez_opp : (d : nat; m : znat) (scalez d (oppz m)) = (oppz (scalez d m)).
Proof. By Move=> d m; Elim: d => //= [d Hrec]; Rewrite: Hrec -oppz_add. Qed.

Lemma scalez_add : (d : nat; m1, m2 : znat)
  (scalez d (addz m1 m2)) = (addz (scalez d m1) (scalez d m2)).
Proof.
Move=> d m1 m2; Elim: d => //= [d Hrec]; Rewrite: Hrec -!addzA.
Congr addz; Apply addzCA.
Qed.

Lemma leqz_scale : (d : nat; m1, m2 : znat)
  (leqz (scalez d m1) (scalez d m2)) = (leqz m1 m2).
Proof.
Move=> d m1 m2; Rewrite: /leqz /subz -!scalez_opp -scalez_add !subzI -oppz_sub.
Case: {m1 m2}(subz m2 m1) => [[|n]|n]; Try By Rewrite: /= scalez0.
  By Rewrite: scalez_opp scalez_pos; Case d.
By Rewrite: /= scalez_pos; Case d.
Qed.

Lemma scalez_scale : (d1, d2 : nat; m : znat)
  (scalez d1 (scalez d2 m)) = (scalez (muld d1 d2) m).
Proof.
Move=> d1 d2 m; Rewrite: /scalez /muld; Elim: d1 => //= [d1 Hrec].
Rewrite: !addnI ~Hrec addnCA; Elim: {1 4}d2 => //= [d Hrec].
By Rewrite: !addnI -~Hrec addzA.
Qed.

(* Fractions                                                             *)

Inductive frac : Set := Frac : nat -> znat -> frac.

Definition leqf [f1, f2 : frac] : bool :=
  let (d1, m1) = f1 in let (d2, m2) = f2 in
  (leqz (scalez d2 m1) (scalez d1 m2)).

Definition ltf [f1, f2 : frac] : bool := (negb (leqf f2 f1)).

Lemma ltfNge : (f1, f2 : frac) (ltf f1 f2) = (negb (leqf f2 f1)). Proof. Done. Qed.
Lemma leqfNgt : (f1, f2 : frac) (leqf f1 f2) = (negb (ltf f2 f1)).
Proof. By Move=> *; Rewrite: /ltf negb_elim. Qed.

Definition eqf [f1, f2 : frac] : bool :=
  (andb (leqf f1 f2) (leqf f2 f1)).

Lemma leqff : (f : frac) (leqf f f). Proof. Move=> [d m]; Apply: leqzz. Qed.

Lemma ltff : (f : frac) (ltf f f) = false.
Proof. By Move=> *; Rewrite: /ltf leqff. Qed.

Lemma leqf_trans : (f1, f2, f3 : frac)
 (leqf f1 f2) -> (leqf f2 f3) -> (leqf f1 f3).
Proof.
Move=> [d1 m1] [d2 m2] [d3 m3] /=.
Rewrite: -(leqz_scale d3) !scalez_scale muldC; Move=> H12.
Rewrite: -(leqz_scale d1) !scalez_scale muldC; Move=> H23.
Rewrite: -(leqz_scale d2) !scalez_scale (muldC d2 d1); EApply leqz_trans; EAuto.
Qed.

Lemma leqf_lt_trans :  (f1, f2, f3 : frac)
 (leqf f1 f2) -> (ltf f2 f3) -> (ltf f1 f3).
Proof.
Move=> f1 f2 f3 Hf12 Hf23; Apply/idP=> [Hf13]; Case/idP: Hf23.
By Apply: leqf_trans Hf12.
Qed.

Lemma ltf_leq_trans :  (f1, f2, f3 : frac)
 (ltf f1 f2) -> (leqf f2 f3) -> (ltf f1 f3).
Proof.
Move=> f1 f2 f3 Hf12 Hf23; Apply/idP=> [Hf13]; Case/idP: Hf12.
By Apply: leqf_trans Hf13.
Qed.

Lemma leqf_eqVlt : (f1, f2 : frac) (leqf f1 f2) = (orb (eqf f1 f2) (ltf f1 f2)).
Proof.
By Move=> [d1 m1] [d2 m2]; Rewrite: /eqf /ltf /= -eqz_leq negb_leqz -leqz_inc.
Qed.

Lemma ltfW : (f1, f2 : frac) (ltf f1 f2) -> (leqf f1 f2).
Proof. Move=> *; Rewrite: leqf_eqVlt; Apply/orP; Auto. Qed.

Lemma leqf_cases : (f1, f2 : frac) (leqf f1 f2) \/ (ltf f2 f1).
Proof. Move=> f1 f2; Apply: orP; Apply: orb_neg_b. Qed.

Lemma leqf_eql : (f1, f2 : frac)
  (eqf f1 f2) -> (leqf f1) =1 (leqf f2).
Proof.
Move=> f1 f2; Move/andP=> [Hf12 Hf21] f3.
Apply/idP/idP=> *; EApply leqf_trans; EAuto.
Qed.

Lemma leqf_eqr : (f1, f2 : frac)
  (eqf f1 f2) -> (f3 : frac) (leqf f3 f1) = (leqf f3 f2).
Proof.
Move=> f1 f2; Move/andP=> [Hf12 Hf21] f3.
Apply/idP/idP=> *; EApply leqf_trans; EAuto.
Qed.

Lemma eqff : (f : frac) (eqf f f).
Proof. By Move=> *; Rewrite: /eqf leqff. Qed.

Lemma eqf_sym : (f1, f2 : frac) (eqf f1 f2) = (eqf f2 f1).
Proof. By Move=> *; Rewrite: /eqf andbC. Qed.

Lemma eqf_eql : (f1, f2 : frac)
  (eqf f1 f2) -> (eqf f1) =1 (eqf f2).
Proof.
By Move=> f1 f2 Ef12 f3; Rewrite: /eqf (leqf_eql Ef12) (leqf_eqr Ef12).
Qed.

Lemma eqf_eqr : (f1, f2 : frac)
  (eqf f1 f2) -> (f3 : frac) (eqf f3 f1) = (eqf f3 f2).
Proof.
By Move=> f1 f2 Ef12 f3; Rewrite: /eqf (leqf_eql Ef12) (leqf_eqr Ef12).
Qed.

Lemma eqf_trans : (f1, f2, f3 : frac) (eqf f1 f2) -> (eqf f2 f3) -> (eqf f1 f3).
Proof. By Move=> f1 f2 f3 Ef12; Rewrite: (eqf_eql Ef12). Qed.

Definition addf [f1, f2 : frac] : frac :=
  let (d1, m1) = f1 in let (d2, m2) = f2 in
  (Frac (muld d1 d2) (addz (scalez d2 m1) (scalez d1 m2))).

Definition F0 : frac := (Frac (0) (Znat 0)).
Definition F1 : frac := (Frac (0) (Znat 1)).

Definition eqf0 [f : frac] : bool :=
  if f is (Frac _ (Zpos (0))) then true else false.

Lemma eqf0I : (f : frac) (eqf f F0) = (eqf0 f).
Proof.
By Move=> [d m]; Rewrite: /eqf /= -eqz_leq scalez0; Case: m => [[|n]|n].
Qed.

Lemma addF0 : (f : frac) (addf f F0) = f.
Proof. By Move=> [d m]; Rewrite: /= scalez0 muld0 addz0. Qed.

Lemma addf0 : (f, f0 : frac) (eqf0 f0) -> (eqf (addf f f0) f).
Proof.
By Move=> [d m] [d' [[|n]|n]]; Rewrite: /eqf //= scalez0 addz0 scalez_scale leqzz.
Qed.

Lemma addfC : (f1, f2 : frac) (addf f1 f2) = (addf f2 f1).
Proof. By Move=> [d1 m1] [d2 m2] /=; Rewrite: muldC addzC. Qed.

Lemma addfA : (f1, f2, f3 : frac)
  (addf f1 (addf f2 f3)) = (addf (addf f1 f2) f3).
Proof. 
Move=> [d1 m1] [d2 m2] [d3 m3]; Rewrite: /= muldA; Congr Frac.
By Rewrite: !scalez_add !scalez_scale addzA !(muldC d3).
Qed.

Lemma addfCA : (f1, f2, f3 : frac)
  (addf f1 (addf f2 f3)) = (addf f2 (addf f1 f3)).
Proof. By Move=> f1 f2 f3; Rewrite: !addfA (addfC f1). Qed.

Lemma leqf_add2l : (f, f1, f2 : frac)
  (leqf (addf f f1) (addf f f2)) = (leqf f1 f2).
Proof.
Move=> [d m] [d1 m1] [d2 m2] /=; Rewrite: -!scalez_scale leqz_scale !scalez_add.
By Rewrite: !scalez_scale muldC leqz_add2l -!(muldC d) -!scalez_scale leqz_scale.
Qed.

Lemma leqf_add2r : (f, f1, f2 : frac)
  (leqf (addf f1 f) (addf f2 f)) = (leqf f1 f2).
Proof. By Move=> f f1 f2; Rewrite: -!(addfC f) leqf_add2l. Qed.

Lemma leqf_add2 : (f1, f2, f3, f4 : frac)
  (leqf f1 f2) -> (leqf f3 f4) -> (leqf (addf f1 f3) (addf f2 f4)).
Proof.
Move=> f1 f2 f3 f4 Hf12 Hf34.
By Apply leqf_trans with (addf f1 f4); Rewrite: ?leqf_add2l ?leqf_add2r.
Qed.

Lemma eqf_add2l : (f, f1, f2 : frac)
  (eqf (addf f f1) (addf f f2)) = (eqf f1 f2).
Proof. By Move=> *; Rewrite: /eqf !leqf_add2l. Qed.

Lemma eqf_add2r : (f, f1, f2 : frac)
  (eqf (addf f1 f) (addf f2 f)) = (eqf f1 f2).
Proof. By Move=> *; Rewrite: /eqf !leqf_add2r. Qed.

Definition oppf [f : frac] : frac := let (d, m) = f in (Frac d (oppz m)).

Lemma oppF0 : (oppf F0) = F0. Proof. Done. Qed.

Lemma addfI : (f : frac) (eqf0 (addf f (oppf f))).
Proof. By Move=> [e m]; Rewrite: /= scalez_opp addz_opp. Qed.

Lemma addf_inv : (f1, f2 : frac) (eqf (addf (oppf f1) (addf f1 f2)) f2).
Proof. Move=> *; Rewrite: addfCA addfA addfC; Apply addf0; Apply addfI. Qed.

Lemma oppf_opp : (f : frac) (oppf (oppf f)) = f.
Proof. By Move=> [d m]; Rewrite: /= oppz_opp. Qed.

Lemma oppf_add : (f1, f2 : frac) (oppf (addf f1 f2)) = (addf (oppf f1) (oppf f2)).
Proof. By Move=> [d1 m1] [d2 m2]; Rewrite: /= !scalez_opp -oppz_add. Qed.

Lemma leqf_opp2 : (f1, f2 : frac) (leqf (oppf f1) (oppf f2)) = (leqf f2 f1).
Proof. By Move=> [d1 m1] [d2 m2]; Rewrite: /= !scalez_opp leqz_opp2. Qed.

Lemma eqf_opp2 : (f1, f2 : frac) (eqf (oppf f1) (oppf f2)) = (eqf f1 f2).
Proof. By Move=> *; Rewrite: /eqf !leqf_opp2 andbC. Qed.

(* Frac multiplication. *)

Definition mulf [f1, f2 : frac] : frac :=
  let (d1, m1) = f1 in let (d2, m2) = f2 in
  (Frac (muld d1 d2) (mulz m1 m2)).

Lemma mul0f : (f0, f : frac) (eqf0 f0) -> (eqf0 (mulf f0 f)).
Proof. By Move=> [d0 [[|n]|n]] [d m]. Qed.

Lemma mul1f : (f : frac) (mulf F1 f) = f. Proof. By Case. Qed.

Lemma mulfC : (f1, f2 : frac) (mulf f1 f2) = (mulf f2 f1).
Proof. By Move=> [d1 m1] [d2 m2] /=; Rewrite: muldC mulzC. Qed.

Lemma mulfA : (f1, f2, f3 : frac) (mulf f1 (mulf f2 f3)) = (mulf (mulf f1 f2) f3).
Proof. By Move=> [d1 m1] [d2 m2] [d3 m3] /=; Rewrite: muldA mulzA. Qed.

Lemma mulF0 : (f : frac) (eqf (mulf f F0) F0).
Proof. By Move=>*; Rewrite: mulfC eqf0I mul0f. Qed.

Lemma mulf1 : (f : frac) (mulf f F1) = f.
Proof. By Move=>*; Rewrite: mulfC mul1f. Qed.

Lemma mulfCA : (f1, f2, f3 : frac) (mulf f1 (mulf f2 f3)) = (mulf f2 (mulf f1 f3)).
Proof. By Move=> f1 f2 f3; Rewrite: !mulfA (mulfC f1). Qed.

Lemma mulf_oppl : (f1, f2 : frac) (mulf (oppf f1) f2) = (oppf (mulf f1 f2)).
Proof. By Move=> [d1 m1] [d2 m2]; Rewrite: /= mulz_oppl. Qed.

Lemma mulf_oppr : (f1, f2 : frac) (mulf f1 (oppf f2)) = (oppf (mulf f1 f2)).
Proof. By Move=> [d1 m1] [d2 m2]; Rewrite: /= mulz_oppr. Qed.

Lemma scalez_mul : (d : nat; m : znat)
  (scalez d m) = (mulz (scalez d (Znat 1)) m).
Proof.
Move=> d m; Rewrite mulzC; Elim: d => [|d Hrec]; LeftBy Rewrite: mulzC.
By Rewrite: {Zpos}lock /= -lock mulz_addr mulzC -Hrec.
Qed.

Lemma mulf_addr : (f, f1, f2 : frac)
  (eqf (mulf f (addf f1 f2)) (addf (mulf f f1) (mulf f f2))).
Proof.
Move=> [d m] [d1 m1] [d2 m2]; Rewrite: /eqf /= muldA -(muldC d) -!muldA muldC.
Rewrite: -!scalez_scale -scalez_add !leqz_scale -eqz_leq.
Rewrite: ![d'; m'](scalez_mul d' (mulz m m')) -!(mulzCA m) -!scalez_mul.
By Rewrite: mulz_addr set11.
Qed.

Lemma mulf_addl : (f, f1, f2 : frac)
  (eqf (mulf (addf f1 f2) f) (addf (mulf f1 f) (mulf f2 f))).
Proof. By Move=> f *; Rewrite: -!(mulfC f) mulf_addr. Qed.

Definition F2 : frac := (addf F1 F1).

Lemma mulF2 : (f : frac) (eqf (mulf F2 f) (addf f f)).
Proof. By Move=> f; Rewrite: -{2 3 f}mul1f; Apply: mulf_addl. Qed.

Definition nnegf [f : frac] : bool :=
  if f is (Frac _ (Zpos _)) then true else false.

Lemma nnegfI : (f : frac) (leqf F0 f) = (nnegf f).
Proof. By Move=> [d [[|n]|n]] /=; Rewrite: scalez0. Qed.

Lemma oppf_cases : (P : frac -> Prop)
  ((f : frac) (nnegf f) -> (and (P f) -> (P (oppf f)) (P f))) -> 
  (f : frac) (P f).
Proof.
Move=> P Hrec [d [n|n]]; LeftBy Case (Hrec (Frac d (Zpos n))).
By Case (Hrec (Frac d (Zpos (S n)))); Simpl; Auto.
Qed.

Definition posf [f : frac] : bool := (negb (nnegf (oppf f))).

Lemma posfI : (f : frac) (ltf F0 f) = (posf f).
Proof. By Move=> *; Rewrite: /ltf -leqf_opp2 oppF0 nnegfI. Qed.

Lemma nposfI : (f : frac) (leqf f F0) = (negb (posf f)).
Proof. By Move=> *; Rewrite: leqfNgt posfI. Qed.

Lemma nnegf_0Vpos : (f : frac) (nnegf f) = (orb (eqf0 f) (posf f)).
Proof. By Case=> [d [[|n]|n]]. Qed.

Lemma posf_n0Anneg : (f : frac) (posf f) = (andb (negb (eqf0 f)) (nnegf f)).
Proof. By Case=> [d [[|n]|n]]. Qed.

Lemma posf_opp : (f : frac) (posf (oppf f)) = (negb (nnegf f)).
Proof. By Case=> [e [[|n]|n]]. Qed.

Lemma nnegf_opp : (f : frac) (nnegf (oppf f)) = (negb (posf f)).
Proof. By Case=> [d [[|n]|n]]. Qed.

Lemma leqf_pmul2l : (f : frac) (posf f) ->
  (f1, f2 : frac) (leqf (mulf f f1) (mulf f f2)) = (leqf f1 f2).
Proof.
Move=> [d m] /= Hm [d1 m1] [d2 m2] /=; Rewrite: -!scalez_scale leqz_scale.
Rewrite: scalez_mul (scalez_mul d1) -!(mulzCA m) -!scalez_mul leqz_pmul2l //.
By Case: m Hm; Case.
Qed.

Lemma eqf_mul2l : (f, f1, f2 : frac) (eqf f1 f2) -> (eqf (mulf f f1) (mulf f f2)).
Proof.
Move=> f f1 f2 Ef12; Elim/oppf_cases: f => [f Hf]; Split.
  By Rewrite: !mulf_oppl eqf_opp2.
Rewrite: nnegf_0Vpos in Hf; Case/orP: Hf => [Hf].
  By Apply eqf_trans with F0; Rewrite: ?eqf0I 1?eqf_sym ?eqf0I mul0f.
By Rewrite: /eqf !leqf_pmul2l.
Qed.

Lemma eqf_mul2r : (f, f1, f2 : frac) (eqf f1 f2) -> (eqf (mulf f1 f) (mulf f2 f)).
Proof. By Move=> f *; Rewrite: -!(mulfC f) eqf_mul2l. Qed.

Lemma posf_pmull : (f1, f2 : frac) (posf f1) -> (posf (mulf f1 f2)) = (posf f2).
Proof.
By Move=> f1 f2 Hf1; Rewrite: -!posfI /ltf -(leqf_eqr (mulF0 f1)) leqf_pmul2l.
Qed.

(* Inverse.                                                                *)

Definition invf [f : frac] : frac :=
  Cases f of
    (Frac _ (Zpos (0))) => f
  | (Frac d (Zpos (S n))) => (Frac n (Zpos (S d)))
  | (Frac d (Zneg n)) => (Frac n (Zneg d))
  end.

Lemma invf_inv : (f : frac) (invf (invf f)) = f.
Proof. By Move=> [d [[|n]|n]]. Qed.

Lemma invf_opp : (f : frac) (invf (oppf f)) = (oppf (invf f)).
Proof. By Move=> [d [[|n]|n]]. Qed.

Lemma mulfI : (f : frac) (negb (eqf0 f)) -> (eqf (mulf f (invf f)) F1).
Proof.
Elim/oppf_cases=> [[d [[|n]|n]]] // _; Split; Try Done.
  By Rewrite: mulf_oppl invf_opp mulf_oppr oppf_opp.
Clear; Rewrite: /eqf /= -eqz_leq muldC; Apply/eqP.
Move: (scalez_mul (muld n d) (Znat 1)); Rewrite: mulzC -scalez_scale /=; Case.
By Congr (scalez n); Rewrite: scalez_pos; Congr Zpos; Elim: d => // *; Congr S.
Qed.

Lemma pmulf_inv : (f1, f2 : frac) (posf f1) -> 
  (eqf (mulf (invf f1) (mulf f1 f2)) f2).
Proof.
Move=> f1 f2; Rewrite: posf_n0Anneg; Case/andP; Move/mulfI=> Ef1 _.
By Move: (eqf_mul2r f2 Ef1); Rewrite: mul1f (mulfC f1) mulfA.
Qed.

Lemma posf_inv : (f : frac) (posf (invf f)) = (posf f).
Proof. By Move=> [d [[|n]|n]]. Qed.

Lemma nnegf_inv : (f : frac) (nnegf (invf f)) = (nnegf f).
Proof. By Move=> [d [[|n]|n]]. Qed.

Lemma frac_dense : (f1, f3 : frac)
  (ltf f1 f3) -> {f2 : frac | (ltf f1 f2) & (ltf f2 f3)}.
Proof.
Step Ef2: (f : frac) (eqf f (mulf (invf F2) (addf f f))).
  By Move=> f; Rewrite: -[H](eqf_eql (!pmulf_inv F2 f H)) // eqf_mul2l // mulF2.
Move=> f1 f3 Hf13; Exists (mulf (invf F2) (addf f1 f3)).
  By Rewrite: /ltf (leqf_eqr (Ef2 f1)) leqf_pmul2l // leqf_add2l.
By Rewrite: /ltf (leqf_eql (Ef2 f3)) leqf_pmul2l // leqf_add2r.
Qed.

Unset Implicit Arguments.


 
