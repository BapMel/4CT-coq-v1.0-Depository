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
Require znat.
Require hypermap.
Require geometry.
Require part.

Set Implicit Arguments.

(* Discharging arities to neighboring faces. This file contains the data for *)
(* the 32 (37 after disambiguation) rules, functions for constructing a      *)
(* symmetrical rule database, and for computing its converse.                *)
(* It contains the proof that after discharging, some dart has a positive    *)
(* score.                                                                    *)

Definition drules : Set := (seq partData).

Definition drule1  : part := (Part * * 6+ * *).

Definition drule2  : part := (Part * 5 7+ * *).
Definition drule2' : part := (Part * 5 7+ * * *).

Definition drule3  : part := (Part 5 -6 6+ * *).
Definition drule3' : part := (Part 5 -6 6+ * * *).

Definition drule4  : part := (Part -6 [5] 5 6+ * * *).
Definition drule4' : part := (Part -6 [5] 6 6+ * * *).

Definition drule5  : part := (Part 6 [-6 5] 6 6+ * * *).

Definition drule6  : part := (Part 6 [-6] 5 [5] 7+ * * *).

Definition drule7  : part := (Part 6 [6 -6] 6 [5] 7+ * * *).

Definition drule8  : part := (Part 5 -6 7+ * * * *).

Definition drule9  : part := (Part -6 -6 7+ * * * 5).

Definition drule10 : part := (Part 5 5 7+ 5 6+ * *).
Definition drule10': part := (Part 5 5 7+ 5 5 * *).

Definition drule11 : part := (Part 6 [5] 5 7+ 5 6+ * *).

Definition drule12 : part := (Part 5 [5] 5 7+ 5 [5] 5 * *).

Definition drule13 : part := (Part 6 [5] 5 [5] 8+ 5 5 * *).

Definition drule14 : part := (Part 5 [5] 6 7+ 5 * * *).

Definition drule15 : part := (Part 5 6 7+ 5 7+ 5 6).

Definition drule16 : part := (Part 6 6 7+ 5 5 5 6).

Definition drule17 : part := (Part 5 [6] 6 7+ 5 5 7+ 5).

Definition drule18 : part := (Part 6 [5] 5 [5] 7 6+ * * 5).

Definition drule19 : part := (Part 6 6+ 8+ [5] 5 [5] 6 5 6).

Definition drule20 : part := (Part 5 6 7+ 6 6 5 5).

Definition drule21 : part := (Part -6 6 [5] 7 6+ * 5 5).

Definition drule22 : part := (Part 5 6 [5] 7 6+ * 5 6).

Definition drule23 : part := (Part 5 [5] 7 7+ 5 * * *).

Definition drule24 : part := (Part 5 5 [5] 7 7+ 6 6 5).

Definition drule25 : part := (Part 5 5 7+ [* * 5] 7 [6] 5 5 *).

Definition drule26 : part := (Part 6 6 [5] 7 7+ 5 5 6).

Definition drule27 : part := (Part 7+ 6 [6 5 6+] 7 7 [5] -6 * *).

Definition drule28 : part := (Part 5 5 7+ 5 5 * * 5).

Definition drule29 : part := (Part 5 [5] 5 7+ 5 * * 5 5).

Definition drule30 : part := (Part 5 5 7+ 5 [5] 6 5 * *).

Definition drule31 : part := (Part 5 [5] 5 7+ 5 [6+] 5 6+ * 6+).
Definition drule31': part := (Part 5 [5] 5 7+ 5 [5] 5 6+ * 6+).

Definition drule32 : part := (Part 5 6 [5] 7 7+ 6 5 5 5).

Definition base_drules : drules :=
  (Seq drule1  drule1  drule2  drule2' drule3   drule3' drule4   drule4'
       drule5  drule6  drule7  drule8  drule9   drule10 drule10' drule11
       drule12 drule13 drule14 drule15 drule16  drule17 drule18  drule19 
       drule20 drule21 drule22 drule23 drule24  drule25 drule26  drule27 
       drule28 drule29 drule30 drule31 drule31' drule32).

Fixpoint symmetrize_drules [r : drules] : drules :=
  if r is (Adds p r') then
    let p' = (iter (5) (rot_part (pred (size_part p))) (mirror_part p)) in
    let psr = (Adds p (symmetrize_drules r')) in
    if (cmp_part p p') is Psubset then psr else (Adds p' psr)
  else r.

Definition the_drules : drules := (symmetrize_drules base_drules).

Section Discharge.

Variable g : hypermap.

Definition dscore1 [x : g] : znat :=
  (Zpos (count (exact_fitp (inv_face2 x)) the_drules)).

Definition dscore2 [x : g] : znat := (subz (dscore1 (edge x)) (dscore1 x)).

Definition dscore [x : g] : znat :=
  (addz (subz (Znat 60) (Zpos (mult (10) (arity x)))) (sumz dscore2 (cface x))).

Lemma dscore_cface : (x, y : g) (cface x y) -> (dscore x) = (dscore y).
Proof.
By Move=> x y Hxy; Rewrite: /dscore (arity_cface Hxy) (eq_sumz_r (same_cface Hxy)).
Qed.

End Discharge.

Syntax constr level 0:
  pp_dscore  [(dscore 1!$_)]  -> ["dscore"]
| pp_dscore1 [(dscore1 1!$_)] -> ["dscore1"]
| pp_dscore2 [(dscore2 1!$_)] -> ["dscore2"].

Grammar constr constr0 : constr :=
  map_dscore  ["dscore"]  -> [(!dscore ?)]
| map_dscore1 ["dscore1"] -> [(!dscore1 ?)]
| map_dscore2 ["dscore2"] -> [(!dscore2 ?)].

Section DischargePlanar.

Variable g : hypermap.

Hypothesis Hg : (planar_plain_cubic_connected g).
Local De2 := (plain_eq Hg).
Local Dn3 := (cubic_eq Hg).

Lemma dscore_roots : (!sumz g dscore (froots face)) = (Znat 120).
Proof.
Pose ds3 := [x : g](sumz [y : g](subz (dscore2 y) (zconst (10) y)) (cface x)).
Transitivity (sumz [x](addz (zconst (60) x) (ds3 x)) (froots face)).
  By Apply: eq_sumz => [x]; Rewrite: /ds3 sumz_sub sumz_const addz_subCA addzC.
Rewrite: sumz_add ~/ds3 (sumz_roots (Sface g)) sumz_sub !sumz_const.
Move: (Hg :: (planar g)); Rewrite: (cubic_Euler Hg) /n_comp.
Rewrite: -(!eq_card g (froots face)); RightBy Move=> y; Rewrite: /setI andbT. 
Move/eqP=> Eg; Rewrite: -{1 (60)}/(mult (10) (6)) -mult_assoc_l ~Eg.
Rewrite: /addn mult_plus_distr_r addnI zpos_addn addz_subCA subz_add /= /dscore2.
By Rewrite: (sumz_sub [x : g](dscore1 (edge x))) (sumz_perm (Iedge g)) // subzz.
Qed.

Lemma posz_dscore : (EX x : g | (posz (dscore x))).
Proof.
Case: (!posz_sum g dscore (froots face)); LeftBy Rewrite dscore_roots.
By Move=> x *; Exists x.
Qed.

Lemma dscore_mirror : (x : g) (!dscore (mirror g) x) = (dscore x).
Proof.
Move=> x; Rewrite: /dscore arity_mirror (eq_sumz_r (cface_mirror x)); Congr addz.
Cut (y : g) (!dscore1 (mirror g) (face y)) = (dscore1 y).
  Move=> Es1x; Rewrite: -(sumz_perm (Iface g)).
    Apply eq_sumz; Move=> y; Rewrite: /dscore2.
    By Rewrite: {dscore1}lock /= -lock /comp !Es1x (plain_eq' Hg).
  By Move=> y z Dz; Rewrite: cface1r (eqP Dz).
Move {x}=> x; Rewrite: /dscore1 /the_drules; Congr Zpos.
Elim: {}base_drules => [|p r Hrec] //; Pose n := (size_part p).
Pose rp := [i](iter i (rot_part (pred n)) (mirror_part p)).
Step Erp : (i : nat) (size_part (rp i)) = n.
  By Elim=> /= *; Rewrite: ?size_rot_part ?size_mirror_part.
Step Hrp: (i : nat; g' : hypermap; x' : g')
    (exact_fitp x' (rp i)) = (exact_fitp (iter i face x') (mirror_part p)).
  Elim{Hrec}=> //= [i Hrec] g' x'; Case Hx': ((arity x') =d n).
    Rewrite: -arity_face in Hx'; Rewrite: /= -{1 x'}(finv_f (Iface g')) /finv.
    By Rewrite: (eqP Hx') -fitp_rot ?Hrec ?iter_f // Erp -subn1 leq_subr.
  Rewrite: /exact_fitp size_rot_part Erp arity_face arity_iter_face.
  By Rewrite: size_mirror_part -/n Hx'.
Def Dp': p' := (rp (5)); Move: Dp' (Hrp (5)) (Erp (5)) {Hrp Erp} => /= [] Hp' Ep'.
Pose x2' := (inv_face2 x); Pose x3 := (face (face (face x))).
Step Ex3: x3 = (iter (5) face x2') By Rewrite: /x2' /inv_face2 /= !Enode.
Simpl in Hrec Ex3; Case Hpp': (cmp_part p p') => //=;
  Rewrite: ~Hrec /comp ?(f_finv (Inode g)) -/x2' -/x3;
  Try By Rewrite: !Hp' // -Ex3 {1 x3}Ex3 /= ?(finv_f (Iface g));
         Rewrite: -?(fitp_mirror Hg) mirror_mirror_part addnCA.
Congr [b : bool](addn b ?); Apply/idP/idP; Move/andP=> [Exp Hxp].
  Step Hxp': (!exact_fitp (mirror g) x3 p').
    By Rewrite: /exact_fitp (fitp_cmp Hxp) Hpp' /= andbT Ep'.
  Move: Hxp'; Rewrite: Hp' Ex3 /= !(finv_f (Iface g)) -(fitp_mirror Hg).
  By Rewrite mirror_mirror_part.
By Rewrite: -(fitp_mirror Hg) Ex3 -Hp' /exact_fitp (fitp_cmp Hxp) Hpp' andbT Ep'.
Qed.

End DischargePlanar.

Section ScoreBound.

Variable nhub : nat. (* hub size *)

(* Rule selectors, by source or target arity, or by matching a part. The *)
(* "target arity" returns a list of converse rules. The "matching"       *)
(* selector returns a pair of the number of rules that are forced by the *)
(* part, plus the list of rules that straddle the part, discarding the   *)
(* rules that are disjoint from or forced by the part. The matching      *)
(* selector is part of the inner loop of the unavoidability computation. *)

Definition pick_source_drules : drules -> drules :=
  (filter [p](size_part p) =d nhub).

Fixpoint pick_target_drules [r : drules] : drules :=
  if r is (Adds p r') then
    let (u, p') = (converse_part p) in
    let tr = (pick_target_drules r') in
    if (u nhub) then (Adds p' tr) else tr
  else r.

Section SortDrules.

Record sort_drules_result : Set :=
  SortDrulesResult {
    nb_forced_drules :> nat;
    straddling_drules :> drules
  }.

Variable p : part.

Fixpoint sort_drules_rec [n : nat; rs, r : drules] : sort_drules_result :=
  if r is (Adds p' r') then
    Cases (cmp_part p p') of
      Psubset => (sort_drules_rec (S n) rs r')
    | Pstraddle => (sort_drules_rec n (Adds p' rs) r')
    | Pdisjoint => (sort_drules_rec n rs r')
    end
  else (SortDrulesResult n rs).

Definition sort_drules [r : drules] : sort_drules_result :=
  (sort_drules_rec (0) seq0 r).

End SortDrules.

(* A rule fork specializes the full set of discharge rules for a specific *)
(* hub size, so that the source/target arity selection is only performed  *)
(* once. We use a dependent predicate to specify the computation.         *)

Inductive drule_fork_values : drules -> drules -> Prop :=
  DruleForkValues : (drule_fork_values (pick_source_drules the_drules)
                                       (pick_target_drules the_drules)).
Record drule_fork : Set :=
  DruleFork {
    source_drules : drules;
    target_drules : drules;
    drule_fork_values_def : (drule_fork_values source_drules target_drules)
  }.

Variable rf : drule_fork.
Local rs : drules := (source_drules rf).
Local rt : drules := (target_drules rf).

Variable g : hypermap.
Hypothesis Hg : (plain_cubic_pentagonal g).
Local HgF : (pentagonal g) := Hg.
Local De2 := (plain_eq Hg).
Local Dn3 := (cubic_eq Hg).

Section BoundDart.

Definition dbound1 [r : drules; x : g] : nat := (count (fitp x) r).

Definition dbound2 [r, r' : drules; x : g] : znat :=
  (subz (Zpos (dbound1 r x)) (Zpos (dbound1 r' x))).

Definition dboundK : znat :=
  if (subn nhub (5)) is (S n) then (zneg (mult n (10))) else (Znat 10).

Variable x : g; (* hub *) p : part (* for sort_drules *).
Hypotheses Hxn : (arity x) = nhub; Hpn : (size_part p) = nhub; Hxp : (fitp x p).

Lemma dbound1_eq : (dscore1 (face (face x))) = (Zpos (dbound1 rs x)).
Proof.
Congr Zpos; Rewrite: /rs /source_drules; Case: {}rf => [rs' rt' []] {rs' rt'}.
Elim: {}the_drules=> //= [r dr Hrec].
Rewrite: ~Hrec /exact_fitp /inv_face2 !Eface Hxn eqd_sym.
By Case ((size_part r) =d nhub).
Qed.
 
Lemma sort_dbound1_eq : (ru : drules) let rup = (sort_drules p ru) in
  (dbound1 ru x) = (addn rup (dbound1 rup x)).
Proof.
Move=> ru; Apply: (etrans (esym (addn0 ?))); Rewrite: /sort_drules.
Rewrite: -{1 (0)}/(addn (0) (count (fitp x) seq0)).
Elim: ru (0) (seq0::drules) => //= [r ru Hrec] m ru'.
Rewrite: (fitp_cmp Hxp); Case Hpr: (cmp_part p r) => //=.
  By Rewrite: -Hrec /= -!addnA; Repeat NatCongr.
By Rewrite: -Hrec /= !addSn addnS.
Qed.

Inductive sort_drules_spec [r : drules] : sort_drules_result -> nat -> Set :=
  SortDrulesSpec : (n : nat; r' : drules)
    (sort_drules_spec r (SortDrulesResult n r') (addn n (dbound1 r' x))).

Lemma sort_drulesP : (r : drules)
  (sort_drules_spec r (sort_drules p r) (dbound1 r x)).
Proof. By Move=> r; Rewrite: sort_dbound1_eq; Case (sort_drules p r). Qed.

Lemma dbound2_leq : (leqz (dscore2 (face (face x))) (dbound2 rt rs x)).
Proof.
Rewrite: /dbound2 -dbound1_eq /dscore2 /subz leqz_add2r /dscore1 /dbound1 leqz_nat.
Pose y := (inv_face2 (edge (face (face x)))).
Rewrite: /rt /target_drules; Case: {}rf => [rs' rt' []] {rs' rt'}.
Elim: {}the_drules=> //= [r dr Hrec].
Case Dr': (converse_part r) => [u r'].
Case Hyr: (exact_fitp y r).
  Move: (fitp_converse Hg Hyr); Rewrite Dr'; Case/andP.
  Rewrite: {1 2}/y /inv_face2 !Enode De2 !Eface Hxn.
  By Move=> Hu Hr'; Rewrite: Hu /= Hr'.
By Case: (u nhub) => //=; Case: (fitp x r') => //; Apply ltnW.
Qed.

Lemma dboundK_eq : dboundK = (subz (Znat 60) (Zpos (mult (10) (arity x)))).
Proof.
Rewrite:  -(leq_add_sub (HgF x)) Hxn /dboundK.
Case: (subn nhub (5)) => // [m].
Rewrite: -addSnnS /addn mult_plus_distr_r addnI zpos_addn -oppz_sub subz_add.
By Rewrite: (mult_sym (10)); Case m.
Qed.

End BoundDart.

Lemma dscore_cap1 :
  (m : nat; Hm : (y : g) (leqz (dscore1 y) (Zpos m)))
  (x : g) (posz (dscore x)) ->
  (d : nat) (leq (60) (mult (subn (10) m) d)) -> (ltn (arity x) d).
Proof.
Move=> m Hm x Hx d Hdm; Rewrite: ltnNge; Apply/idP=> [Hdx]; Case/idPn: Hx.
Step H60: (leqz (Znat 60) (Zpos (mult (subn (10) m) (arity x)))).
  Rewrite: leqz_nat; Apply: (leq_trans Hdm).
  By Rewrite: -(leq_add_sub Hdx) /addn mult_plus_distr_r addnI leq_addr.
Rewrite: /dscore addzC addz_subCA -oppz_sub; Apply: (leqz_trans H60); Apply/idP.
Rewrite: /order -!sumz_const -!sumz_sub; Case/posz_sum=> [y _]; Apply: negP.
Step Hm10: (ltn m (10)) By Rewrite: ltn_lt0sub; Case: (subn (10) m) Hdm.
Rewrite: /zconst -{2 (10)}(leq_add_sub (ltnW Hm10)) zpos_addn -oppz_sub subz_sub.
Rewrite: subz_add2r /dscore2 oppz_sub subz_sub {2}/dscore1 -zpos_addn {Zpos}lock.
By Apply: (leqz_trans (Hm ?)); Rewrite: -lock leqz_nat leq_addl.
Qed.

Lemma source_drules_range : (negb (Pr58 nhub)) -> rs = seq0.
Proof.
Move=> Hu; Rewrite: /rs /source_drules; Case: {}rf => [rs' rt' []] {rs' rt'}.
Step Eu: ([p](size_part p) =d nhub) =1
   (comp [n](andb (negb (Pr58 n)) n =d nhub) size_part).
  Move=> p; Rewrite: /comp andbC; Case: ((size_part p) =P nhub) => // [Ep].
  By Rewrite Ep.
By Rewrite: /pick_source_drules (eq_filter Eu).
Qed.

Lemma dscore_cap2 :
  (x : g) (arity x) = nhub -> (posz (dscore x)) ->
    (posz (addz dboundK (sumz (dbound2 rt rs) (cface x)))).
Proof.
Move=> x Hxn; Rewrite: -!leq1z; Apply: [H](leqz_trans H ?).
Rewrite: /dscore -dboundK_eq // leqz_add2l.
Rewrite: -2!(sumz_perm (Iface g) (connect_closed (Sface g) x)).
Rewrite: /leqz -sumz_sub; Apply/idP; Case/posz_sum=> [y Hxy]; Apply: negP.
Def Da: a := (dscore2 (face (face y))); Def Db: b := (dbound2 rt rs y).
By Rewrite: (arity_cface Hxy) in Hxn; Move: (dbound2_leq Hxn); Rewrite: -Da -Db.
Qed.

End ScoreBound.

Unset Implicit Arguments.
