(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require tacticext.
Require boolprop.
Require funs.
Require dataset.
Require natprop.
Require seq.
Require paths.
Require znat.
Require grid.

Set Implicit Arguments.

(* Mattes are finite sets of grid squares that are delimited by a simple grid  *)
(* ring; we explicitly include the enumeration of the region and the ring.     *)
(* Mattes will be used to define conservative approximations of aribitrary     *)
(* connected open sets of points (regions). We therefore need to provide       *)
(* operations for extending a matte in order to improve the approximation.     *)
(* This involves three different operations :                                  *)
(*   - adding pixels within a specified rectangle that the matte meets, so     *)
(*     that a specific pixel is covered.                                       *)
(*   - adding the pixels surrounding a grid point of the matte boundary.       *)
(*   - refining the grid to ensure that the two previous operations are safe.  *)
(* Note that we can't add large rectangle blindly to a matte if we want to     *)
(* preserve its geometrical properties (we might end up with a disconnected    *)
(* contour). We reduce the first two operations above to two primitives, which *)
(* add a pixel that has exactly one or two consecutive sides in common with    *)
(* the matte, respectively (more precisely, 2 or 3 consecutive vertices in     *)
(* common with the matte contour vertices). We don't actually provide the      *)
(* second operation here, because it requires multiple grid refinement.        *)
(* Instead we provide a basic step that needs to be iterated to accomplish the *)
(* operation, along with the metric ("matte_order") that decreases with that   *)
(* step.                                                                       *)

Definition mrlink [p1, p2 : gpoint] : bool := (end1g p1) =d (end0g p2).

Record matte : Set := Matte {
  mdisk :> gpointseq;
  mring : gpointseq;
  matte_ne : (ltn (0) (size mdisk));
  cycle_mring : (cycle mrlink mring);
  simple_mring : (uniq (maps end0g mring));
  mring_def : mring =1 [x](andb (mdisk (halfg x)) (negb (mdisk (halfg (gedge x)))))
}.

Lemma mring_edge : (m : matte; p : gpoint)
  (mring m p) -> (negb (mring m (gedge p))).
Proof.
By Case=> /= [c d _ _ _ Dc] p; Rewrite: !Dc; Move/andP=> [_ H]; Rewrite: (negbE H).
Qed.

(* Initial single_square matte. *)

Section PointMatte.

Variable p : gpoint.

Local pmdisk : gpointseq := (Seq p).
Local pmring : gpointseq := (maps [d](consg d p) (Seq Gb00 Gb10 Gb11 Gb01)).

Lemma pmatte_ne : (ltn (0) (size pmdisk)). Proof. Done. Qed.

Lemma cycle_pmring : (cycle mrlink pmring).
Proof. By Rewrite: /= /mrlink /end0g /end1g !halfg_cons !oddg_cons /= !set11. Qed.

Lemma simple_pmring : (uniq (maps end0g pmring)).
Proof.
By Rewrite: /= /setU1 /end0g !halfg_cons !oddg_cons !(monic_eqd (addg_inv p)).
Qed.

Lemma pmring_def :
   pmring =1 [x](andb (pmdisk (halfg x)) (negb (pmdisk (halfg (gedge x))))).
Proof.
Move=> x; Rewrite: -{1 x}consg_odd_half halfg_edge.
Case Hx: (pmdisk (halfg x)).
  Rewrite: /= /setU1 orbF in Hx; Rewrite: -(eqP Hx) /= /setU1 !orbF.
  Rewrite: -{9 p}addg0 (monic_eqd (addg_inv p)).
  By Case (oddg x); Rewrite: set11 ?orbT.
Apply/mapsP=> [[d _ Dx]]; Move: (congr halfg Dx); Rewrite: !halfg_cons.
By Move=> Dp; Rewrite: /pmdisk Dp /= setU11 in Hx.
Qed.

Definition point_matte : matte :=
  (Matte pmatte_ne cycle_pmring simple_pmring pmring_def).

End PointMatte.

(* Grid refinement for mattes.                                                  *)

Section RefineMatte.

Fixpoint refine_mring [c : gpointseq] : gpointseq :=
  if c is (Adds p c') then
    (Seq (consg (oddg p) p) (consg (oddg p) (gface p))
       & (refine_mring c'))
  else seq0.

Fixpoint refine_mdisk [md : gpointseq] : gpointseq :=
  if md is (Adds p md') then
    (Seq (consg Gb00 p) (consg Gb10 p) (consg Gb11 p) (consg Gb01 p)
       & (refine_mdisk md'))
  else seq0.

Variable m : matte.

Lemma mem_refine_mdisk : (md : gpointseq; p : gpoint)
  (refine_mdisk md p) = (md (halfg p)).
Proof.
Move=> md p; Elim: md => //= [q md Hrec]; Rewrite: /setU1 Hrec !orbA; Congr orb.
Rewrite: -!orbA; Apply/idP/eqP; LeftBy Case/or4P; Case/eqP; Rewrite: halfg_cons.
By Rewrite: -{-1 p}consg_odd_half; Case; Case (oddg p); Rewrite: set11 /= ?orbT.
Qed.

Lemma refine_matte_ne : (ltn (0) (size (refine_mdisk m))).
Proof. By Case: (mdisk m) (matte_ne m). Qed.

Lemma cycle_refine_mring : (cycle mrlink (refine_mring (mring m))).
Proof.
Case: (mring m) (cycle_mring m) => // [p0 c]; Rewrite: !(cycle_path p0).
Rewrite: {1}/last -/(last p0); Pose q := (last p0 c).
Step []: (consg (oddg q) (gface q)) = (last p0 (refine_mring (Adds p0 c))).
  By Rewrite: ~/q /=; Elim: c p0 => /=.
Elim: {p0 c}(Adds p0 c) q => //= [p c Hrec] q; Move/andP=> [Hqp Hc]; Move: Hqp.
Rewrite: ~Hrec ~{c Hc}// andbT /mrlink /end0g /end1g !halfg_cons !oddg_cons.
Move/eqP=> Dp; Rewrite: /gface -{1 3 p}consg_odd_half /consg.
Rewrite: addgA -addgA -(addgC (halfg q)) ~Dp addgA (addgC (halfg p)) !addgA set11.
By Rewrite: addgC -!addgA addgCA addgC -!addgA set11.
Qed.

Lemma mem_refine_mring : (c : gpointseq; p : gpoint)
  (reflect (EX q | (c q) & p = (consg (oddg q) q)
                        \/ p = (consg (oddg q) (gface q)))
           (refine_mring c p)).
Proof.
Move=> c p; Elim: c => [|q c Hrec] /=; LeftBy Right; Case.
Apply: (iffP setU1P).
  Case; LeftBy Exists q; [Apply setU11 | Left].
  Case/setU1P; LeftBy Exists q; [Apply setU11 | Right].
  By Case/Hrec=> [q' Hq' Dp]; Exists q'; LeftBy Apply setU1r.
Case=> [q']; Case/setU1P=> [[] | Hq'].
  By Case; Case; [Left | Right; Apply setU11].
By Right; Apply setU1r; Apply/Hrec; Exists q'.
Qed.

Lemma simple_refine_mring : (uniq (maps end0g (refine_mring (mring m)))).
Proof.
Elim: (mring m) (simple_mring m) (!mring_edge m) => //= [p c Hrec].
Move/andP=> [Hp Uc] HpcE; Step HcE: (q : gpoint)(c q) -> (negb (c (gedge q))).
  By Move=> q Hq; Case/norP: (HpcE ? (setU1r ? Hq)). 
Rewrite: ~Hrec ~{Hc HcE}// andbT; Apply/andP; Split. 
  Apply/setU1P=> [[Dp | Hp']].
    Rewrite: /end0g !halfg_cons !oddg_cons -!(addgC (oddg p)) in Dp.
    Move: (congr oddg (monic_inj (addg_inv ?) Dp)).
    By Rewrite: oddg_face; Case (oddg p).
  Case/mapsP: Hp' => [q Hq Dq].
  Case/(mem_refine_mring ? ?): Hq => [q' Hq' [Dq' | Dq']].
    Case/mapsP: Hp; Exists q'; Auto.
    Rewrite: -halfg_add_odd addgC.
    Move: Dq; Rewrite: -!halfg_add_odd Dq' !oddg_cons addgC /consg addgA.
    Rewrite: (addgC (oddg p)) -(addgA (addg p p)) !halfg_add_double !halfg_double.
    By Case.
  Move: Dq; Rewrite: -!halfg_add_odd Dq' !oddg_cons addgC /consg addgA.
  Rewrite: (addgC (oddg p)) -(addgA (addg p p)) !halfg_add_double !halfg_double.
  Move/(congr oddg 5!?); Rewrite: /gface /consg addgA oddg_add_double.
  Rewrite: (addgC p) -{2 p}consg_odd_half /consg addgA oddg_add_double oddg_double.
  By Case (oddg q').
Apply/mapsP=> [[q Hq Dq]]; Move: {Dq}(esym Dq); Rewrite: -!halfg_add_odd oddg_cons.
Rewrite: addgC /consg addgA halfg_add_double halfg_double (addgC q).
Case/(mem_refine_mring ? ?): Hq => [q' Hq' [Dq | Dq]];
  Rewrite: ~Dq oddg_cons /consg addgA halfg_add_double halfg_double.
  Move/(congr oddg 5!?); Rewrite: /gface /consg addgA oddg_add_double.
  Rewrite: -{2 q'}consg_odd_half /consg addgA oddg_add_double oddg_double.
  By Case (oddg p).
Case/norP: {HpcE}(HpcE ? (setU1r ? Hq')) => [Epq' _].
Rewrite: /gface /consg addgCA -/(consg (oddg p) (halfg p)) consg_odd_half.
Rewrite: addgCA consgI consg_odd_half; Move=> Dq'.
Rewrite: /gedge addgA (addgC q') -Dq' -addgA addgCA -{1 p}addg0 in Epq'.
Rewrite: (monic_eqd (addg_inv p)) in Epq'.
Step Dq1: (oddg q') = (oddg p).
  Move: (congr oddg Dq'); Rewrite: oddg_add {1 oddg}lock oddg_add -lock.
  Case: (oddg p) Epq'; Case: (oddg q') => //.
Rewrite: Dq1 in Dq'; Case/mapsP: Hp; Exists q'; Auto.
By Rewrite: (monic_inj (addg_inv ?) Dq').
Qed.

Lemma refine_mring_def :
  let md' = (refine_mdisk (mdisk m)) in
  (refine_mring (mring m)) =1 
     [p](andb (md' (halfg p)) (negb (md' (halfg (gedge p))))).
Proof.
Move: (mdisk m) (mring_def m) (mem_refine_mdisk (mdisk m)) => md Dmd Dmd' /= p.
Rewrite: /= !~Dmd' halfg_edge.
Apply/(mem_refine_mring ? ?)/andP=> [[q Hq Dp] | [Hp Hep]].
  Rewrite: Dmd halfg_edge addgC in Hq; Case/andP: Hq => [Hq HqE].
  By Case: Dp => [Dp | Dp]; Rewrite: Dp !halfg_cons oddg_cons ?halfg_face;
    Split; Rewrite: // addgC halfg_add ?halfg_face ?oddg_face; Case: (oddg q) HqE.
Pose q := (halfg p); Pose d := (oddg p).
Rewrite: addgC halfg_add addgC -/q -/d in Hep.
Step Hqd: (set2 d (ccw d) (oddg q)).
  Move: Hp Hep; Rewrite: -/q -{1 (halfg q)}addg0.
  By Case: d; Case: (oddg q) => //= [] H; Case/idP.
Exists (consg (oddg p) (halfg (halfg p))).
  Rewrite: Dmd halfg_edge halfg_cons oddg_cons Hp -/q -/d /=.
  By Case: (oddg q) Hqd Hep; Case d.
Rewrite: oddg_cons /gface oddg_cons halfg_cons -/d -/q.
Case/orP: Hqd; Move/eqP=> Dq; Rewrite: {2 d}Dq /q /d !consg_odd_half; Auto.
Qed.

Definition refine_matte : matte :=
  (Matte refine_matte_ne cycle_refine_mring simple_refine_mring refine_mring_def).

Lemma mem_refine_matte : (p : gpoint) (refine_matte p) = (m (halfg p)).
Proof. Exact (!mem_refine_mdisk ?). Qed.

Lemma refine_matte_refined : (r : gpointset)
  (refined_in refine_matte :: (set ?) r).
Proof. By Move=> r p q _ Dq; Rewrite: !mem_refine_matte Dq. Qed.

End RefineMatte.

Section ExtendMatte.

Variable m : matte.

Definition ext_mdisk [p : gpoint] : gpointseq := (Adds (halfg p) m).

Lemma ext_mdisk_ne : (p : gpoint) (ltn (0) (size (ext_mdisk p))).
Proof. Done. Qed.

Definition ehex [p : gpoint] : grect := (gchop_rect (gtouch (halfg p)) p).

Definition equad [p : gpoint] : grect := (gchop_rect (ehex p) (gface p)).

Lemma ehexF : (p : gpoint) (sub_set (equad p) (ehex (gface p))).
Proof.
Move=> p q; Rewrite: /equad /ehex halfg_face !mem_gchop_rect /setI.
By Rewrite: mem_gchop_rect /setI -andbA andbCA; Case/andP.
Qed.

Lemma end0g_equad : (p : gpoint) (negb (has (equad (gface p)) m)) ->
  (m (end0g p)) = false.
Proof.
Move=> p Hp; Apply/idP=> [Hmp]; Case/idP: {Hp Hmp}(hasPn Hp ? Hmp).
Rewrite: /equad /ehex /gchop_rect !halfg_face !oddg_face /= /end0g.
Case: (halfg p) => [x y] /=; Rewrite: !leq_decz_z !leq_z_incz.
Case (oddg p); Rewrite: /= ?addz0 -?incz_def -?decz_def;
 Do 2 Rewrite: ?leqzz ?leq_decz_z ?leq_z_incz //.
Qed.

Lemma mring_equad : (p : gpoint) (negb (has (equad (gface p)) m)) ->
  (maps end0g (mring m) (end0g p)) = false.
Proof.
Move=> p Hp; Apply/mapsP=> [[q Hq Eqp]].
Rewrite: mring_def in Hq; Move/andP: Hq => [Hq _]; Case/idP: (hasPn Hp ? Hq).
Rewrite: /equad /ehex /gchop_rect !halfg_face !oddg_face /=.
Rewrite: /end0g addgC in Eqp; Rewrite: (monic_move (addg_inv ?) Eqp) addgC -addgA.
Case: (halfg p) => [x y] /=; Rewrite: !leq_decz_z !leq_z_incz.
Case (oddg p); Case (oddg q); Rewrite: /= ?addz0 -?incz_def -?decz_def;
 Do 2 Rewrite: ?leqzz ?leq_decz_z ?leq_z_incz //.
Qed.

Section Extend1.

Variable p : gpoint.

Definition ext1_hex : bool := (andb (m (halfg (gedge p))) (negb (has (ehex p) m))).

Hypothesis HpE : ext1_hex.

Remark HpF : (mdisk m (halfg p)) = false.
Proof.
Apply/idP=> [Hdp]; Case: (andP HpE); Clear; Case/hasP; Exists (halfg p); Auto.
By Rewrite: /ehex mem_gchop_rect /setI gtouch_refl gchop_halfg.
Qed.

Remark Hp : (mring m (gedge p)).
Proof. By Rewrite: mring_def gedge2 HpF andbT; Case/andP: HpE. Qed.

Remark Hp1 : (negb ((has (equad (iter (3) gface p))) m)).
Proof.
Apply/hasP=> [[q Hmq Hq]]; Case/andP: HpE; Clear; Case/hasP; Exists q; LeftDone.
By Rewrite: -{p}gface4; Apply ehexF.
Qed.

Remark Hp2 : (negb ((has (equad (iter (4) gface p))) m)).
Proof.
Apply/hasP=> [[q Hmq Hq]]; Case/andP: HpE; Clear; Case/hasP; Exists q; LeftDone.
By Rewrite: /iter gface4 /equad mem_gchop_rect in Hq; Case/andP: Hq.
Qed.

Definition ext1_mring : gpointseq :=
  let (_, c, _) = (rot_to Hp) in (cat (traject gface (gface p) (3)) c).

Lemma cycle_ext1_mring : (cycle mrlink ext1_mring).
Proof.
Rewrite: /ext1_mring; Case: (rot_to Hp) (cycle_mring m) => [i c Dc].
Rewrite: -(cycle_rot i) ~{i}Dc !(cycle_path p) /=.
Rewrite: {1 3 4 5}/mrlink !end0g_face !set11 /= end0g_edge.
Case: c => [|q c] /=; LeftBy Rewrite: end1g_edge -{1 p}gface4 end0g_face.
By Rewrite: {1 3}/mrlink end1g_edge -{2 p}gface4 end0g_face.
Qed.

Lemma simple_ext1_mring : (uniq (maps end0g ext1_mring)).
Proof.
Rewrite: /ext1_mring; Move: (mring_equad Hp2) (simple_mring m).
Case: (rot_to Hp) => [i c Dc]; Rewrite: -(uniq_rot i) -(mem_rot i).
Move: (mring_equad Hp1); Rewrite: -(mem_rot i) -maps_rot.
Rewrite: ~{i}Dc {uniq}lock /= !end0g_edge -!end0g_face -lock.
Move: {c}(maps end0g c) (gface p) => c q /=; Rewrite: /setU1.
Move/norP=> [Uqq1 Ucq1]; Move/norP=> [Uqq2 Ucq2]; Move/andP=> [Ucq Uc].
Rewrite: ~Uc (negbE Ucq) (negbE Ucq1) (negbE Ucq2) eqd_sym (negbE Uqq1).
Rewrite: eqd_sym (negbE Uqq2) /= orbF andbT end0g_face; Apply/eqP.
By Move/(monic_inj (addg_inv ?) 7!?); Case (oddg (gface q)).
Qed.

Remark HpEF : (all [q](negb (m (halfg (gedge q)))) (traject gface (gface p) (3))).
Proof.
Apply/allP=> [q Hq]; Apply/idP=> [Hmq]; Case/andP: HpE; Clear; Case/hasP.
Exists (halfg (gedge q)); LeftDone; Case/trajectP: Hq => [i Hi []] {q Hmq}.
Rewrite: halfg_edge iter_f halfg_iter_face oddg_iter_face /ehex /gchop_rect. 
Case: (halfg p) => [x y]; Rewrite: /= ?leq_decz_z ?leq_z_incz.
Case (oddg p); Case: i Hi => [|[|[|i]]] //= _;
  Rewrite: ?addz0 -?incz_def -?decz_def;
  By Rewrite: ?leqzz ?leq_decz_z ?leq_z_incz ?leq_decz_incz.
Qed.
  
Lemma ext1_mring_def :
  ext1_mring =1 
   [q](andb (ext_mdisk p (halfg q)) (negb (ext_mdisk p (halfg (gedge q))))).
Proof.
Move=> q; Rewrite: /ext1_mring; Case: (rot_to Hp) => [i c Dc] /=.
Case/and4P: {}HpEF => [Hep1 Hep2 Hep3 _].
Rewrite: /setU1; Case Hq1: ((gface p) =d q).
  Case/eqP: {q}Hq1 => /=; Rewrite: halfg_face set11 /=.
  By Rewrite: -halfg_face neq_halfg_edge /=.
Case Hq2: ((gface (gface p)) =d q).
  Case/eqP: {q Hq1}Hq2 => /=; Rewrite: !halfg_face set11 /=; Symmetry.
  By Rewrite: -2!halfg_face neq_halfg_edge /=.
Case Hq3: ((gface (gface (gface p))) =d q).
  Case/eqP: {q Hq1 Hq2}Hq3 => /=; Rewrite: !halfg_face set11 /=; Symmetry.
  By Rewrite: -3!halfg_face neq_halfg_edge /=.
Case Hcq: (mring m q).
  Move: {}Hcq (maps_uniq (simple_mring m)) {}Hcq => Hdq.
  Rewrite: -(mem_rot i) -(uniq_rot i) Dc /= /setU1; Case/andP.
  Case Hpq: ((gedge p) =d q).
    By Case/eqP: Hpq; Rewrite: gedge2 set11 andbF; Move/negPf.
  Rewrite: mring_def in Hdq; Case/andP: Hdq => [Hdq Hdeq] _ _ /= Hcq'.
  Rewrite: ~Hcq' ~Hdq ~{Hdeq}(negbE Hdeq) orbT orbF; Symmetry; Apply/eqP=> [Dp].
  Move: {}Hcq; Rewrite: mring_def; Case/nandP; Left.
  Case Heq1: ((gedge (gface p)) =d q); LeftBy Case/eqP: Heq1.
  Case Heq2: ((gedge (gface (gface p))) =d q); LeftBy Case/eqP: Heq2.
  Case Heq3: ((gedge (gface (gface (gface p)))) =d q); LeftBy Case/eqP: Heq3.
  ElimType False; Move: Hpq Heq1 Heq2 Heq3; Rewrite: !(monic2_eqd gedge2 gedge2).
  Rewrite: -{(gedge q)}consg_odd_half -{1 p}consg_odd_half -Dp.
  Rewrite: {1 2 4}/gface !halfg_face !oddg_face /consg.
  Pose p2 := (addg (halfg p) (halfg p)).
  Rewrite: -!(addgC p2) !(monic_eqd (addg_inv p2)).
  By Case (oddg p); Case (oddg (gedge q)).
Move: {}Hcq; Rewrite: -(mem_rot i) Dc /=; Move/norP=> [Hpq Hcq'].
Rewrite: (negbE Hcq') /=; Symmetry.
Case Hpq': ((halfg p) =d (halfg q)).
  Case Hq0: (p =d q).
    Move: Hp; Rewrite: (eqP Hq0) mring_def; Case/andP=> [Dp _].
    By Rewrite: Dp orbT andbF.
  Move: Hq0 Hq1 Hq2 Hq3; Rewrite: -{p}consg_odd_half -{q}consg_odd_half (eqP Hpq').
  Rewrite: /gface !oddg_cons !halfg_cons /consg.
  Pose q2 := (addg (halfg q) (halfg q)).
  Rewrite: -!(addgC q2) !(monic_eqd (addg_inv q2)).
  By Case (oddg p); Case (oddg q).
Case: ((halfg p) =d (halfg (gedge q))); LeftBy Rewrite andbF.
By Rewrite: /= -mring_def.
Qed.

Definition ext1_matte : matte :=
  (Matte (ext_mdisk_ne ?) cycle_ext1_mring simple_ext1_mring ext1_mring_def).

End Extend1.

Section Extend2.

Variable p : gpoint.

Definition ext2_quad : bool :=
  (and3b (mdisk m (halfg (gedge p)))
         (mdisk m (halfg (gedge (gface p))))
         (negb (has (equad p) m))).

Hypothesis HpE : ext2_quad.

Remark HpF : (m (halfg p)) = false.
Proof.
Apply/idP=> [Hp]; Case: (and3P HpE) => [_ _]; Case/hasP; Exists (halfg p); Auto.
Rewrite: /equad /ehex /gchop_rect halfg_face oddg_face.
Case: (halfg p) => [x y]; Rewrite: /= ?leq_decz_z ?leq_z_incz.
By Case (oddg p); Rewrite: /= ?leq_decz_z ?leq_z_incz ?leqzz.
Qed.

Remark Hp1 : (negb (has (equad (iter (4) gface p)) m)).
Proof. By Rewrite: /iter gface4; Case/and3P: HpE. Qed.

Remark Hefp : (mring m (gedge (gface p))).
Proof. By Rewrite: mring_def gedge2 halfg_face HpF andbT; Case/and3P: HpE. Qed.

Remark Hep : (mring m (gedge p)).
Proof. By Rewrite: mring_def gedge2 HpF andbT; Case/andP: HpE. Qed.

Remark Hp: {c : gpointseq & {i : nat |
  (rot i (mring m)) = (Seq (gedge (gface p)) (gedge p) & c)}}.
Proof.
Case/rot_to: {}Hefp => [i [|p' c] Dp].
  Move: (cycle_mring m); Rewrite: -(cycle_rot i) Dp /= /mrlink.
  Rewrite: /end0g /end1g [q](monic_eqd (addg_inv q)) oddg_edge oddg_face.
  By Case (oddg p).
Exists c; Exists i; Rewrite Dp; Do 2 Congr Adds.
Move: (cycle_mring m) {}Hep (simple_mring m).
Rewrite: -(cycle_rot i) -(mem_rot i) -(uniq_rot i) -maps_rot Dp /mrlink.
Move/andP=> [Dp' _]; Rewrite: end1g_edge end0g_face in Dp'.
Rewrite: -(mem_rot (1)) -(uniq_rot (1)) -maps_rot rot1_adds /=.
Case/setU1P => // [Hp']; Case/andP; Case/mapsP; Exists (gedge p); Auto.
By Rewrite: end0g_edge (eqP Dp').
Qed.

Definition ext2_mring : gpointseq :=
  let (c, _) = Hp in (cat (traject gface (gface (gface p)) (2)) c).

Lemma cycle_ext2_mring : (cycle mrlink ext2_mring).
Proof.
Rewrite: /ext2_mring; Case: Hp (cycle_mring m) => [c [i Dc]].
Rewrite: -(cycle_rot i) ~{i}Dc !(cycle_path p) /=.
Rewrite: {1 2 4 5}/mrlink end1g_edge !end0g_face !end0g_edge !set11 /=.
Case: c => [|q c] /=; LeftBy Rewrite: end1g_edge -{1 p}gface4 end0g_face.
By Rewrite: {1 3}/mrlink end1g_edge -{2 p}gface4 end0g_face.
Qed.

Lemma simple_ext2_mring : (uniq (maps end0g ext2_mring)).
Proof.
Rewrite: /ext2_mring -(uniq_rot (1)).
Case: Hp (mring_equad Hp1) (simple_mring m) => [c [i Dc]].
Rewrite: -(uniq_rot i) -(mem_rot i)  -(uniq_rot (1)) -(mem_rot (1)) -!maps_rot.
Rewrite: ~{i}Dc {maps}lock /= -!lock !rot1_adds /= !maps_add_last.
By Rewrite: !end0g_edge !end0g_face; Move/norP=> [_ H]; Rewrite: ~H; Case/andP.
Qed.

Remark HpEF :
  (all [q](negb (m (halfg (gedge q)))) (traject gface (gface (gface p)) (2))).
Proof.
Apply/allP=> [q Hq]; Apply/idP=> [Hmq]; Case/and3P: HpE; Do 2 Clear; Case/hasP.
Exists (halfg (gedge q)); LeftDone; Case/trajectP: Hq => [i Hi []] {q Hmq}.
Rewrite: halfg_edge !iter_f halfg_iter_face oddg_iter_face.
Rewrite: /equad /ehex /gchop_rect halfg_face oddg_face.
Case: (halfg p) => [x y]; Rewrite: /= ?leq_decz_z ?leq_z_incz.
Case (oddg p); Rewrite: /= ?leq_decz_z ?leq_z_incz;
  Case: i Hi => [|[|i]] //= _; Rewrite: ?addz0 -?incz_def -?decz_def;
  By Rewrite: ?leqzz ?leq_decz_z ?leq_z_incz.
Qed.
  
Lemma ext2_mring_def :
  ext2_mring =1 
   [q](andb (ext_mdisk p (halfg q)) (negb (ext_mdisk p (halfg (gedge q))))).
Proof.
Move=> q; Rewrite: /ext2_mring; Case: Hp => [c [i Dc]] /=; Rewrite: /setU1.
Case/and3P: {}HpEF => [Hep2 Hep3 _].
Case Hq2: ((gface (gface p)) =d q).
  Case/eqP: {q}Hq2 => /=; Rewrite: !halfg_face set11 /=; Symmetry.
  By Rewrite: -2!halfg_face neq_halfg_edge /=.
Case Hq3: ((gface (gface (gface p))) =d q).
  Case/eqP: {q Hq2}Hq3 => /=; Rewrite: !halfg_face set11 /=; Symmetry.
  By Rewrite: -3!halfg_face neq_halfg_edge /=.
Case Hcq: (mring m q).
  Move: {}Hcq (maps_uniq (simple_mring m)) {}Hcq => Hdq.
  Rewrite: -(mem_rot i) -(uniq_rot i) Dc /= /setU1; Case/and3P; Case/norP; Clear.
  Case Hepq: ((gedge (gface p)) =d q).
    By Case/eqP: Hepq; Rewrite: gedge2 halfg_face set11 andbF; Move/negPf.
  Case Hpq: ((gedge p) =d q).
    By Case/eqP: Hpq; Rewrite: gedge2 set11 andbF; Clear; Move/negPf.
  Rewrite: mring_def in Hdq; Case/andP: Hdq => [Hdq Hdeq] _ _ _ /= Hcq'.
  Rewrite: ~Hcq' ~Hdq ~{Hdeq}(negbE Hdeq) orbT orbF; Symmetry; Apply/eqP=> [Dp].
  Move: {}Hcq; Rewrite: mring_def; Case/nandP; Left.
  Case Heq2: ((gedge (gface (gface p))) =d q); LeftBy Case/eqP: Heq2.
  Case Heq3: ((gedge (gface (gface (gface p)))) =d q); LeftBy Case/eqP: Heq3.
  ElimType False; Move: Hpq Hepq Heq2 Heq3; Rewrite: !(monic2_eqd gedge2 gedge2).
  Rewrite: -{(gedge q)}consg_odd_half -{1 p}consg_odd_half -Dp.
  Rewrite: {1 2 4}/gface !halfg_face !oddg_face /consg.
  Pose p2 := (addg (halfg p) (halfg p)).
  Rewrite: -!(addgC p2) !(monic_eqd (addg_inv p2)).
  By Case (oddg p); Case (oddg (gedge q)).
Move: {}Hcq; Rewrite: -(mem_rot i) Dc /=.
Case/norP=> [Hpq]; Case/norP=> [Hpeq Hcq'].
Rewrite: (negbE Hcq') /=; Symmetry.
Case Hpq': ((halfg p) =d (halfg q)).
  Case Hq0: (p =d q).
    Move: Hep; Rewrite: (eqP Hq0) mring_def; Case/andP=> [Dp _].
    By Rewrite: Dp orbT andbF.
  Case Hq1: ((gface p) =d q).
    Move: Hefp; Rewrite: (eqP Hq1) mring_def; Case/andP=> [Dp _].
    By Rewrite: Dp orbT andbF.
  Move: Hq0 Hq1 Hq2 Hq3; Rewrite: -{p}consg_odd_half -{q}consg_odd_half (eqP Hpq').
  Rewrite: /gface !oddg_cons !halfg_cons /consg.
  Pose q2 := (addg (halfg q) (halfg q)).
  Rewrite: -!(addgC q2) !(monic_eqd (addg_inv q2)).
  By Case (oddg p); Case (oddg q).
Case: ((halfg p) =d (halfg (gedge q))); LeftBy Rewrite andbF.
By Rewrite: /= -mring_def.
Qed.

Definition ext2_matte : matte :=
  (Matte (ext_mdisk_ne ?) cycle_ext2_mring simple_ext2_mring ext2_mring_def).

End Extend2.

End ExtendMatte.

Section MatteExtension.

Variable m : matte.

Inductive matte_extension : matte -> Set :=
  Mext_nil : (matte_extension m)
| Mext_add : (p : gpoint; xm', xm : matte)
            (matte_extension xm') ->
            (mring xm' (gedge p)) ->
             xm =1 (ext_mdisk xm' p) ->
          (matte_extension xm).

Implicits Mext_add [].

Lemma mem_extension : (xm : matte) (matte_extension xm) -> (sub_set m xm).
Proof.
Move=> xm; Elim {xm} => [|p xm' xm _ Hrec _ Dxm] q Hq //.
By Rewrite: Dxm /= setU1r ?Hrec. 
Qed.

Inductive extends_in [r : grect; p : gpoint] : Set :=
  ExtendIn : (xm : matte) (matte_extension xm) ->
      (sub_set xm (setU r m)) -> (xm p) -> (extends_in r p).

Lemma extends_in_sub : (r1, r2 : grect) (sub_set r1 r2) ->
  (p : gpoint) (extends_in r1 p) -> (extends_in r2 p).
Proof.
Move=> r1 r2 Hr12 p [xm Hxm Hxmr Hp]; Exists xm; Auto.
By Move=> q Hq; Apply/orP; Case/orP: (Hxmr ? Hq); Auto.
Qed.

Definition inset [r : grect; p : gpoint] : bool := (sub_grect (gtouch p) r).

Lemma refined_extends_in : (r : grect)
  (refined_in m::(set ?) r) -> (has r m) ->
  (p : gpoint) (inset r p) -> (extends_in r p).
Proof.
Move=> r Hr0m Hrm p Hirp; Step Hrr0: (sub_set r r) By Move.
Step Hr0r: (sub_set (setI r m) r) By Move=> q; Case/andP.
Step Hr0p: (sub_set (gtouch p) r) By Apply mem_sub_grect.
Step Hrp: (r p) By Apply Hr0p; Apply gtouch_refl.
Move: {-1}r {1 3 4 5 8 11}r p (ltnSn (garea r)) Hrm Hrp Hrr0 Hr0r Hr0p Hr0m {Hirp}.
Elim: {r}(S (garea r)) => // [n Hrec] r0 r p Hn Hrm Hrp Hrr0 Hr0r Hr0p Hr0m.
Pose G := (extends_in r p); Rewrite ltnS in Hn. 
Case Hmp: (mdisk m p).
  By Exists m; Try First [Left | Move=> q Hq; Rewrite: /setU Hq orbT].
Step Hxm1: (p' : gpoint) (halfg p') = p -> (negb (has (ehex p') m)) -> 
           (extends_in (gchop_rect r (gedge p')) (halfg (gedge p'))) -> G.
  Move=> p' Dp' Hep' [xm Hxm Hxmr' Hxmp'].
  Step Hp': (ext1_hex xm p').
    Rewrite: /ext1_hex Hxmp'; Apply/hasPn=> [q Hq].
    Case/orP: {Hq}(Hxmr' ? Hq); RightBy Move=> *; Apply (hasPn Hep').
    Rewrite: /ehex !mem_gchop_rect /setI gchop_edge.
    By Case/andP=> *; Apply/nandP; Right.
  Exists (ext1_matte Hp'); Rewrite: /= ?Dp' ?setU11 //.
    Right with p' xm; Rewrite: // mring_def gedge2 Dp' Hxmp'.
    Apply/idP; Move/(Hxmr' ?); Rewrite: /setU Hmp mem_gchop_rect /setI gchop_edge.
    By Rewrite: -Dp' /setC gchop_halfg andbF.
  Move=> q; Case/setU1P=> [[] | Hq]; LeftBy Rewrite: /setU Hrp.
  Apply/orP; Case/orP: (Hxmr' ? Hq); Try (Rewrite mem_gchop_rect; Case/andP); Auto.
Step Hcut: (p' : gpoint) (halfg p') = p -> (has (setD r0 (gchop1 p')) m) -> G.
  Move=> p' Dp' Hr0p'; Pose r0' := (gchop1_rect r0 p').
  Case Hr0': (has r0' m).
    Pose r' := (gchop1_rect r p').
    Step Hr'r : (sub_set r' r) By Apply: (!gchop_rect_sub).
    Apply: (extends_in_sub Hr'r); Apply (Hrec r0').
     Case/hasP: Hr0p' => [q Hmq]; Move/andP=> [Hp'q Hr0q].
      Apply: leq_trans Hn; Apply (ltn_garea_sub_rect Hr'r 4!q).
      By Rewrite: /setD /r' mem_gchop1_rect /setI (negbE Hp'q) Hr0r //= /setI Hr0q.
     Case/hasP: Hr0' => [q Hmq]; Rewrite: /r0' mem_gchop1_rect.
      Move/andP=> [Hr0q Hp'q]; Apply/hasP; Exists q; LeftDone.
      By Rewrite: /r' mem_gchop1_rect /setI Hp'q Hr0r //= /setI Hr0q.
     By Rewrite: /r' mem_gchop1_rect /setI Hrp gchop_chop1 // -Dp' gchop_halfg.
     Move=> q; Rewrite: /r' /r0' !mem_gchop1_rect /setI.
      By Case/andP=> *; Apply/andP; Auto.
     Move=> q; Rewrite: /r' /r0' /setI !mem_gchop1_rect /setI -andbA andbCA.
      By Case/andP=> *; Apply/andP; Auto.
     Move=> q Hq; Rewrite: /r0' mem_gchop1_rect; Apply/andP; Split; Auto.
      By Move: Hq; Rewrite: -Dp' gtouch_chop1; Case/andP.
    Move=> q q' Hq; Exact (Hr0m q q' (gchop_rect_sub Hq)).
  Apply (Hxm1 ? Dp').
    Apply/hasP=> [[q Hmq]]; Rewrite: /ehex mem_gchop_rect Dp'.
    Move/andP=> [Hpq _]; Case/hasP: Hr0'; Exists q; LeftDone.
    Rewrite: /r0' mem_gchop1_rect /setI Hr0p //=.
    By Move: Hpq; Rewrite: -Dp' gtouch_chop1; Case/andP.
  Pose r' := (gchop_rect r (gedge p')).
  Step Hr'r: (sub_set r' r) By Apply: (!gchop_rect_sub).
  Step Hr'm: (has r' m).
    Case/hasP: Hr0p' => [q Hmq]; Move/andP=> [Hp'q1 Hr0q]; Apply/hasP.
    Exists q; Rewrite: // /r' mem_gchop_rect /setI Hr0r /setI ?Hr0q // gchop_edge.
    By Apply/idP=> [Hp'q]; Case/idP: Hp'q1; Apply gchop_chop1.
  Apply (Hrec r0); Auto.
   Apply: leq_trans Hn; Apply (ltn_garea_sub_rect Hr'r 4!p); Rewrite: /setD /r'.
    By Rewrite: mem_gchop_rect /setI Hrp gchop_edge /setC -Dp' gchop_halfg.
   Case/hasP: Hr'm => [q _ Hq]; Apply: (gchop_rect_edge ? Hq).
    By Rewrite: gedge2 Dp'.
   By Move; Auto.
   Move=> q Hq; Rewrite: /r' mem_gchop_rect /setI Hr0r //= gchop_edge.
    Apply/idP=> [Hp'q]; Case/andP: Hq => [Hr0q Hmq]; Case/hasP: Hr0'.
    By Exists q; Rewrite: // /r0' mem_gchop1_rect /setI Hr0q; Apply: gchop_chop1.
  Pose p2 := (gedge (gface (gface (gedge p')))).
  Step Hp2: (gchop_rect r0 p2 (halfg p2)).
    Case/hasP: Hr0p' => [q Hmq Hq0]; Apply gchop_rect_edge with q.
      By Apply Hr0p; Rewrite: /p2 gedge2 !halfg_face -Dp' gtouch_edge.
    By Rewrite: mem_gchop_rect /p2 /setI gchop_edge andbC.
  Rewrite: mem_gchop_rect /setI gchop_halfg andbT in Hp2.
  Step Hp1: (r0 (halfg (gedge (gface p')))).
    By Apply Hr0p; Rewrite: -Dp' -halfg_face gtouch_edge.
  Step Hp3: (r0 (halfg (gedge (gface (gface (gface p')))))).
    By Apply Hr0p; Rewrite: -Dp' -3!halfg_face gtouch_edge.
  Apply mem_sub_grect; Move: Hp1 Hp2 Hp3.
  Rewrite: /p2 !halfg_edge !oddg_face !halfg_face !oddg_edge halfg_edge ccw4 Dp'.
  Rewrite: -!addgA; Case: {}r0 {}p => [x0 x1 y0 y1] [x y].
  Case (oddg p'); Case/and4P=> [Hx01 Hx11 Hy01 Hy11];
    Case/and4P=> [Hx02 Hx12 Hy02 Hy12]; Case/and4P=> [Hx03 Hx13 Hy03 Hy13];
  By Rewrite: /= ?incz_def ?decz_def -!addzA; Apply/and4P; Split.
Pose np := [q](consg (ccw (ccw (ccw (oddg q)))) q).
Step Enph: (q : gpoint) (halfg (np q)) = q By Move=> *; Rewrite: /np halfg_cons.
Step Enpo: (q : gpoint) (oddg (np q)) = (ccw (ccw (ccw (oddg q)))).
  By Move=> *; Rewrite: /np oddg_cons.
Step EnpE: (q : gpoint) (halfg (gedge (np q))) = (gnode q).
  By Move=> q; Rewrite: halfg_edge /gnode /np halfg_cons oddg_cons; Case (oddg q).
Step DnpN: (q : gpoint) (np (gnode q)) = (gedge (gnode (gedge (np q)))).
  Move=> q; Apply (monic_move gmonicF).
  By Rewrite: /gface Enph Enpo oddg_node -Enpo -oddg_edge -EnpE consg_odd_half.
Step Hnp4: (q : gpoint) (r0 q) -> (has (equad (np q)) m) -> (m q).
  Move=> q0 Hr0q0; Move/hasP=> [q Hmq Hq]; Rewrite: -(Hr0m ? q Hr0q0) //.
  Apply: eqP; Move: Hq {Hmq}; Rewrite: /equad /ehex /gchop_rect halfg_face.
  Rewrite:  oddg_face Enph Enpo ccw4 -{1 2 4 q0}consg_odd_half /consg addgC.
  Case: (halfg q0) q => [x y] [x' y']; Rewrite: eqd_sym /eqd /=.
  Rewrite: !eqz_leq -!andbA !leqz_halfl !leqz_halfr.
  By Case (oddg q0);
    Rewrite: /= ?addz0 ?addn0 ?leq_decz_z ?leq_z_incz -?incz_def ?decz_inc.
Step Eq2x2: (q, q' : gpoint) (ehex q q') \/ (ehex (gface (gedge (gface q))) q')
                           -> (equad q q') \/ (equad (gedge (gface q)) q').
  Step Ec1c: (q, q' : gpoint; b : bool)
    (andb (andb (gchop1 q q') b) (gchop q q')) = (andb (gchop q q') b).
    Move=> q q' b; Case Hqq': (gchop q q'); RightBy Rewrite andbF.
    By Rewrite: andbT (gchop_chop1 Hqq').
  Move=> q q'; Repeat Rewrite: /equad /ehex mem_gchop_rect /setI.
  Rewrite: !gtouch_chop1 /all /traject !andbT gface4 !Ec1c.
  Rewrite: {-12 -13 andb}lock andbCA -!lock Ec1c gchopFEF.
  Case (gchop q q'); Rewrite: // !andTb Ec1c.
  Pose q2q' := (gchop1 (gface (gface q)) q').
  Step []: q2q' = (gchop1 (gface (gface (gface (gedge (gface q))))) q').
    Rewrite: /gchop1 -gchopFEF -!gnode_face !gface4; Congr gchop; Congr gface.
    By Symmetry; Apply: (monic_move gmonicN); Rewrite gnode4.
  Case: q2q'; Rewrite: ?andbF // !andTb !andbT gchop_edge /setC.
  Case Hqq': (gchop (gface q) q').
    By Case; Case/andP; Left; Rewrite: // -{(gface q)}gedge2; Apply: gchop_chop1.
  By Case; Case/andP; Right; LeftBy Apply: gchop_chop1.
Step Hr0np: (r0 (gnode p)) By Apply Hr0p; Rewrite: -EnpE -{1 p}Enph gtouch_edge.
Step EnpFE: (q : gpoint) (np (gface (gedge q))) = (gedge (gface (np q))).
  By Move=> q; Rewrite: -{2 q}gmonicE DnpN gmonicN gedge2.
Step Hr0fep: (r0 (gface (gedge p))).
  Apply Hr0p; Rewrite: -{(gface (gedge p))}Enph -{(np (gface (gedge p)))}gedge2.
  By Rewrite: -{1 p}gmonicE -EnpE gtouch_edge.
Case Hqpm: (has (equad (np p)) m); LeftBy Rewrite: Hnp4 ?Hrr0 in Hmp.
Case Hhpm: (has (ehex (np p)) m).
  Step Hmefp: (m (halfg (gedge (gface (np p))))).
    Rewrite: -EnpFE Enph Hnp4 //.
    Case/hasP: Hhpm => [q Hmq Hq]; Apply/hasP; Exists q; LeftDone.
    Case: (Eq2x2 (np p) q) => //; Rewrite: -?EnpFE //; LeftBy Left.
    By Move=> *; Case/hasP: Hqpm; Exists q.
  Case Hhfpm: (has (ehex (gface (np p))) m).
    Step Hmep: (m (halfg (gedge (np p)))).
      Rewrite: EnpE Hnp4 //; Case/hasP: Hhfpm => [q Hmq Hq].
      Case: (Eq2x2 (np (gnode p)) q); Try Rewrite: -EnpFE gmonicN; Auto.
        By Move=> *; Apply/hasP; Exists q.
      By Move=> *; Case/hasP: Hqpm; Exists q.
    Step Hext: (ext2_quad m (np p)) By Rewrite: /ext2_quad Hmep Hmefp Hqpm.
    Exists (ext2_matte Hext); Rewrite: /= ?Enph ?setU11 //.
      Right with (np p) m; [Left | Idtac | Split].
      By Rewrite: mring_def gedge2 Enph Hmp Hmep.
    By Move=> q; Case/setU1P=> [[] | Hq]; Apply/orP; Auto.
  Apply: (Hxm1 (gface (np p))); Rewrite: ?Hhfpm ?halfg_face //.
  Exists m; [Left | Move=> q Hq; Apply/orP; Auto | Done].
Case Hpm: (negb (has (gtouch p) m)).
  Pose hrp := [i](has (setD r0 (gchop1 (iter i gface (np p)))) m).
  Cut {i : nat | (hrp i)}; LeftBy Case=> [i]; Apply: Hcut; Rewrite: halfg_iter_face.
  Case Hh0: (hrp (0)); LeftBy Exists (0).
  Case Hh1: (hrp (1)); LeftBy Exists (1).
  Case Hh2: (hrp (2)); LeftBy Exists (2).
  Case Hh3: (hrp (3)); LeftBy Exists (3).
  Case/hasP: Hpm; Case/hasP: Hrm => [q Hmq Hq]; Exists q; LeftDone.
  Rewrite: -{p}Enph gtouch_chop1; Apply/allP=> [p']; Move/trajectP=> [i Hi []].
  Case Hhi: (hrp i); LeftBy Case/negPf: Hhi; Case: i Hi => [|[|[|[|i]]]] //.
  By Move: (elimFn hasPn Hhi ? Hmq); Rewrite: /setD Hrr0 //= andbT negb_elim.
Apply: (Hxm1 (np p)); Rewrite: ?Hhpm // EnpE.
Case Hmnp: (m (gnode p)).
  By Exists m; Try First [Left | Move=> q Hq; Rewrite: /setU Hq orbT].
Case Hqnpm: (has (equad (np (gnode p))) m); LeftBy Rewrite Hnp4 in Hmnp.
Step Hr0n2p: (r0 (gnode (gnode p))).
  Rewrite: {1}/gnode oddg_node /gnode -!addgA; Apply Hr0p; Case: {1 2}p => [x y].
  By Case (oddg p); Rewrite: /= -?incz_def -?decz_def !leqzz !leq_decz_incz.
Step Hmn2p: (m (gnode (gnode p))).
  Apply: Hnp4 => //; Apply/hasP; Move/hasP: Hpm => [q Hmq Hq]; Exists q; Auto.
  Step Hnpq: (gchop (gface (np (gnode p))) q).
    Rewrite: DnpN gmonicN gchop_edge; Apply/idP=> [Hpq]; Case/hasP: Hhpm.
    By Exists q; RightBy Rewrite: /ehex mem_gchop_rect Enph /setI Hq.
  Case: (Eq2x2 (np (gnode (gnode p))) q) => //.
    Right; Rewrite: /ehex -EnpFE gmonicN mem_gchop_rect /setI Hnpq halfg_face Enph.
    Move: Hq Hnpq; Rewrite: /gchop halfg_face oddg_face Enph Enpo oddg_node ccw4.
    Rewrite: /gnode; Case: {}p {}q (oddg p) => [x y] [x' y'] /=.
    Case; Rewrite: /= -?incz_def -?decz_def ?addz0 ?decz_inc ?incz_dec andbT;
      Rewrite: !leqz_dec_inc ?leqz_inc_dec; Case/and4P=> *; Apply/and4P; Split;
      By Rewrite: // leqz_dec ?decz_inc; Apply/orP; Right.
  By Rewrite: -EnpFE gmonicN; Move=> *; Case/hasP: Hqnpm; Exists q.
Step Hrnp: (r (gnode p)).
  Step Hrn2p: (r (gnode (gnode p))) By Apply Hr0r; Rewrite: /setI Hr0n2p.
  Move: Hrn2p; Do 3 Rewrite: {1}/gnode ?oddg_node; Rewrite: -!addgA.
  Case: {}r {}p (oddg p) Hrp => [x0 x1 y0 y1] [x y].
  By Case; Rewrite: /= -?incz_def -?decz_def ?decz_inc ?incz_dec ?addz0;
    Move/and4P=> [Hx0 Hx1 Hy0 Hy1]; Case/and4P=> *; Apply/and4P; Split.
Step Hext: (ext1_hex m (np (gnode p))).
  Rewrite: /ext1_hex EnpE Hmn2p; Apply/hasP=> [[q Hmq Hq]].
  Case: (Eq2x2 (np (gnode p)) q); Rewrite: -?EnpFE ?gmonicN; Auto.
    By Move=> *; Case/hasP: Hqnpm; Exists q.
  By Move=> *; Case/hasP: Hqpm; Exists q.
Exists (ext1_matte Hext); Rewrite: /= ?Enph ?setU11 //.
  Right with (np (gnode p)) m; Try By Try Left.
  By Rewrite: mring_def EnpE Hmn2p gedge2 Enph Hmnp.
Move=> q /=; Case/setU1P=> [[] | Hq]; Apply/orP; [Left | By Right].
Rewrite: mem_gchop_rect /setI Hrnp /gchop EnpE oddg_edge Enpo ccw4.
By Case: (gnode p) (oddg p) => [x y]; Case; Apply: leqzz. 
Qed.

(* The refined_extends_in lemma is used directly to show that the union of a   *)
(* set of extension mattes included in a region is closed (relatively to the   *)
(* region). To show that this union is open we will need the MatteOrder lemmas *)
(* below. We use the refined_extend_meet lemma to extend the mattes of         *)
(* adjacent regions so that their contours have a common edge.                 *)

Lemma extend_meet : (m2 : matte; r : grect)
  (refined_in m::(set ?) r) -> (has r m) ->
  (has (inset r) m2) -> (negb (has m m2)) -> 
  {xm : matte | (sub_set m xm) /\ (sub_set xm (setD (setU r m) m2))
      & (has [q](mring m2 (gedge q)) (mring xm))}.
Proof.
Move=> m2 r Hmr Hrm Hrm2 Hmm2; Rewrite has_sym in Hmm2.
Step [p Hm2p Hp]: {p : gpoint | (m2 p) & (inset r p)}.
  Exists (sub neg1g m2 (find (inset r) m2)); RightBy Apply: sub_find.
  By Apply: mem_sub; Rewrite: -has_find.
Case: (refined_extends_in Hmr Hrm Hp) => [xm Hxm Hxmr Hxmp].
Step Hxm2: (has m2 xm) By Apply/hasP; Exists p.
Elim: {xm}Hxm Hxmr Hxm2 {p Hm2p Hrm2 Hp Hxmp}; LeftBy Rewrite (negbE Hmm2).
Move=> p xm' xm Hxm' Hrec Hxm'p Dxm Hxmr Hxm2.
Step Hxm'r: (sub_set xm' (setU r m)).
  By Move=> q Hq; Apply Hxmr; Rewrite: Dxm /= /setU1 Hq orbT.
Case Hxm'2: (has m2 xm'); [EAuto | Exists xm'].
  Split; [By Apply mem_extension | Move=> q Hq; Rewrite: /setD andbC Hxm'r //=].
  By Apply (elimFn hasPn Hxm'2).
Apply/hasP; Exists (gedge p); Rewrite: // gedge2 mring_def; Apply/andP; Split.
  Apply/idPn=> [Hm2p]; Case/hasPn: Hxm2; Move=> q; Rewrite: Dxm /=.
  By Case/setU1P=> [[] | Hq] //; Apply (elimFn hasPn Hxm'2).
By Apply (elimFn hasPn Hxm'2); Rewrite: mring_def in Hxm'p; Case/andP: Hxm'p.
Qed.

End MatteExtension.

Section MatteOrder.

Definition matte_order [m : matte; p : gpoint] : nat :=
  let m' = (setC m) in
  (addn (double (addn (m' (addg p (oppg Gb01))) (m' (addg p (oppg Gb10)))))
                (addn (m' (addg p (oppg Gb11))) (m' (addg p (oppg Gb00))))).

Lemma zspan_decz_z : (x : znat) (zspan (decz x) x) = (Seq (decz x) x).
Proof.
Move=> x; Rewrite: /zspan /zwidth {2 (decz x)}decz_def -subz_sub subzz /=.
By Rewrite incz_dec.
Qed.

Definition ltouch [p : gpoint] : grect :=
  let (mx, my) = p in (Grect (decz mx) mx (decz my) my).
  
Lemma matte_order0 : (m : matte; p : gpoint)
  (matte_order m p) = (0) -> (sub_set (ltouch p) m).
Proof.
Move=> m p; Move/(introT eqP); Rewrite: /matte_order double_addnn !eqn_add0 andbb.
Step Em': ([q]((setC m q)::nat) =d (0)) =1 m By Rewrite: /setC /eqfun; Case/m.
Case: p => [x y] Hp q; Rewrite: -mem_enum_grect /= !zspan_decz_z /=.
Rewrite: !Em' /= !addz0 -!decz_def -!andbA in Hp.
By Case/and4P: Hp => [Hp01 Hp10 Hp11 Hp00]; Do 4 (Case/setU1P; LeftBy Case).
Qed.

Definition inset2 [r : grect; p : gpoint] : bool :=
  (andb (inset r p) (inset r (addg p neg1g))).

Lemma inset2_refine : (r : grect; p : gpoint)
  (inset r (halfg p)) -> (inset2 (refine_rect r) p).
Proof.
Move=> [x0 x1 y0 y1] [x y]; Rewrite: /inset2 /inset /= -?decz_def.
Rewrite: !leqz_inc2 -2!leqz_inc_dec !leqz_halfr 4!incz_def -!addzA.
Rewrite: -!(addzCA x0) -!(addzCA y0) !addzA -!incz_def 6!leqz_inc_dec !leqz_halfl.
Rewrite: 2!incz_def (decz_def x1) (decz_def y1) -!addzA !addz0.
Rewrite: -!(addzC x1) -!(addzC y1) !addzA -?decz_def.
Move/and4P=> [Hx0 Hx1 Hy0 Hy1]; Rewrite: Hx0 Hy0 leqz_dec Hx0 leqz_dec Hx1.
Rewrite: leqz_dec Hy0 leqz_dec Hy1 2!leqz_dec leqz_dec2 Hx1.
By Rewrite: 2!leqz_dec leqz_dec2 Hy1 !orbT.
Qed.

Lemma refine_matte_order : (m : matte; r : grect; p : gpoint)
   (m (halfg p)) -> (inset r (halfg p)) -> (ltn (0) (matte_order m (halfg p))) ->
   {xm : matte |
       (sub_set [q](m (halfg q)) xm) /\ (sub_set xm [q](setU r m (halfg q)))
     & (ltn (matte_order xm p) (matte_order m (halfg p)))}.
Proof.
Move=> m r p Hmp Hrp; Pose dp := [d : gbits](addg p (oppg d)).
Step Hdp: (d : gbits) {xm : matte |
       (sub_set [q](m (halfg q)) xm) /\ (sub_set xm [q](setU r m (halfg q)))
     & (d' : gbits)
       (xm (addg p (oppg d'))) = (or3b d =d d' (m (halfg (dp d'))) (xm (dp d')))}.
  Pose r' := (refine_rect r); Pose m' := (refine_matte m).
  Step Hr'p: (d : gbits) (inset r' (dp d)).
    Move=> d; Case/andP: (inset2_refine Hrp); Rewrite: -/r' ~/dp ~{Hmp Hrp}.
    Case: p r' => [x y] [x0 x1 y0 y1].
    Rewrite: /inset /= -?decz_def ?incz_dec.
    Move/and4P=> [Hx0 Hx1 Hy0 Hy1]; Move/and4P=> [Hx0' Hx1' Hy0' Hy1'].
    By Case: d; Rewrite: /= -?decz_def -?incz_def ?incz_dec ?addz0;
      Apply/and4P; Split.
  Step Hm'r': (refined_in m'::(set ?) r') By Apply: (!refine_matte_refined).
  Step Hr'm': (has r' m').
    Apply/hasP; Exists (dp Gb00); LeftBy Rewrite: /m' mem_refine_matte /dp addg0.
    Apply (mem_sub_grect (Hr'p Gb00)); Apply gtouch_refl.
  Move=> d; Case: (refined_extends_in Hm'r' Hr'm' (Hr'p d)) => [xm Hxm Hxmr' Hxmd].
  Exists xm.
    Split; Move=> q Hq.
      By Apply (mem_extension Hxm); Rewrite: /m' mem_refine_matte.
    Apply/orP; Case/orP: (Hxmr' ? Hq).
      By Rewrite: /r' mem_refine_rect; Left.
    By Rewrite: /m' mem_refine_matte; Right.
  Move=> d'; Rewrite: -/(dp d') -mem_refine_matte -/m'.
  Case: (d =P d') => [[] | _]; LeftBy Rewrite: Hxmd orbT.
  By Case Hd': (m' (dp d')); LeftBy Rewrite: (mem_extension Hxm).
Step leq_norb: (b, b' : bool) (leq (negb (orb b b')) (negb b)) By Do 2 Case.
Step Edp: (d : gbits)
    (halfg (dp d)) = (addg (halfg p) (halfg (addg (oddg p) (oppg d)))).
  By Move=> d; Rewrite: /dp addgC halfg_add addgC; Congr addg; Rewrite addgC.
Case Dp: (oddg p) Edp => [|||] Edp.
 Move=> Hmp0; Pose dhp := [d](negb (m (addg (halfg p) (oppg d)))).
  Step [d Dd Hd]: {d : gbits | (setC1 d Gb00) & (dhp d)}.
    Move: Hmp0; Rewrite: /matte_order /setC addg0 Hmp.
    Rewrite: -/(dhp Gb01) -/(dhp Gb10) -/(dhp Gb11).
    Case H01: (dhp Gb01); LeftBy Exists Gb01.
    Case H10: (dhp Gb10); LeftBy Exists Gb10.
    By Case H11: (dhp Gb11); LeftBy Exists Gb11.
  Rewrite: ~/dhp in Hd; Case: (Hdp d) => [xm Hxm Dxm]; Exists xm; LeftDone.
  Rewrite: /matte_order /setC !Dxm !Edp !addg0 Hmp !addn0.
  By Case: {}d Dd Hd => [|||] //= _ Hd;
    Rewrite: (negbE Hd) /= ?addn1 ?add1n ?doubleS ?addSn ltnS ?addn0 ?add0n;
    Try Apply leqW; Try Apply leq_add2; Rewrite: ?leq_double; Try Apply leq_add2.
 Case: (Hdp Gb01) => [xm Hxm Dxm] Hmp0; Exists xm; LeftDone.
  Rewrite: {1}/matte_order /setC !Dxm !Edp !addg0 Hmp /= add0n addn0.
  Case Hm01: (m (addg (halfg p) (Gpoint (Znat 0) (Znat -1)))) => //.
  By Rewrite: /matte_order /= /setC Hm01 /= add1n doubleS; Case (xm (dp Gb11)).
 Case: (Hdp Gb00) => [xm Hxm Dxm] Hmp0; Exists xm; LeftDone.
  By Rewrite: {1}/matte_order /setC !Dxm !Edp !addg0 Hmp.
 Case: (Hdp Gb10) => [xm Hxm Dxm] Hmp0; Exists xm; LeftDone.
  Rewrite: {1}/matte_order /setC !Dxm !Edp !addg0 Hmp /= add0n addn0.
  Case Hm01: (m (addg (halfg p) (Gpoint (Znat -1) (Znat 0)))) => //.
  By Rewrite: /matte_order /= /setC Hm01 /= addn1 doubleS; Case (xm (dp Gb11)).
Qed.

End MatteOrder.

Unset Implicit Arguments.


