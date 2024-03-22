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
Require geometry.
Require patch.
Require sew.
Require snip.
Require color.
Require chromogram.
Require coloring.
Require kempe.

Set Implicit Arguments.

(* Dissecting a connected plain map along a proper ring, and its reverse  *)
(* edge-conjugate. This gives a symmetric cover (compare with snip.v,     *)
(* where the construction is asymmetric). The properties established here *)
(* feed directly into birkhoff; the chord constructions are also used in  *)
(* embed when using induction over the disk size of a ring.               *)

Section ProperRing.

(* A proper ring is a non-empty ring that is NOT an edge orbit.           *)
(* A nontrivial ring of order m must have more that m face orbits in both *)
(* its inner and outer face disks.                                        *)

Variables n0 : nat; g : hypermap.
Hypothesis Hg : (plain g).

Definition proper_ring [r : (seq g)] : bool :=
  Cases r of
    (Adds _ (Adds _ (Adds _ _))) => true
  | (Adds x (Adds y Seq0)) => (negb (edge x) =d y)
  | _ => false
  end.

Lemma size_proper_ring : (r : (seq g)) (ltn (2) (size r)) -> (proper_ring r).
Proof. By Move=> [|x [|y [|z r]]]. Qed.

Lemma proper_ring_rot : (r : (seq g)) (proper_ring (rot n0 r)) = (proper_ring r).
Proof.
Move=> r; Case Hr: (ltn (2) (size r)).
  By Rewrite: !size_proper_ring ?size_rot.
Case: {}n0 r Hr => [|[|i]] [|x [|y [|z r]]] //= _.
By Rewrite: -{1 x}plain_eq // eqd_sym (inj_eqd (Iedge g)).
Qed.

Definition nontrivial_ring [m : nat; r : (seq g)] : bool :=
  (andb (ltn m (fcard (!face?) (diskF r)))
        (ltn m (fcard (!face?) (diskFC r)))).

Lemma fcard0P: (a : (set g)) (fclosed face a) ->
  (reflect (EX x | (a x)) (ltn (0) (fcard face a))).
Proof.
Move=> a Ha; Rewrite: ltnNge leqn0; Apply: (iffP set0Pn).
  By Case; Move=> x; Case/andP; Exists x.
Move=> [x Hx]; Exists (froot face x); Rewrite: /setI (roots_root (Sface g)).
By Rewrite: -(closed_connect Ha (connect_root (eqdf face) x)).
Qed.

Lemma fcard1P: (a : (set g)) (fclosed face a) ->
  (reflect (EX x | (a x) & (EX y | (a y) & (negb (cface x y))))
    (ltn (1) (fcard face a))).
Proof.
Move=> a Ha; Rewrite: ltn_neqAle andbC eqd_sym; Apply introP.
  Case/andP; Case/(fcard0P Ha)=> [x Hx] Ha1.
  Rewrite: /n_comp (cardD1 (froot face x)) {1}/setI (roots_root (Sface g)) in Ha1.
  Rewrite: -(closed_connect Ha (connect_root ? x)) Hx in Ha1.
  Case/set0Pn: Ha1; Move=> y; Case/and3P=> [Hxy Dy Hy].
  Exists x; Auto; Exists y; Auto.
  By Rewrite: (sameP (rootPx (Sface g) x y) eqP) (eqP Dy).
Move=> H [x Hx [y Hy Hxy]]; Case/andP: H; Split.
  By Apply/(fcard0P Ha); Exists x.
Rewrite: /n_comp (cardD1 (froot face x)) (cardD1 (froot face y)) {1 2}/setI.
Rewrite:  {1}/setD1 !(roots_root (Sface g)).
Rewrite: -![z](closed_connect Ha (connect_root ? z)).
By Rewrite: Hx Hy (sameP eqP (rootPx (Sface g) x y)) Hxy.
Qed.

Lemma nontrivial0P : (r : (seq g))
  (reflect (EX x | (diskF r x)) /\ (EX x | (diskFC r x))
     (nontrivial_ring (0) r)).
Proof.
Move=> r; Rewrite: /nontrivial_ring.
Case: (fcard0P (diskF_face r)); Move=> HrF.
  Case: (fcard0P (diskFC_face r)); Move=> HrFC; Constructor; LeftBy Split.
  By Move=> [_ H]; Case HrFC.
By Right; Move=> [H _]; Case HrF.
Qed.

Lemma nontrivial1P : (r : (seq g))
  (reflect (EX x | (diskF r x) & (EX y | (diskF r y) & (negb (cface x y))))
        /\ (EX x | (diskFC r x) & (EX y | (diskFC r y) & (negb (cface x y))))
    (nontrivial_ring (1) r)).
Proof.
Move=> r; Rewrite: /nontrivial_ring.
Case: (fcard1P (diskF_face r)); Move=> HrF.
  Case: (fcard1P (diskFC_face r)); Move=> HrFC; Constructor; LeftBy Split.
  By Move=> [_ H]; Case HrFC.
By Right; Move=> [H _]; Case HrF.
Qed.

End ProperRing.

Section RevSnip.

Variable g : hypermap.
Hypothesis Hg: (planar_bridgeless_plain_connected g).
Local Hpg : (planar g) := Hg.
Local Hbg : (bridgeless g) := Hg.
Local HgE : (plain g) := Hg.
Local Hcg : (connected g) := Hg.
Local De2 := (plain_eq Hg).
Local He1 := (plain_neq Hg).

Definition rev_ring [r : (seq g)] : (seq g) := (rev (maps edge r)).

Lemma rev_rev_ring : (r : (seq g)) (rev_ring (rev_ring r)) = r.
Proof.
By Move=> r; Rewrite: /rev_ring maps_rev rev_rev (monic_maps 2!g De2).
Qed.

Lemma proper_rev_ring : (r : (seq g))
  (proper_ring (rev_ring r)) = (proper_ring r).
Proof.
Move=> r; Case Hr: (ltn (2) (size r)).
  By Rewrite: !size_proper_ring /rev_ring ?size_rev ?size_maps.
By Case: r Hr => [|x [|y [|z r]]]; Rewrite: //= De2 eqd_sym.
Qed.

(* We use a redundant assumption to facilitate matching in lemmas *)
(* with dependently typed terms.                                  *)
Hypothesis Hpg' : (planar g).

Variable r : (seq g).
Hypothesis HUr : (scycle rlink r).
Local Hr := (scycle_cycle HUr).
Local UrF := (scycle_simple HUr).
Local Ur := (scycle_uniq HUr).

Lemma mem_rev_ring : (x : g) (rev_ring r x) = (r (edge x)).
Proof.
By Move=> x; Rewrite: -{1 x}De2 /rev_ring mem_rev (mem_maps (Iedge g)).
Qed.

Lemma cycle_rev_ring : (cycle rlink (rev_ring r)).
Proof.
Rewrite: /rev_ring /=; Case Dr: r => [|x p] //; Rewrite (cycle_path x).
Rewrite: -Dr {1 r}Dr /= rev_adds last_add_last; Apply/(pathP x)=> [i Hi].
Rewrite size_rev in Hi; Rewrite: -rev_add_last -maps_add_last.
Rewrite: (sub_rev x Hi); Rewrite: size_maps in Hi.
Rewrite: sub_rev !size_maps size_add_last; RightBy Apply ltnW.
Rewrite: (leq_subS Hi); Pose j := (subn (size r) (S i)).
Step Hj: (ltn j (size r)) By Rewrite: /j -(leq_subS Hi) subSS leq_subr.
Rewrite: !(sub_maps x x) ?size_add_last // /rlink De2 Sface Dr /=.
Def: Hrr := Hr; Rewrite: -(cycle_rot (1)) (cycle_path x) in Hrr.
Move: (pathP x Hrr j); Rewrite: size_rot Hj Dr rot1_adds last_add_last.
Rewrite: -add_last_adds -Dr -cats1 sub_cat Hj /=; Auto.
Qed.

Lemma froot_face_rev_ring :
  (maps (froot face) (rev_ring r)) = (rev (rot (1) (maps (froot face) r))).
Proof.
Rewrite: /rev_ring maps_rev -maps_rot; Congr rev.
Case: {}r {}Hr => [|x0 p] //; Rewrite: rot1_adds /=.
By Elim: p {1 3}x0 => [|y p Hrec] x /=; Move/andP=> [Hx Hp];
   Rewrite: -?(Hrec ? Hp) (rootP (Sface g) Hx).
Qed.

Lemma simple_rev_ring : (simple (rev_ring r)).
Proof.
By Rewrite: /simple froot_face_rev_ring uniq_rev uniq_rot; Case (andP HUr).
Qed.

Lemma scycle_rev_ring : (scycle (!rlink?) (rev_ring r)).
Proof. By Rewrite: /scycle cycle_rev_ring simple_rev_ring. Qed.

Syntactic Definition HUrr := scycle_rev_ring.

Lemma fband_rev_ring : (fband (rev_ring r)) =1 (fband r).
Proof.
Move=> x; Apply/hasP/hasP=> [[y Hy Hxy]].
  Rewrite: mem_rev_ring in Hy.
  Exists (next r (edge y)); LeftBy Rewrite mem_next.
  Apply: (connect_trans Hxy); Rewrite: -{1 y}De2; Exact (next_cycle Hr Hy).
Exists (edge (prev r y)); LeftBy Rewrite: mem_rev_ring De2 mem_prev.
Apply: (connect_trans Hxy); Rewrite Sface; Exact (prev_cycle Hr Hy).
Qed.

Section RingPartitions.

Hypothesis HrE: (proper_ring r).

Lemma pick_in_ring : (EX x | (r x)).
Proof. By Case: {}r HrE => [|x p]; RightBy Exists x; Rewrite: /= setU11. Qed.

Lemma diskN_edge_ring : (x : g) (r x) -> (diskN r (edge x)) = false.
Proof.
Move=> x Hx; Rewrite: diskN_E /setU -(fclosed1 (diskE_edge Hpg HUr)).
Rewrite: /diskE /setD Hx /= orbF; Apply/idP => [Hex].
Step Dex: (edge x) = (next r x).
  By Apply: (scycle_cface HUr (next_cycle Hr Hx) Hex); Rewrite mem_next.
Step Dx: x = (next r (edge x)).
  Apply: (scycle_cface HUr ? Hx); RightBy Rewrite mem_next.
  By Rewrite: -{1 x}De2; Exact (next_cycle Hr Hex).
Case: (rot_to Hx) Dex Dx {}Ur HrE => [i p Dr].
Rewrite: -!(next_rot i Ur) -(proper_ring_rot i) // -(uniq_rot i) ~{i}Dr.
Case: p => [|y [|z p]] Dex; Rewrite: /= ?set11 /eqdf Dex /= ?set11 // /=.
By Move=> Dx; Rewrite: Dx /setU1; Case (y =d x); Rewrite: set11 /= ?orbT.
Qed.

Lemma diskN_rev_ring : (diskN (rev_ring r)) =1 (setC (diskN r)).
Proof.
Case: (pick_in_ring) => [y Hy] x; Rewrite: -(De2 y) in Hy; Rewrite: /setC.
Case: (connected_clink Hcg x (edge y)) Hy => [p Hp []] {y}.
Elim: p x Hp => [|x' p Hrec] x /=.
  Move=> _ Hex; Rewrite: diskN_E /setU mem_rev_ring Hex /= -(De2 x).
  By Rewrite: (diskN_edge_ring Hex).
Case/andP; Move/clinkP=> [Dx | Dx'] Hp.
  Rewrite: Dx -![r'](fclosed1 (diskN_node r') x'); Auto.
Rewrite: diskN_E /setU mem_rev_ring; Case Hrex: (r (edge x)).
  By Clear; Rewrite: -{2 x}De2 (diskN_edge_ring Hrex).
Rewrite: /= diskN_E /setU (fclosed1 (diskE_edge Hpg HUrr)).
Rewrite: (fclosed1 (diskE_edge Hpg HUr)) /diskE /setD Hrex mem_rev_ring De2.
Case: (r x) => //=.
By Rewrite: -(Eface ? x) Dx' De2 -![r'](fclosed1 (diskN_node r') x'); Auto.
Qed.

Lemma diskF_rev_ring :
  (diskF (rev_ring r)) =1 (setD (setC (diskN r)) (fband r)).
Proof. By Move=> y; Rewrite: /setD -diskN_rev_ring -fband_rev_ring. Qed.

Definition chord_ring [x : g] : (seq g) :=
  (Adds x (arc r (fproj r (edge x)) (fproj r x))).

Lemma scycle_chord_ring : (x : g)
  (fband r x) -> (fband r (edge x)) -> (scycle rlink (chord_ring x)).
Proof.
Move=> x Hx Hex; Case: {Hx}(fprojP Hx) {Hex}(fprojP Hex).
Rewrite: /chord_ring; Pose y1 := (fproj r x); Pose y2 := (fproj r (edge x)).
Move=> Hy1 Hxy1 [Hy2 Hxy2]; Step Hy21: (negb y2 =d y1).
  Apply/eqP=> [Dy1]; Case/set0Pn: Hbg; Exists x.
  By Rewrite: (same_cface Hxy1) -Dy1 Sface.
Case (andP HUr); Case: (cat_arc Ur Hy2 Hy1 Hy21) => [i Dr].
Rewrite: /scycle /simple -(uniq_rot i) -maps_rot -(cycle_rot i) -Dr.
Case: (head_arc Hy2 Hy21) => [p2 []]; Def Dq2: q2 := (Adds y2 p2).
Rewrite eqd_sym in Hy21; Case: (head_arc Hy1 Hy21) => [p1 []].
Rewrite: -cat_add_last maps_cat uniq_cat; Move=> Hp; Move/andP=> [Up2 _].
Rewrite: -rot1_adds maps_rot uniq_rot /= -(rootP (Sface g) Hxy1) in Up2.
Rewrite: /= ~Up2 andbT -cats1 path_cat Dq2 /= {1 3}/rlink Hxy2 /=.
Rewrite: Sface (same_cface Hxy1) Sface.
By Rewrite: Dq2 /= -?cats1 !path_cat -andbA in Hp; Case (and3P Hp).
Qed.

Variable x : g.

Hypotheses HxE : (diskE r x); Hx : (fband r x); Hex : (fband r (edge x)).

Remark HdEr : (y : g) (diskE r y) = (diskE r (edge y)).
Proof. Exact (fclosed1 (diskE_edge Hpg HUr)). Qed.
Remark Heex: (fband r (edge (edge x))). Proof. By Rewrite: De2 Hx. Qed.
Remark HexE : (diskE r (edge x)). Proof. By Rewrite: -HdEr HxE. Qed.

Local x1 : g := (fproj r x).
Local x2 : g := (fproj r (edge x)).
Remark Hx1 : (r x1). Proof. By Case (fprojP Hx). Qed.
Remark Hx2 : (r x2). Proof. By Case (fprojP Hex). Qed.
Remark Hxx1 : (cface x x1). Proof. By Case (fprojP Hx). Qed.
Remark Hxx2 : (cface (edge x) x2). Proof. By Case (fprojP Hex). Qed.
Remark Hx12 : (negb x1 =d x2).
Proof.
Apply/eqP=> [Dx1]; Case/set0Pn: Hbg; Exists x.
By Rewrite: (same_cface Hxx1) Dx1 Sface Hxx2.
Qed.

Local r1 : (seq g) := (arc r x1 x2).
Local r2 : (seq g) := (arc r x2 x1).
Local ix : nat := let (i, _) = (cat_arc Ur Hx1 Hx2 Hx12) in i.
Remark Dr : (rot ix r) = (cat r1 r2).
Proof. By Rewrite: /ix; Case (cat_arc Ur Hx1 Hx2). Qed.
Remark Er : r =1 (setU r1 r2).
Proof. By Move=> y; Rewrite: -mem_cat -Dr mem_rot. Qed.
Remark Dr1 : {p1 : (seq g) | (Adds x1 p1) = r1}.
Proof. Exact (head_arc Hx1 Hx12). Qed.
Remark Dr2 : {p2 : (seq g) | (Adds x2 p2) = r2}.
Proof. By Apply: (head_arc Hx2 ?); Rewrite: eqd_sym Hx12. Qed.

Local cr1 : (seq g) := (chord_ring x).
Local cr2 : (seq g) := (chord_ring (edge x)).
Lemma Dcr1 : cr1 = (Adds x r2). Proof. Done. Qed.
Lemma Dcr2 : cr2  = (Adds (edge x) r1).
Proof. By Rewrite: /cr2 /chord_ring De2. Qed.

Remark HdEr1 : (y : g) (diskE cr1 y) = (diskE cr1 (edge y)).
Proof. Exact (fclosed1 (diskE_edge Hpg (scycle_chord_ring Hx Hex))). Qed.
Remark HdEr2 : (y : g) (diskE cr2 y) = (diskE cr2 (edge y)).
Proof. Exact (fclosed1 (diskE_edge Hpg (scycle_chord_ring Hex Heex))). Qed.

Lemma proper_chord_ring : (proper_ring cr1).
Proof.
Rewrite Dcr1; Case: {}Dr2 => [[|z p] []] //=.
By Apply/eqP=> [Dx2]; Case/andP: HexE; Rewrite: Dx2 Hx2.
Qed.

Lemma diskN_chord_ring : (diskN cr1) =1 (setD (diskN r) (diskN cr2)).
Proof.
Move=> y; Cut (addn (diskN cr1 y) (diskN cr2 y)) = (diskN r y).
  By Rewrite: /setD; Case (diskN cr1 y); Case (diskN cr2 y); Case (diskN r y).
Case: (connected_clink Hcg x y) => [p Hp []] {y}.
Elim/last_ind: p Hp => [|p y Hrec] /=.
  Clear; Rewrite: !diskN_E /setU HxE orbT HdEr2 {1 cr2}Dcr2 /diskE /setD.
  By Case (andP HxE); Rewrite: /= !setU11 /= /setU1 He1 Er /setU; Case (r1 x).
Rewrite: last_add_last -cats1 path_cat ![r'](fclosed1 (diskN_node r') y).
Move/and3P=> [Hp Dy _]; Case/clinkP: Dy {Hrec Hp}(Hrec Hp) => [[]|Dy]; Auto.
Rewrite: -{(last x p)}Eface ~{p}Dy; Move/node: y => y.
Rewrite: !diskN_E {1 2 4 5 6}/setU {1 3 cr1}Dcr1 {1 3 cr2}Dcr2 /= /setU1.
Rewrite:  -{1 x}De2 !(inj_eqd (Iedge g)).
Case: (x =P y) => [[]| _].
  Clear; Rewrite: HdEr2 HxE He1 /= /diskE /setD /= setU11 orbT /=.
  By Case/andP: HxE; Rewrite: Er /setU; Case (r1 x).
Case: ((edge x) =P y) => [[]|_].
  Clear; Rewrite: HexE HdEr1 /diskE /setD /= De2 setU11 orbT /=.
  By Case (andP HexE); Rewrite: Er /setU orbC; Case (r2 (edge x)).
Case Hry: (r y).
  Rewrite: -diskN_E (diskN_edge_ring Hry) -HdEr1 -HdEr2 /= orbC.
  Case: (diskE cr1 y) => //=; Rewrite: orbC addnC.
  Case: (diskE cr2 y) => //= [] _.
  Move: {}Ur Hry; Rewrite: -(uniq_rot ix) Er Dr uniq_cat /setU !orbF.
  Case/and3P=> [_ Hr12 _].
  Case Hr2: (r2 y); LeftBy Rewrite (negbE (hasPn Hr12 y Hr2)).
  By Rewrite orbF; Move=> H; Rewrite: H.
Rewrite: Er /setU in Hry; Case: (r1 y) Hry => [|] H //; Rewrite: ~H /=.
Rewrite: (HdEr y) (HdEr1 y) (HdEr2 y) {3 6}/diskE /setD /setU.
Case Hrey: (r (edge y)); Rewrite: Er /setU in Hrey.
  Case/orP: Hrey; Move=> Hrey; Rewrite: Hrey /= orbC.
    Case: (diskE cr1 (edge y)) => //=.
    By Rewrite: /diskE /setD Dcr2 /= /setU1 Hrey orbT.
  Case: (diskE cr2 (edge y)); LeftBy Rewrite addnC.
  By Rewrite: /diskE /setD Dcr1 /= /setU1 Hrey orbT.
By Case/norP: Hrey => [H H']; Rewrite: (negbE H) (negbE H').
Qed.

Lemma fband_chord_ring : (setU (fband cr1)  (fband cr2)) =1 (fband r).
Proof.
Move=> y; Apply/orP/hasP.
  Rewrite: /fband; Case; Move/hasP=> [z Hz Hyz];
  (Rewrite: ?Dcr1 ?Dcr2 /= in Hz; Case/setU1P: Hz => [Dz | Hz];
    RightBy Exists z; LeftBy Rewrite: Er /setU Hz ?orbT);
  [Exists x1 | Exists x2]; Rewrite: ?(same_cface Hyz) -?Dz;
  [Exact Hx1 | Exact Hxx1 | Exact Hx2 | Exact Hxx2].
Move=> [z Hz Hyz]; Rewrite: Er in Hz.
Case/orP: Hz => [Hz | Hz]; [Right | Left]; Apply/hasP;
By Exists z; Rewrite: // /= /setU1 ?De2 -/x1 -/x2 Hz orbT.
Qed.

Lemma diskF_chord_ring : (diskF cr1) =1 (setD (diskF r) (diskF cr2)).
Proof.
Move=> y; Rewrite: {2 3}/diskF /setD -fband_chord_ring /setU.
Case HyF: (fband cr2 y).
  Rewrite: /fband in HyF; Case/hasP: HyF => [z Hz Hyz].
  Rewrite: [r'](closed_connect (diskF_face r') Hyz) /diskF /setD.
  By Rewrite: diskN_chord_ring /setD diskN_E /setU Hz orbT /= andbF.
Rewrite: /diskF /setD diskN_chord_ring.
By Case (fband cr1 y); Rewrite: // /= ?andbF.
Qed.

Lemma nontrivial_chord_ring :
  (negb x2 =d (next r x1)) -> (EX y | (diskF cr1 y)) ->
  (nontrivial_ring (0) cr1) /\ (ltn (size cr1) (size r)).
Proof.
Rewrite: -(next_rot ix Ur) -(size_rot ix r) Dr.
Case: (Dr1) => [[|x3 p1] Dp1]; Rewrite: -Dp1.
  By Case: (Dr2) => [p2 []]; Rewrite: /= !set11.
Move=> _ Hcr1F; Split; RightBy Rewrite: size_cat Dcr1 /= !addSnnS leq_addl.
Apply/(nontrivial0P ?); Split; Auto.
Exists x3; Apply/andP; Split.
  Step Hx3: (r x3) By Rewrite: Er -Dp1 /setU /= /setU1 set11 /= orbT.
  Def: Ux3 := Ur; Rewrite: -(uniq_rot ix) Dr -Dp1 /= mem_cat in Ux3.
  Case/and3P: Ux3; Move/norP=> [Ux31 _]; Move/norP=> [_ Ux3] _.
  Apply/hasP=> [[y Hy Hyx3]]; Rewrite: Dcr1 /= in Hy.
  Case/setU1P: Hy => [Dy | Hy].
    Case/eqP: Ux31; Apply: (scycle_cface HUr ? Hx3 Hx1).
    By Rewrite: (same_cface Hyx3) -Dy Hxx1.
  Case: (negP Ux3); Rewrite: (scycle_cface HUr Hyx3 Hx3) //.
  By Rewrite: Er /setU Hy orbT.
Rewrite: /setC diskN_chord_ring /setD diskN_E /setU {1 cr2}Dcr2 -Dp1 /=.
By Rewrite: /setU1 set11 /= !orbT.
Qed.

End RingPartitions.

Section NonTrivialRing.

Variable m : nat.
Hypothesis Hm : (nontrivial_ring m r).

Lemma nontrivial_ring_proper : (proper_ring r).
Proof.
Case Dr: {1 3}r (andP Hm) => [|x r'] [Hm1 Hm2].
  Rewrite: /n_comp -(!eq_card g set0) ?card0 // in Hm1.
  By Move=> y; Rewrite: /setI andbC.
Case: r' Dr {Hm1} => [|ex [|z r']] Dr //.
  By Move: {}Hr; Rewrite: Dr /= /rlink Sface (set0P Hbg).
Apply/eqP=> [Dex]; Rewrite: /n_comp -(!eq_card g set0) ?card0 // in Hm2.
Move{Hm2}=> y; Cut (diskN r y) = true.
  By Move=> Hy; Rewrite: /setI /diskFC /setC /setD Hy /= !andbF.
Case: (connected_clink Hcg x y) => [p Hp []] {y}.
Step Hrx: (r x) By Rewrite: Dr /= setU11.
Elim/last_ind: p Hp => [|p y Hrec]; LeftBy Rewrite: /= diskN_E /setU Hrx.
Rewrite: last_add_last -cats1 path_cat (fclosed1 (diskN_node r)).
Move/and3P=> [Hp Dy _]; Apply: etrans (Hrec Hp) {Hrec Hp}.
Case/clinkP: Dy => [[] | Dy] //; Rewrite: -{(last x p)}Eface Dy !diskN_E /setU.
Rewrite: -(fclosed1 (diskE_edge Hpg HUr)); Congr orb.
By Rewrite: Dr -Dex /= /setU1 !orbF -{3 x}De2 !(inj_eqd (Iedge g)) orbC.
Qed.

Lemma nontrivial_rev_ring : (nontrivial_ring m (rev_ring r)).
Proof.
Case: (andP Hm) (diskN_rev_ring nontrivial_ring_proper) => [Hm1 Hm2] HrN.
Def: HrF := fband_rev_ring; Apply/andP; Split; [Move: Hm2 | Move: Hm1];
  Apply: etrans; Congr leq; Apply: eq_n_comp_r => [x].
  By Rewrite: /diskFC /setD -HrN -HrF.
By Rewrite: /diskFC /setD /setC HrN HrF /setC negb_elim.
Qed.

Syntactic Definition gd := (snip_disk Hpg' HUr).
Syntactic Definition bgd := (snipd_ring Hpg' HUr).
Local pfd [x : g] : (set gd) := (preimage [y : gd](snipd y) (cface x)).

Remark pfdP : (x : g; y : gd) (cface x (snipd y)) ->
    (EX z | (Some ? z) = (pick (pfd x)) & (cface y z)).
Proof.
Move=> x y Hy; Case: (pickP (pfd x)) => [z Hz | Ha]; RightBy Case/idP: (Ha y).
Exists z; Rewrite: //= Sface in Hy *.
By Apply: (etrans (esym (cface_snipd ? ?)) (connect_trans ? Hz)).
Qed.

Definition rev_snipd_disk : hypermap := (snip_disk Hpg' HUrr).

Definition rev_snipr_disk : hypermap := (snip_rem Hpg' HUrr).

Definition rev_snipd_ring : (seq rev_snipd_disk) := (snipd_ring Hpg' HUrr).

Definition rev_snipr_ring : (seq rev_snipr_disk) := (snipr_ring Hpg' HUrr).

Lemma rev_snipr_ring_eq :
  (maps (snipr 4!?) rev_snipr_ring) = (maps edge r).
Proof. By Rewrite: /rev_snipr_ring maps_snipr_ring /rev_ring rev_rev. Qed.

Syntactic Definition grd := rev_snipd_disk.
Syntactic Definition bgrd := rev_snipd_ring.
Syntactic Definition grr := rev_snipr_disk.
Syntactic Definition bgrr := rev_snipr_ring.
Local pfrr [x : g] : (set grr) := (preimage [y : grr](snipr y) (cface x)).

Remark pfrrP : (x : g; y : grr) (cface x (snipr y)) ->
  (EX z | (Some ? z) = (pick (pfrr x)) & (cface y z)).
Proof.
Move=> x y Hy; Case: (pickP (pfrr x)) => [z Hz | Ha]; RightBy Case/idP: (Ha y).
Exists z; Rewrite: //= Sface in Hy.
By Apply: (etrans (patch_face_r (snip_patch ? ?) ? ?) (connect_trans ? Hz)).
Qed.

Lemma rev_ring_cotrace : (et : colseq)
  (ring_trace bgd et) <-> (ring_trace (rotr (1) bgrr) et).
Proof.
Pose pd := bgd; Pose pr := (rotr (1) bgrr).
Step Efp : (maps (froot face) (maps (snipr 4!?) pr))
              = (maps (froot face) (maps (snipd 4!?) pd)).
  Rewrite: /pd maps_snipd_ring // /pr !maps_rotr /rev_snipr_ring.
  Rewrite: /rev_snipr_disk maps_snipr_ring maps_rev.
  By Rewrite: froot_face_rev_ring rev_rev rotr_rot.
Move=> et; Split.
  Move=> [k [HkE HkF] Det]; Rewrite: ~{et}Det.
  Pose k' := [x : grr]if pick y in (pfd (snipr x)) then (k y) else Color0.
  Def: Hppgr := (snip_patch Hpg' HUrr).
  Step HgrrE: (plain grr) By Move: {}HgE; Rewrite: (plain_patch Hppgr); Case/andP.
  Step Hk'F : (invariant face k') =1 grr.
    Move=> x; Apply/eqcP; Rewrite: /setA /k' -(eq_pick 2!(pfd (snipr x))) //.
    By Move=> y; Apply: same_cface {y}; Rewrite: -(patch_face_r Hppgr) fconnect1.
  Step Hk'E: (x : grr)
     (rev_ring r (snipr x)) = false -> ((k' (edge x)) =d (k' x)) = false.
    Move=> [x Hx]; Rewrite: /k' /=; Move=> Hxr.
    Rewrite: /setC /diskE /setD Hxr /= in Hx.
    Rewrite: (diskN_rev_ring nontrivial_ring_proper) /= /setC negb_elim in Hx.
    Rewrite: -(codom_snipd Hpg' HUr) in Hx.
    Case/set0Pn: Hx => [xd Dx]; Rewrite: /preimage in Dx.
    Case (!pfdP x xd); LeftBy Rewrite: -(eqP Dx) connect0.
    Move=> yd /= [] Hyd; Rewrite: -~{yd Hyd}(fconnect_invariant HkF Hyd).
    Pose fexd := (face (edge xd)); Case: (!pfdP (edge x) fexd).
      Rewrite: (eqP Dx) -{1 xd}Eedge -/fexd cface1.
      By Case: fexd => [y Hy]; Rewrite: /= Enode connect0.
    Move=> yd /= [] Hyd; Rewrite: /fexd -(!cface1 gd) in Hyd.
    Rewrite: -~{yd Hyd}(fconnect_invariant HkF Hyd); Apply: HkE.
  Exists k'; [Split; Auto | Idtac].
    Move=> xr; Case Hxr: (rev_ring r (snipr xr)); RightBy Apply: Hk'E.
    Rewrite: /invariant eqd_sym -{1 xr}(plain_eq HgrrE); Apply: Hk'E.
    Case: xr Hxr => [x H] {H}/=; Rewrite: !mem_rev_ring.
    Move=> Hex; Move: (diskN_edge_ring nontrivial_ring_proper Hex).
    By Rewrite: diskN_E; Case/norP; Move/negbE.
  Congr trace; Elim: pd pr Efp => [|xd pd Hrec] [|xr pr] //=.
  Injection=> Hp; Move/(introT (rootP (Sface g))) => Hxrd; Congr Adds; Auto.
  Case: (pfdP Hxrd); Rewrite: /k' /=; Move=> yd [] Hyd.
  Exact (fconnect_invariant HkF Hyd).
Move=> [k' [Hk'E Hk'F] Det]; Rewrite: ~{et}Det.
Pose k := [x : gd]if pick y in (pfrr (snipd x)) then (k' y) else Color0.
Step HkF : (invariant face k) =1 gd.
  Move=> x; Apply/eqcP; Rewrite: /setA /k -(eq_pick 2!(pfrr (snipd x))) //.
  By Move=> y; Apply: same_cface {y}; Rewrite: cface_snipd fconnect1.
Exists k; [Split; Auto | Idtac].
  Move=> x; Rewrite: /invariant -(eqcP (HkF (edge x))) -{2 x}Eedge.
  Move: {x}(face (edge x)) => [x Hx]; Rewrite: /k /=.
  Def: Hxr := (codom_snipr Hpg' HUrr (node x)).
  Rewrite: /setC /diskE /setD in Hxr.
  Rewrite: (diskN_rev_ring nontrivial_ring_proper) /setC in Hxr.
  Rewrite: -(fclosed1 (diskN_node r)) ~Hx andbF /= in Hxr.
  Case/(set0Pnx 1!grr ?): Hxr; Move=> nxr; Move/eqP => Dnx.
  Case: (!pfrrP (node x) nxr); LeftBy Rewrite: Dnx connect0.
  Move=> yr /= [] Hyr; Rewrite: -~{yr Hyr}(fconnect_invariant Hk'F Hyr).
  Pose enxr := (edge nxr); Case: (!pfrrP x enxr).
    Rewrite: -{1 x}Enode Dnx /enxr -cface1.
    By Case: {}nxr => /= *; Rewrite: connect0.
  Move=> yr /= [] Hyr; Rewrite: -~{yr Hyr}(fconnect_invariant Hk'F Hyr).
  Apply: Hk'E.
Congr trace; Elim: pd pr Efp => [|xd pd Hrec] [|xr pr] //=.
Injection=> Hp; Move/(introT (rootP (Sface g))) => Hxr; Congr Adds; Auto.
Rewrite Sface in Hxr; Case: (pfrrP Hxr); Rewrite: /k /=; Move=> yr [] Hyr.
Exact (fconnect_invariant Hk'F Hyr).
Qed.

Lemma ring_disk_closed : (cubic g) -> (kempe_closed (ring_trace bgd)).
Proof.
Move=> HgN; Def: Hppgr := (snip_patch Hpg' HUrr).
Step Hbgrr: (ucycle_planar_plain_quasicubic (rotr (1) bgrr)).
  Split; RightBy Exact (planar_snipr Hpg' HUrr).
  Split; RightBy Rewrite: /ucycle cycle_rotr uniq_rotr; Case Hppgr.
  Split; LeftBy Move: {}HgE; Rewrite: (plain_patch Hppgr); Case/andP.
  Move: HgN; Rewrite: (cubic_patch Hppgr); Case/andP; Clear; Apply: etrans.
  By Apply: eq_subset => [x]; Rewrite: /setC mem_rotr.
Move=> et; Case: (rev_ring_cotrace et) => [H _]; Move/H {H} => Hetr.
Case: (kempe_map Hbgrr Hetr) => [Hget [w Hw Hwet]]; Split.
  Move=> ge; Case: (rev_ring_cotrace (permt ge et)); Auto.
Exists w; Auto; Move=> et' Hwet'; Case (rev_ring_cotrace et'); Auto.
Qed.

Lemma colorable_from_ring : (et : colseq)
  (ring_trace bgd et) -> (ring_trace bgrd (rev et)) -> (four_colorable g).
Proof.
Move=> et Hetr Hetd; Def: Hppgr := (snip_patch Hpg' HUrr).
Case: (colorable_patch Hppgr) => [_ H]; Apply: H {H}.
Case: (rev_ring_cotrace et) => [H _]; Case: {H Hetr}(H Hetr) => [k Hk Det].
Exists (rev et); LeftDone; Rewrite rev_rev; Exists k; Auto.
By Rewrite: Det -!urtrace_trace -urtrace_rot -maps_rot rot_rotr.
Qed.

Lemma ring_disk_chord : (negb (chordless bgd)) ->
  (EX r' | (scycle rlink r')
         & (!nontrivial_ring g (0) r') /\ (ltn (size r') (size r))).
Proof.
Def: Ird := (!inj_snipd ? Hpg' ? HUr); Def: Drd := (maps_snipd_ring Hpg' HUr).
Move/andP: (ucycle_snipd_ring Hpg' HUr) => [_ Urd].
Step Erd: (xd, yd : gd) (xd =d yd) = ((snipd xd) =d (snipd yd)) By Done.
Step EdN: (xd : gd) (snipd (node xd)) = (node (snipd xd)) By Done.
Case/set0Pn; Move=> xd; Case/andP; Move=> Hrx.
Rewrite: -(mem_maps Ird) maps_snipd_ring in Hrx.
Case/set0Pn; Move=> yd; Case/andP; Rewrite: /adj; Case/hasP; Move=> zd.
Rewrite: {1}/rlink cface1 -fconnect_orbit -{1 zd}Eedge -!cface_snipd ~EdN.
Case: {zd}(face (edge zd)) => [] z /=.
Rewrite: (fclosed1 (diskN_node r)) -{3 z}Enode -cface1.
Move/node: z => z HzN Hxz Hzy; Case/and3P.
Rewrite: !~Erd -(next_maps Ird Urd) -(prev_maps Ird Urd) -(mem_maps Ird) ~Drd.
Move/snipd: yd Hzy {Ird Urd} => y Hzy.
Move/snipd: xd Hrx Hxz => x Hrx Hxz Hrxy Hryx Hry.
Rewrite: eqd_sym -(monic2F_eqd (prev_next Ur)) in Hryx.
Step HzF: (fband r z) By Apply/hasP; Exists x; Rewrite: // Sface.
Step HezF: (fband r (edge z)) By Apply/hasP; Exists y.
Step HzE: (diskE r z).
  Apply/andP; Split; RightDone; Apply/idP=> [Hrz]; Case/idP: Hrxy.
  Rewrite: (scycle_cface HUr Hxz Hrx Hrz); Apply/eqP.
  Apply (scycle_cface HUr); Auto; RightBy Rewrite mem_next.
  Rewrite: Sface -(same_cface Hzy); Exact (next_cycle Hr Hrz).
Step HezE: (diskE r (edge z)) By Rewrite: -(fclosed1 (diskE_edge Hpg' HUr)).
Def: HrF := (scycle_fproj HUr).
Step EzF: (fproj r z) = x By Rewrite: -(fproj_cface r Hxz) HrF.
Step EezF: (fproj r (edge z)) = y By Rewrite: (fproj_cface r Hzy) HrF.
Def: HrE := nontrivial_ring_proper.
Case: (elimT (fcard0P (diskF_face r))).
  By Apply: (!leq_trans (S m) (1) ? (leq0n m) ?); Case (andP Hm).
Move=> t Ht; Case Htz: (diskF (chord_ring z) t).
  Exists (chord_ring z); LeftBy Apply scycle_chord_ring.
  Apply nontrivial_chord_ring; Auto; RightBy Exists t.
  By Rewrite: EzF EezF eqd_sym.
Exists (chord_ring (edge z)); LeftBy Apply scycle_chord_ring; Rewrite: ?De2.
Apply nontrivial_chord_ring; Rewrite: ?De2; Auto.
  By Rewrite: EzF EezF eqd_sym.
By Exists t; Rewrite: (diskF_chord_ring HrE) ?De2 // /setD Htz.
Qed.

End NonTrivialRing.

End RevSnip.

Unset Implicit Arguments.

