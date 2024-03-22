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
Require color.
Require chromogram.
Require coloring.
Require patch.
Require snip.
Require revsnip.
Require kempe.
Require birkhoff.
Require contract.

Set Implicit Arguments.

(* This is the heart of the proof: we build an injective embedding of a *)
(* configuration map from the partial embedding constructed by the part *)
(* quiz, and derive a contradiction from the reducibility property.     *)

Section Embeddings.

Variables gm, gc : hypermap; rc, cc : (seq gc); h : gc -> gm.

Local rrc : (seq gc) := (rev rc).
Syntactic Definition ac := (kernel rc).
Syntactic Definition bc := (setC rc).
Local Hacbc := (subsetP (kernel_off_ring rc)).
Local HacF := (kernelF rc).

Hypothesis Hgm : (minimal_counter_example gm).
Hypothesis Hgc : (embeddable rc).
Hypothesis Hh : (preembedding ac h).
Hypothesis Hcc : (c_reducible rc cc).

Local Hpgm : (planar gm) := Hgm.
Local Hbgm := (bridgeless_cface Hgm).
Local HgmE : (plain gm) := Hgm.
Local De2m := (plain_eq Hgm).
Local Dn3m := (cubic_eq Hgm).
Local HgmF : (pentagonal gm) := Hgm.
Local Hgm' : (planar_bridgeless_plain_connected gm) := Hgm.

Local Hpgc : (planar gc) := Hgc.
Local Hbgc := (bridgeless_cface Hgc).
Local HgcE : (plain gc) := Hgc.
Local HgcN : (quasicubic rc) := Hgc.
Local De2c := (plain_eq Hgc).
Local Dn3c := (quasicubic_eq HgcN).
Local Hgc' : (planar_bridgeless_plain_connected gc) := Hgc.
Local HUrc : (sfcycle node rc) := Hgc.
Local Hrc := (scycle_cycle HUrc).
Local Urc := (scycle_uniq HUrc).
Local UrcF := (scycle_simple HUrc).

Syntactic Definition hc := (edge_central h).
Local HhcE := (edge_central_edge h Hgc Hgm).
Local HhF := (preembedding_face Hh).
Syntactic Definition Hhac := (preembedding_simple_path Hh HacF).

Lemma embed_functor :
  (x : gc) (ac x) -> (ac (edge x)) -> (h (edge x)) = (edge (h x)).
Proof.
Cut ~(EX x | (setD ac hc x) & (EX p |
  (scycle rlink (Adds x p)) & (sub_set p (setI ac hc)))).
  Move=> H x Hx Hex; Apply: eqP; Apply/idPn=> [Hhex]; Case: H.
  Exists x; LeftBy Rewrite: /setD /edge_central Hhex.
  Case: {Hx Hex Hhex}(Hhac ? ? Hex Hx) => [p]; Case; Case/lastP: p => // [p y].
  Rewrite: last_add_last; Move=> Hp Hyx _ [Up Hpac]; Exists p.
    Apply/andP; Split.
      By Move: Hp; Rewrite: /= -!cats1 !path_cat /= (rlinkFr Hyx).
    By Rewrite: simple_adds -(closed_connect (fbandF p) Hyx) -simple_add_last.
  By Move=> z Hz; Apply: (allP Hpac); Rewrite: mem_add_last; Apply: setU1r.
Cut ~(EX x | (negb (hc x)) &
        (EX p | (scycle rlink (Adds x p)) &
                (sub_set p hc) /\ (sub_set (diskN (Adds x p)) ac))).
  Move=> H [x Hx [p HUp Hpac]]; Case: H; Case/andP: Hx => [HxE Hx].
  Step Hxpac: (sub_set (Adds x p) ac).
    By Move=> y; Case/setU1P=> [[] | Hy] //; Case (andP (Hpac ? Hy)).
  Case HpN: (negb (has (diskF (Adds x p)) rc)).
    Exists x; LeftDone; Exists p; Auto; Split.
      By Move=> y Hy; Case (andP (Hpac ? Hy)).
    Move=> y Hy; Case HyF: (fband (Adds x p) y).
      Rewrite: /fband in HyF; Case/hasP: HyF => [z Hz Hyz].
      By Rewrite: (closed_connect HacF Hyz); Auto.
    Apply/hasP=> [[z Hz Hyz]]; Case/hasP: HpN; Exists z; LeftDone.
    By Rewrite: -(closed_connect (diskF_face (Adds x p)) Hyz) /diskF /setD HyF.
  Step Erp1: (rev_ring (rot (1) (Adds x p))) = (Adds (edge x) (rev_ring p)).
    By Rewrite: {1}/rev_ring maps_rot /= rot1_adds rev_add_last.
  Step HUp1: (scycle rlink (rot (1) (Adds x p))) By Rewrite scycle_rot.
  Exists (edge x); [By Rewrite: HhcE | Exists (rev_ring p)].
    By Rewrite: -Erp1; Apply scycle_rev_ring.
  Split; Move=> y Hy.
    Rewrite: mem_rev_ring // in Hy.
    By Case: (andP (Hpac ? Hy)); Rewrite HhcE.
  Rewrite: -Erp1 (diskN_rev_ring Hgc' HUp1) in Hy.
    Apply/hasP=> [[z Hz Hyz]]; Case HzF: (diskF (Adds x p) z).
      Rewrite: -(closed_connect (diskF_face (Adds x p)) Hyz) in HzF.
      Case/andP: HzF => [_ HyN]; Rewrite: /diskN in HyN.
      Case/hasP: HyN => [y' Hy' Hyy'].
      Case/hasP: Hy; Exists y'; LeftBy Rewrite mem_rot.
      Apply: etrans Hyy'; Apply: eq_connect {y' Hy'} => [y1 y2].
      By Rewrite: /dlink mem_rot.
    Case/andP: HzF {y Hy Hyz}; Split.
      Apply/hasP=> [[y Hy Hyz]].
      By Case/hasP: (Hxpac ? Hy); Exists z; Rewrite: 1?Sface.
    Case/hasP: HpN => [z' Hz' Hz'N]; Rewrite: -(fconnect_cycle Hrc Hz) in Hz'.
    By Rewrite: (closed_connect (diskN_node (Adds x p)) Hz'); Case/andP: Hz'N.
  Rewrite: proper_ring_rot //.
  Case: {}p HUp Hpac => [|x' [|x'' p']] //.
    By Rewrite: /scycle /= /rlink Sface Hbgc.
  Move=> _ H; Apply/eqP=> [Dx']; Move: {H}(H ? (setU11 ? ?)).
  By Rewrite: /setI -Dx' HhcE (negbE HxE) andbF.
Move=> [x HxE [p HUp [HpE Hpac]]]; Pose n := (S (card (diskN (Adds x p)))).
Move: (leqnn n) HUp HpE Hpac; Rewrite: {1}/n.
Elim: n x HxE p => [|n Hrec] // x HxE p Hn HUp HpE.
Pose xp := (Adds x p); Move=> Hpac.
Step HxN: (diskN xp x) By Rewrite: diskN_E /setU /xp /= setU11.
Step HnxN: (diskN xp (node x)) By Rewrite: -(fclosed1 (diskN_node xp)).
Step HnnxN: (diskN xp (node (node x))) By Rewrite: -(fclosed1 (diskN_node xp)).
Case: (andP HUp) => [Hp]; Move/simple_uniq=> Up.
Case Dp': p {}Hp => [|x' p']; LeftBy Rewrite: /= /rlink Sface Hbgc.
Clear; Pose enx := (edge (node x)); Pose p1 := (add_last p enx).
Step Hp1: (path (!rlink?) x p1).
  Rewrite: /p1 -cats1 path_cat /= {2}/rlink cface1r /enx Enode.
  By Rewrite: /= -cats1 path_cat in Hp.
Step Up1: (simple p1).
  Step Henxx: (cface enx x) By Rewrite: cface1 /enx Enode connect0.
  Rewrite: /p1 simple_add_last (closed_connect (fbandF p) Henxx) -simple_adds.
  By Case (andP HUp).
Case HnxE: (hc (node x)).
  Move: (cubicP HgcN ? (Hacbc (Hpac ? HxN))) => [Dn3x Hnxx].
  Case HnnxE: (hc (node (node x))).
    Case/eqP: HxE; Apply Iface; Apply: (etrans ? (Dn3m ?)).
    Do 2 (Apply Iedge; Apply Iface); Rewrite: !Enode Eedge -{1 x}Dn3x -HhF.
      Rewrite: Enode -(eqP HnnxE) -HhF.
        Rewrite: Enode -(eqP HnxE) -HhF ?Enode //.
        Rewrite: /kernel /setC (fclosed1 (fbandF rc)) Enode; Exact (Hpac ? HxN).
      Rewrite: /kernel /setC (fclosed1 (fbandF rc)) Enode; Exact (Hpac ? HnxN).
    Rewrite: /kernel /setC (fclosed1 (fbandF rc)) Enode; Exact (Hpac ? HnnxN).
  Pose ennx := (edge (node (node x))).
  Pose i := (find (cface ennx) p1); Pose q := (Adds ennx (take i p1)).
  Step Hi: (leq i (size p1)) By Apply: find_size.
  Step HUq: (scycle rlink q).
    Step Hp1': (path rlink ennx p1).
      Move: Hp1; Rewrite: -(drop0 p1) (drop_sub x) ?sub0 /=.
        By Rewrite: /= {1 3}/rlink -{1 x}Dn3x cface1 /ennx Enode De2c.  
      By Rewrite: /p1 size_add_last.
    Apply/andP; Rewrite: leq_eqVlt orbC in Hi; Move: Hi Hp1' {Hp1} Up1.
    Case Hi: (ltn i (size p1)).
      Rewrite: -(cat_take_drop (S i) p1) (take_sub x Hi); Move=> _ Hp1 Up1.
      Rewrite: /i -has_find in Hi; Move: {Hi}(sub_find x Hi) => Hi.
      Rewrite: -cats1 !path_cat /= {2}/rlink Sface -(same_cface Hi) in Hp1.
      Rewrite: simple_cat simple_add_last in Up1; Case/andP: Up1 => [Up1 _].
      Split; RightBy Rewrite: /q simple_adds [q'](closed_connect (fbandF q') Hi).
      By Rewrite: /= -cats1 path_cat /= {2}/rlink Sface; Case/andP: Hp1.
    Move=> Di Hp1 Up1; Rewrite: /q (eqnP Di) take_size (cycle_path x) /=.
    Rewrite: Hp1 {1}/p1 last_add_last /rlink /enx {1}/ennx cface1r Enode De2c.
    Split; LeftBy Rewrite connect0.
    Apply/andP; Split; [Apply/mapsP=> [[y Hy Hyennx]] | Done].
    Rewrite: /i -has_find in Hi; Case/hasP: Hi.
    By Exists y; RightBy Apply/(rootP (Sface ?)).
  Step Hp1E: (sub_set (take i p1) hc).
    Move=> y Hy'.
    Step Hy: (p1 y) By Rewrite: -(cat_take_drop i p1) mem_cat /setU Hy'.
    Rewrite: /p1 mem_add_last in Hy; Case/setU1P: Hy; RightBy Auto.
    By Case; Rewrite: /enx HhcE.
  Step Hqx: (diskN q x) = false.
    Rewrite: 2!(fclosed1 (diskN_node q)) -{(node (node x))}De2c.
    Apply: (diskN_edge_ring Hgc' HUq ? (setU11 ? ?)).
    Rewrite: /q; Case Dp1: (take i p1) => [|x1 [|x2 p1']] //.
      By Rewrite: /scycle /q Dp1 /= /rlink Sface Hbgc in HUq.
    Rewrite: /ennx /= De2c; Apply/eqP=> [Dx1]; Case/idP: HnnxE.
    By Rewrite Dx1; Apply Hp1E; Rewrite: Dp1 /= setU11.
  Step HqN: (sub_set (diskN q) (diskN xp)).
    Move=> y Hy; Rewrite: /diskN in Hy; Case/hasP: Hy => [z Hz].
    Case/connectP=> [r Hr []] {y}; Move: Hr; Pose y := (finv node z).
    Step Hy: (andb (diskN xp y) (diskN q y)).
      Rewrite: ![r'](fclosed1 (diskN_node r') y) /y (f_finv (Inode gc)).
      Rewrite: !diskN_E /setU Hz /= andbT /q /= /setU1 (orbC x =d z).
      Apply/orP; Case Hpz: (p z); [By Left | Right].
      Move: Hz; Rewrite: /q /= /setU1; Case: (ennx =P z) => [[] | _].
        Clear; Rewrite: /ennx -(fclosed1 (diskE_edge Hpgc HUp)).
        Rewrite: /diskE /setD HnnxN andbT; Apply/orP.
        Move=> [Dnnx | Hpnnx]; RightBy Rewrite (HpE ? Hpnnx) in HnnxE.
        Move: (Hbgc (node x)).
        By Rewrite: {1 x}(eqP Dnnx) Dn3x cface1r Enode connect0.
      Pose p2 := (take i p); Rewrite: /= /p1 -cats1 take_cat -/p2.
      Rewrite: /i /p1 -cats1 find_cat.
      Case HpF: (has (cface ennx) p).
        Rewrite: -has_find HpF /p2 /=; Move=> Hp2z.
        By Rewrite: -(cat_take_drop i p) mem_cat /setU Hp2z in Hpz.
      Rewrite: ltnNge leq_addr subn_addr /= cface1 /ennx Enode /enx.
      Rewrite: Hbgc /= mem_cat /setU Hpz /= /setU1 orbF.
      Move=> Dz; Rewrite: -(eqP Dz) -(fclosed1 (diskE_edge Hpgc HUp)).
      Rewrite: /diskE /setD HnxN andbT /= /setU1 eqd_sym Hnxx /=.
      Apply/idP=> [Hnx]; Case/hasP: HpF.
      By Exists (node x); RightBy Rewrite: /ennx cface1 Enode connect0.
    Elim: {z Hz Hrec}r y Hy => [|z r Hrec] y Hy; [By Case (andP Hy) | Simpl].
    Rewrite: {1}/dlink; Case Hqy: (q y); LeftDone.
    Case/andP=> [Dz]; Apply: Hrec {r Hrec}.
    Rewrite: ![p'](fclosed1 (diskN_node p') z).
    Case/clinkP: Dz; Case{z}=> //; Rewrite: -(De2c y) Eedge.
    Case/andP: Hy => [Hxpy HqyN].
    Rewrite: !diskN_E /setU -(fclosed1 (diskE_edge Hpgc HUp)).
    Rewrite: -(fclosed1 (diskE_edge Hpgc HUq)) /diskE /setD Hqy Hxpy HqyN.
    Rewrite: /= orbT !andbT orbC /setU1; Apply/orP; Left.
    Case: (x =P y) => [Dx | _]; LeftBy Rewrite: Dx HqyN in Hqx.
    Rewrite: /q /= in Hqy; Case/norP: Hqy; Clear.
    Rewrite: /p1 -cats1 take_cat ~{Hi}.
    Case Hi: (ltn i (size p)); RightBy Rewrite: mem_cat /setU; Case (p y).
    Move=> Hy; Rewrite: -(cat_take_drop i p) mem_cat /setU ~{Hy}(negbE Hy) /=.
    Rewrite: (drop_sub x Hi); Apply/idP=> [Hy]; Case/idP: Hqx.
    Move: (mem_rot (1) xp) Hp Up; Rewrite: {1}/xp -(uniq_rot (1)) rot1_adds.
    Rewrite: {1 xp}lock /= -lock -(cat_take_drop (S i) p) -cats1 -catA.
    Case/splitPl: Hy => [r' r Er']; Rewrite: -catA cats1 uniq_cat catA.
    Rewrite: -{6 x}(last_add_last y r); Move: {r}(add_last r x) => r.
    Rewrite: has_cat path_cat last_cat.
    Move=> Erp; Move/andP=> [_ Hr]; Move/and3P=> [_ Ur _].
    Step HrF: (negb (has (fband (locked q)) r)).
      Apply/hasP=> [[z Hrz Hqz]]; Case/orP: Ur; Right.
      Apply/hasP; Exists z; LeftDone.
      Step Hpz: (fband (take (S i) p) z).
        Rewrite: (take_sub x Hi) -cats1 /fband has_cat /= orbF orbC Sface.
        Step Hi1: (ltn i (size p1)) By Rewrite: /p1 size_add_last leqW.
        Rewrite: /i -has_find in Hi1.
        Rewrite: /fband -lock /= Sface (same_cface (sub_find x Hi1)) in Hqz.
        By Rewrite: -/i /p1 sub_add_last -cats1 take_cat Hi in Hqz *.
      Case/hasP: Hpz => [z' Hz' Hzz']; Rewrite: (scycle_cface HUp Hzz') //.
        By Rewrite: -/xp -Erp mem_cat /setU Hrz orbT.
      By Rewrite: /= /setU1 -(cat_take_drop (S i) p) mem_cat /setU Hz' /= orbT.
    Rewrite: (take_sub x Hi) last_add_last ~{r' Erp Ur}Er' in Hr.
    Elim: {Hxpy Hqy}r y HqyN Hr HrF => [|z r Hrec] y Hy //=.
    Move/andP=> [Hyz Hr]; Move/norP=> [HzF HrF].
    Step Hz: (diskF q z); RightBy Case/andP: Hz; Auto.
    Rewrite: /rlink cface1 in Hyz; Rewrite: -lock in HzF.
    Rewrite: -(closed_connect (diskF_face q) Hyz) /diskF /setD.
    Rewrite: (closed_connect (fbandF q) Hyz) HzF.
    By Rewrite: (fclosed1 (diskN_node q)) Eedge.
  Rewrite: -HhcE in HnnxE.
  Case: {Hrec}(Hrec ? (negbI HnnxE) (take i p1)); Fold q; Auto.
    Rewrite ltnS in Hn; Apply: (leq_trans ? Hn).
    Rewrite: {1 card}lock (cardD1 x) -lock.
    Rewrite: {1 diskN}lock diskN_E /setU -lock /= setU11 /= add1n ltnS.
    Apply: subset_leq_card; Apply/subsetP=> [y Hy].
    Rewrite: /setD1 (HqN ? Hy) andbT; Apply/eqP=> [Dx].
    By Rewrite: Dx Hy in Hqx.
  By Move=> y Hy; Apply Hpac; Apply HqN.
Step HenxN: (diskN xp enx).
  Rewrite: diskN_E; Apply/orP; Right.
  Rewrite: /enx -(fclosed1 (diskE_edge Hpgc HUp)) /diskE /setD HnxN /= /setU1.
  Case Hpnx: (p (node x)); LeftBy Case/idP: HnxE; Auto.
  Rewrite: orbF andbT; Apply/eqP=> [Dnx].
  By Move: (Hbgc (node x)); Rewrite: cface1r Enode -Dnx connect0.
Rewrite: -{(node x)}De2c -/enx in HnxN.
Case: (Hhac ? ? (Hpac ? HnxN) (Hpac ? HxN)) => [q1 [Hq1 Eq1 Eq10] [Uq1 Hq1ac]].
Pose i := (find (fband p1) q1); Pose q2 := (take i q1).
Step Upq2: (negb (has (fband q2) p1)).
  Apply/hasP=> [[y Hy]]; Case/hasP=> [z Hz Hyz].
  Case (elimF (hasPx (cface z) p1)); RightBy Exists y; Rewrite: 1?Sface.
  Step Hq1z: (q1 z) By Rewrite: -(cat_take_drop i q1) -/q2 mem_cat /setU Hz.
  Rewrite: -/(fband p1 z) -(sub_index x Hq1z); Apply before_find.
  Rewrite: -(size_takel (find_size (fband p1) q1)) -/i -/q2.
  By Rewrite: -(cat_take_drop i q1) -/q2 index_cat Hz index_mem.
Step Hih: (has (fband p1) q1).
  Apply/hasP; Exists (last enx q1).
    By Case: {}q1 Eq10 => // [nx' q1'] _; Apply: mem_last.
  Apply/hasP; Exists enx; LeftBy Rewrite: /p1 mem_add_last /= setU11.
  By Rewrite: cface1r /enx Enode.
Step Hi: (ltn i (size q1)) By Rewrite: /i -has_find.
Pose y' := (sub x q1 i); Step Hy': (fband p1 y') By Apply: sub_find.
Rewrite: /fband in Hy'; Case/hasP: Hy' => [y Hy Hyy'].
Move: (simple_uniq Up1) Upq2 (last_add_last y p enx) {Up}; Rewrite: -/p1.
Case/splitPr Dp: p1 / Hy {Up} => [p2 p3] Up.
Rewrite: last_cat /= has_cat; Move/norP=> [Up2q Up3q] Ep3.
Pose q3 := (cat q2 (belast y p3)); Pose q := (Adds enx q3).
Step HUq: (scycle rlink q).
  Apply/andP; Split.
    Rewrite: /= /q3 -cats1 -catA cats1 path_cat -{3 enx}Ep3 -lastI /=.
    Rewrite: -(cat_take_drop i q1) -/q2 (drop_sub x Hi) -/y' path_cat in Hq1.
    Rewrite: /= andbA {2}/rlink Sface (same_cface Hyy') Sface in Hq1.
    Case/andP: Hq1 => [H _]; Rewrite: {2}/rlink andbA ~H /=.
    By Rewrite: Dp path_cat in Hp1; Case/and3P: Hp1.
  Rewrite: -(simple_rot (1)) /q rot1_adds -cats1 /q3 -catA.
  Rewrite: -Ep3 cats1 -lastI simple_cat; Apply/and3P; Split; Auto.
    By Rewrite: -(cat_take_drop i q1) simple_cat in Uq1; Case/andP: Uq1.
  By Rewrite: Dp simple_cat in Up1; Case/and3P: Up1.
Step Hp3p: (sub_set (belast y p3) p).
  Move=> z Hz; Rewrite: -{1 p}/(behead (Adds x p)).
  Rewrite: -(belast_add_last x p enx) -/p1 Dp belast_cat /= -cat_add_last.
  By Rewrite: -lastI /= mem_cat /setU Hz orbT. 
Step Hq3E: (sub_set q3 hc).
  Move=> z; Rewrite: /q3 mem_cat; Case/orP=> [Hz]; Auto.
  By Case: (andP (allP Hq1ac z (mem_take Hz))).
Step Hqx: (diskN q x) = false.
  Rewrite: (fclosed1 (diskN_node q)) -{(node x)}De2c.
  Apply: (diskN_edge_ring Hgc' HUq ? (setU11 ? ?)).
  Case/andP: HUq (Hq3E (node x)); Rewrite: /q.
  Case: {}q3 => [|y1 [|y2 q4]] //; LeftBy Rewrite: /= /rlink Sface Hbgc.
  Do 2 Clear; Rewrite: /= /setU1 orbF /enx De2c eqd_sym.
  Move=> *; Apply/idP=> [Dy1]; Case/idP: HnxE; Auto.
Step HqN: (sub_set (diskN q) (diskN xp)).
  Move{Hrec}=> z0; Rewrite: {1}/diskN; Case/hasP=> [z2 Hz2].
  Case/connectP=> [r Hr []] {z0}; Move: Hr; Pose z1 := (finv node z2).
  Step Hz1: (andb (diskN xp z1) (diskN q z1)).
    Rewrite: ![r'](fclosed1 (diskN_node r') z1) /z1 (f_finv (Inode gc)).
    Rewrite: andbC diskN_E /setU Hz2; Rewrite: /q /q3 -cat_adds mem_cat in Hz2.
    Case/orP: Hz2 => [Hz2];
      RightBy Rewrite: diskN_E {1}/xp /setU /= /setU1 (Hp3p ? Hz2) orbT.
    Step Uq2p: (negb (has (fband xp) q2)).
      Apply/hasP=> [[t Ht]]; Rewrite: /fband; Move/hasP=> [t' Ht' Htt'].
      Case: (elimN (hasPx (fband q2) p1)).
        By Rewrite: Dp has_cat; Apply/norP; Split.
      Rewrite: /xp /= in Ht'; Case/setU1P: Ht' => [Dt' | Ht'].
        Exists enx; LeftBy Rewrite: /p1 mem_add_last /= setU11.
        Apply/hasP; Exists t; LeftDone.
        By Rewrite: cface1 /enx Enode Dt' Sface.
      Exists t'; LeftBy Rewrite: /p1 mem_add_last /= setU1r.
      By Apply/hasP; Exists t; RightBy Rewrite Sface.
    Case/andP: HUq Uq2p; Rewrite: /= -cats1 /q3 -catA.
    Case/splitPl: Hz2 => [q' q'' []]; Rewrite: -catA path_cat has_cat.
    Move/andP=> [Hq' _] _; Move/norP=> [Uq'p _] {q''}.
    Elim: q' {}enx Hq' HenxN Uq'p => [|t2 q' Hrec] t1 //=.
    Move/andP=> [Dt2 Hq'] Ht1; Move/norP=>  [Ut2p Uq'p].
    Step Ht2: (diskF xp t2); RightBy Case/andP: Ht2; Auto.
    Rewrite: /rlink cface1 in Dt2.
    Rewrite: -(closed_connect (diskF_face xp) Dt2) /diskF /setD.
    Rewrite: (closed_connect (fbandF xp) Dt2). 
    By Rewrite: (fclosed1 (diskN_node xp)) Eedge Ht1 andbT.
  Elim: r z1 Hz1 {z2 Hz2 Hrec} => [|z2 r Hrec] z1 Hz1; LeftBy Case/andP: Hz1.
  Rewrite: /= {1}/dlink; Case Hqz1: (q z1); LeftDone.
  Case/andP=> [Dz1]; Apply: Hrec {r Hrec}.
  Rewrite: ![p'](fclosed1 (diskN_node p') z2).
  Case/clinkP: Dz1 => [[]] //; Rewrite: -{z2}(De2c z1) Eedge.
  Case/andP: Hz1 => [Hxpz1 Hqz1N].
  Rewrite: !diskN_E /setU -(fclosed1 (diskE_edge Hpgc HUp)).
  Rewrite: -(fclosed1 (diskE_edge Hpgc HUq)) /diskE /setD Hqz1 Hxpz1 Hqz1N.
  Rewrite: -(belast_add_last x p enx) -/p1 Dp belast_cat /= orbT !andbT.
  Apply/orP; Right; Rewrite: -cat_add_last -lastI mem_cat /setU.
  Apply/norP; Split;
    RightBy Rewrite: /q /q3 -cat_adds mem_cat in Hqz1; Case/norP: Hqz1.
  Step Uqp2: (negb (has (fband q) p2)).
    Apply/hasP=> [[t Ht]]; Rewrite: /fband; Move/hasP=> [t' Ht' Htt'].
    Rewrite: -(mem_rot (1)) /q rot1_adds in Ht'.
    Rewrite: -cats1 /q3 -catA cats1 -Ep3 -lastI mem_cat in Ht'.
    Case/orP: Ht' => [Ht'].
      By Case/hasP: Up2q; Exists t; RightBy Apply/hasP; Exists t'.
    Rewrite: Dp simple_cat in Up1; Case/and3P: Up1; Clear; Case/hasP.
    By Exists t'; RightBy Apply/hasP; Exists t; Rewrite: 1?Sface.
  Apply/idP=> [Hz1]; Case/idP: Hqx {Hqx Hqz1}.
  Def: Hp2 := Hp1; Rewrite: Dp path_cat in Hp2; Case/andP: Hp2 => [Hp2 _].
  Case/splitPl: Hz1 Hp2 Uqp2 Hqz1N => [p2' p2'' []] {z1 Hxpz1}.
  Rewrite: path_cat has_cat; Move/andP=> [Hp2' _]; Move/norP=> [Up2' _] {p2''}.
  Elim/last_ind: p2' Hp2' Up2' => [|r z Hrec] //.
  Rewrite: last_add_last -cats1 has_cat path_cat {2}/rlink /= orbF cface1.
  Move/and3P=> [Hr Dz _]; Move/norP=> [Ur Uz] Hz.
  Step HzF: (diskF q z) By Apply/andP; Split.
  Rewrite: -(closed_connect (diskF_face q) Dz) in HzF; Case/andP: HzF; Clear.
  Rewrite: (fclosed1 (diskN_node q)) Eedge; Auto.
Rewrite: -HhcE in HnxE.
Case: {Hrec}(Hrec ? (negbI HnxE) q3); Rewrite: -/enx -/q; Auto.
  Rewrite ltnS in Hn; Apply: leq_trans Hn.
  Rewrite: {1 card}lock (cardD1 x) -lock.
  Rewrite: {1 diskN}lock diskN_E /setU -lock /= setU11 /= add1n ltnS.
  Apply subset_leq_card; Apply/subsetP=> [z Hz].
  By Rewrite: /setD1 (HqN ? Hz) andbT; Apply/eqP=> [Dx]; Rewrite: Dx Hz in Hqx.
By Move=> z Hz; Apply Hpac; Apply HqN.
Qed.

Remark cface_ac_h : (x, y : gc) (ac x) -> (cface x y) -> (cface (h x) (h y)).
Proof.
Move=> x y Hx; Case/connectP=> [p Hp []] {y}.
Elim: p x Hx Hp => [|y p Hrec] x Hx; LeftBy Rewrite: /= connect0.
Rewrite: cface1 -(HhF Hx) /=; Move/andP=> [Dy Hp].
Move: Hx Hp; Rewrite: (fclosed1 HacF) (eqP Dy); Exact (Hrec y).
Qed.

Remark cface_h_ac : (x : gc; u : gm) (ac x) -> (cface (h x) u) ->
  (EX y | (cface x y) & (h y) = u).
Proof.
Move=> x u Hx; Case/connectP=> [p Hp []] {u}.
Elim: p x Hx Hp => [|u p Hrec] x Hx; LeftBy Exists x; LeftBy Apply connect0.
Simpl; Case/andP; Rewrite: {1}/eqdf -(HhF Hx); Case/eqP {u}; Move=> Hp. 
Rewrite: (fclosed1 HacF) in Hx; Case: (Hrec ? Hx Hp) => [y Hxy []].
By Exists y; LeftBy Rewrite: cface1.
Qed.

Local HhFn := (preembedding_arity Hh).

Remark cface_inj_embed :
  (x, y : gc) (ac x) -> (cface x y) -> (h x) = (h y) -> x = y.
Proof.
Move=> x y Hx Hxy Ehxy.
Step Ehn: (n : nat) (h (iter n face x)) = (iter n face (h x)).
  Elim=> [|n Hrec] //=; Rewrite: HhF ?Hrec // /kernel /setC.
  By Rewrite: -(closed_connect (fbandF rc) (fconnect_iter face n x)).
Step Efxy: (findex face (h x) (h y)) = (findex face x y).
  By Rewrite: -{1 y}(iter_findex Hxy) Ehn findex_iter // HhFn // findex_max.
By Rewrite: -(iter_findex Hxy) -Efxy Ehxy findex0.
Qed.

Definition pre_hom_ring [x : gc; p : (seq gc)] : Prop :=
   (and3 (path rlink x p)
         (sub_set (Adds x p) ac)
         (scycle rlink (maps h (Adds x p)))).

Lemma intro_pre_hom_ring : (x : gc; p : (seq gc))
    (path rlink x p) ->
    (rlink (h (last x p)) (h x)) ->
    (sub_set (Adds x p) ac) ->
    (simple (maps h (Adds x p))) ->
  (pre_hom_ring x p).
Proof.
Move=> x p Hp Ehp Hpac Uhp; Split; Auto.
Rewrite: /scycle ~Uhp andbT (cycle_path (h x)) last_maps /= ~Ehp /=.
Move/(introT subsetP): Hpac; Rewrite: /subset {1}/setC disjoint_has.
Elim: p x Hp => [|y p Hrec] x //; Rewrite: /= negb_orb negb_elim.
Move/andP=> [Hxy Hp]; Move/andP=> [Hx Hpac]; Move/norP: {}Hpac => [Hex _].
Rewrite: negb_elim -(closed_connect HacF Hxy) in Hex.
Rewrite: {1}/rlink -(embed_functor Hx Hex) (cface_ac_h Hex Hxy) /=; Auto.
Qed.

Lemma trivial_hom_ring : (x : gc; p : (seq gc))
  (pre_hom_ring x p) ->
  (leq (fcard face (diskF (maps h (Adds x p)))) (0)) ->
  (rlink (last x p) x).
Proof.
Move=> x p Hxp; Case: (pickP (diskF (maps h (Adds x p)))) => [y Hy | HpF].
  Rewrite: /n_comp (cardD1 (froot face y)) /setI.
  Rewrite: -[q](closed_connect (diskF_face q) (connect_root ? y)).
  By Rewrite: (roots_root (Sface gm)) Hy.
Clear; Elim: {p}(S (size p)) x {-2}p (ltnSn (size p)) HpF Hxp => // [n Hrec].
Move=> x p Hn HpF; Case; Pose xp := (Adds x p); Move=> Hp Hpac HUhp.
Rewrite ltnS in Hn; Pose y := (last x p); Step Hxpy: (xp y) By Apply: mem_last.
Step Hhxpy : (maps h xp (h y)) By Apply maps_f.
Step Hy: (ac y) By Apply Hpac. 
Step Hnhy: (fband (maps h xp) (node (h y))).
  Apply negbEf; Move: (HpF (node (h y))).
  Rewrite: /diskF /setD -(fclosed1 (diskN_node (maps h xp))) diskN_E /setU.
  By Rewrite: Hhxpy /= andbT.
Rewrite: /fband in Hnhy; Case/hasP: {}Hnhy => [u]; Move/mapsP=> [z Hz []] {u}.
Rewrite Sface; Move=> Hhzny.
Case/splitPl Dp: p / {}Hz => [p1 p2 Ep1].
Case/lastP: p2 Dp => [|p2 y'] Dp.
  Rewrite: cats0 in Dp; Rewrite: -Dp -/y in Ep1.
  By Rewrite: Ep1 -{1 (h z)}Enode -cface1 Sface Hbgm in Hhzny.
Step Dy': y' = y By Rewrite: /y Dp last_cat last_add_last.
Case/lastP: p1 Ep1 Dp => [|p1 z'] Ep1 Dp.
  Simpl in Ep1; Case/andP: HUhp; Rewrite: (cycle_path (h x)) /=.
  Rewrite: last_maps -/y Ep1 (rlinkFr Hhzny) -{1 (node (h y))}Enode.
  By Rewrite: /rlink -cface1r cface1 -{1 (h y)}Dn3m Enode Hbgm.
Rewrite: last_add_last in Ep1; Rewrite: ~{z'}Ep1 ~{y'}Dy' in Dp.
Pose eny := (edge (node y)).
Step Heny : (ac eny) By Rewrite: (fclosed1 HacF) /eny Enode.
Step Dheny : (h eny) = (edge (node (h y))).
  By Rewrite: -{1 y}Enode -/eny (HhF Heny) Eface.
Step Henyz: (rlink eny z).
  Case Hhpny: (maps h xp (node (h y))).
    Case/mapsP: Hhpny => [t Ht Dht].
    Case/splitPl Dp': p / {}Ht => [p1' p2' Ep1'].
    Step Dp2': p2' = (seq1 y).
      Case: p2' Dp' => [|t1 [|t2 p2']] Dp'.
          Rewrite cats0 in Dp'; Rewrite: -Dp' -/y in Ep1'.
          Move: (Hbgm (node (h y))); Rewrite: cface1r Enode.
          By Rewrite: -Dht Ep1' connect0.
        By Rewrite: /y Dp' last_cat /=.
      Case/andP: HUhp; Rewrite: /xp Dp' (cycle_path (h x)) -cat_adds.
      Rewrite: !maps_cat path_cat simple_cat.
      Move/and3P=> [_ Htt1 _]; Move/and3P=> [_ _ Ut1].
      Rewrite: maps_adds simple_adds in Ut1; Move/andP: Ut1 => [Ut1 _].
      Rewrite: /fband in Ut1; Case/hasP: Ut1; Exists (h y).
        By Apply maps_f; Rewrite: /y Dp' last_cat /= mem_lastU.
      By Rewrite: /= last_maps Ep1' /rlink Dht cface1 Enode Sface in Htt1 *.
    Step Dt: t = (node y).
      Rewrite: Dp' path_cat Ep1' Dp2' in Hp; Case/and3P: Hp => [_ Hty _].
      Def: Het := Hy; Rewrite: -(closed_connect HacF Hty) in Het.
      Rewrite: /rlink -{1 y}Enode -cface1r -/eny in Hty.
      Apply: (Iedge ? (cface_inj_embed Het Hty ?)).
      By Rewrite: (embed_functor (Hpac ? Ht) Het) Dht Dheny.
    Case: p2 Dp (congr [q](last x (belast x q)) Dp) => [|z1 p2] Dp.
      Rewrite: Dp' Dp2' !belast_cat !last_cat /= last_add_last Ep1'.
      By Case; Rewrite: /rlink /eny De2c Dt connect0.
    Rewrite: Dp' Dp2' -cats1 !belast_cat !last_cat /= belast_add_last Ep1' /=.
    Move=> Ep2; Rewrite: lastI -Ep2 cat_add_last in Dp; Case/andP: HUhp; Clear.
    Rewrite: /xp Dp -cat_adds maps_cat !maps_adds simple_cat !simple_adds /fband.
    Case/and4P; Do 2 Clear; Case/hasP; Exists (h t); RightBy Rewrite: Dht.
    By Apply maps_f; Do 2 Rewrite: mem_add_last /= /setU1; Rewrite: set11 orbT.
  Pose q := (add_last p2 eny).
  Step HhenyF: (cface (h eny) (h y)) By Rewrite: cface1 Dheny Enode connect0.
  Step Hzq: (pre_hom_ring z q).
    Apply intro_pre_hom_ring.
          Rewrite: Dp path_cat last_add_last in Hp; Case/andP: Hp; Clear.
          By Rewrite: /q -!cats1 !path_cat /= {4}/rlink cface1r /eny Enode.
        Rewrite: /rlink /q last_add_last Sface (same_cface Hhzny).
        By Rewrite: -[u](Eedge gm (edge u)) De2m Dheny Enode connect0.
      Move=> t Ht; Rewrite: /q -cats1 -cat_adds cats1 mem_add_last in Ht.
      Rewrite mem_adds in Ht; Case/setU1P: Ht => [[] | Ht] //.
      Apply Hpac; Rewrite: /xp /= setU1r // Dp cat_add_last mem_cat /setU.
      By Rewrite: -cats1 -cat_adds mem_cat /setU Ht /= orbT.
    Rewrite: ~/q -add_last_adds maps_add_last simple_add_last.
    Rewrite: [q](closed_connect (fbandF q) HhenyF) -simple_add_last.
    Case/andP: HUhp; Clear; Rewrite: /xp Dp cat_add_last -cat_adds -add_last_adds.
    By Rewrite: maps_cat -maps_add_last simple_cat; Case/and3P.
  Rewrite: -(last_add_last z p2 eny) -/q; Apply Hrec; Auto.
    Apply: leq_trans Hn; Rewrite: /q Dp size_cat !size_add_last.
    By Rewrite: addSnnS leq_addl.
  Step Hxpeny: (fband (maps h xp) (h eny)) By Apply/hasP; Exists (h y).
  Step Eqr: (chord_ring (maps h xp) (h eny)) = (maps h (rotr (1) (Adds z q))).
    Rewrite: /q -add_last_adds rotr1_add_last maps_adds; Congr Adds.
    Step [ ]: (h y) = (fproj (maps h xp) (h eny)).
      Case: (fprojP Hxpeny) => [Hpr Hypr]; Rewrite: (same_cface HhenyF) in Hypr.
      By Apply (scycle_cface HUhp).
    Rewrite: Dheny De2m.
    Step [ ]: (h z) = (fproj (maps h xp) (node (h y))).
      Case: (fprojP Hnhy) => [Hpr Hzpr]; Rewrite: -(same_cface Hhzny) in Hzpr.
      By Apply (scycle_cface HUhp); Try By Apply maps_f.
    Case/andP: HUhp; Clear; Move/simple_uniq.
    Rewrite: -(rot_rotr (1) xp) maps_rot uniq_rot; Move=> Up.
    Rewrite: arc_rot //; RightBy Apply maps_f; Rewrite: mem_rotr.
    Move: Up; Rewrite: /xp Dp -cat_adds -add_last_cat rotr1_add_last.
    Rewrite: -add_last_adds cat_add_last maps_adds maps_cat !maps_adds.
    Apply: (!right_arc).
  Move=> u; Rewrite: -{(Adds z q)}(rot_rotr (1)) maps_rot diskF_rot -Eqr.
  Rewrite: diskF_chord_ring // /setD ?HpF ?andbF //.
      By Rewrite: /xp Dp; Case: {}p1 => [|x1 [|x2 p1']]; Case p2.
    Rewrite: Dheny -(fclosed1 (diskE_edge Hpgm HUhp)) /diskE /setD Hhpny.
    By Rewrite: -(fclosed1 (diskN_node (maps h xp))) diskN_E /setU Hhxpy.
  By Rewrite: Dheny De2m.
Step Hny: (ac (node y)).
  By Rewrite: -{(node y)}De2c -/eny (closed_connect HacF Henyz) Hpac.
Step Dhny : (h (node y)) = (node (h y)).
  By Apply Iedge; Rewrite: -Dheny -embed_functor.
Pose enny := (edge (node (node y))).
Step Henny : (ac enny) By Rewrite: (fclosed1 HacF) /enny Enode.
Step Dhenny : (h enny) = (edge (node (node (h y)))).
  By Rewrite: -Dhny -{(node y)}Enode -/enny (HhF Henny) Eface.
Step Hhyx: (rlink (h y) (h x)).
  Case: (andP HUhp); Rewrite: /xp (cycle_path (h x)) /= last_maps -/y.
  By Case/andP.
Step Hennyx: (rlink enny x).
  Case Hhpnny: (maps h xp (node (node (h y)))).
    Case/mapsP: Hhpnny => [t Ht Dht].
    Case/splitPl Dp': p / Ht => [p1' p2' Ep1'].
    Step Dp1': p1' = seq0.
      Case: p1' Dp' Ep1' => [|t1 p1'] Dp' Ep1' //.
      Simpl in Ep1'; Case/andP: HUhp; Clear.
      Rewrite: /rlink -{(h y)}Dn3m cface1 Enode -Dht in Hhyx.
      Rewrite: /xp maps_adds simple_adds {1 p}Dp' lastI Ep1' cat_add_last.
      By Rewrite: maps_cat fband_cat /= Sface Hhyx !orbT.
    Rewrite: -Ep1' Dp1' ~{t Ht p1' p2' Ep1' Dp' Dp1'}/= in Dht.
    Step Dp1 : p1 = seq0.
      Case: p1 Dp => [|x1 p1] Dp //.
      Case/andP: HUhp; Rewrite: /xp Dp /=; Move/andP=> [Hxx1 _].
      Rewrite: /rlink Dht cface1 Enode -(same_cface Hhzny) Sface in Hxx1.
      Rewrite: cat_add_last !simple_adds maps_cat /= !fband_cat /= Hxx1 orbT.
      By Rewrite: andbF.
    Rewrite: ~{p1}Dp1 /= in Dp. 
    Step Dx: x = (node (node y)).
      Rewrite: Dp /= in Hp; Move/andP: Hp => [Hxz _].
      Step Hex: (ac (edge x)) By Rewrite: (closed_connect HacF Hxz); Apply Hpac.
      Rewrite: /rlink /eny De2c -{(node y)}Enode -/enny -cface1 in Henyz.
      Rewrite: Sface -(same_cface Hxz) in Henyz.
      Apply: (Iedge ? (cface_inj_embed Hex Henyz ?)).
      By Rewrite: (embed_functor (Hpac ? (setU11 ? ?)) Hex) Dht Dhenny.
    By Rewrite: /rlink /enny -Dx De2c connect0.
  Pose q := (add_last p1 enny).
  Step HhennyF: (cface (h enny) (h z)) By Rewrite: cface1 Dhenny Enode Sface.
  Step Hxq: (pre_hom_ring x q).
    Apply intro_pre_hom_ring.
          Rewrite: Dp path_cat in Hp; Case/andP: Hp => [H _]; Move: H.
          Rewrite: /q -!cats1 !path_cat /= {2 4}/rlink Sface -(same_cface Henyz).
          By Rewrite: /eny De2c -{(node y)}Enode -cface1 Sface.
        Rewrite: /rlink /q last_add_last Dhenny De2m.
        By Rewrite: -{(h y)}Eedge Dn3m -cface1.
      Move=> t Ht; Rewrite: /q -cats1 -cat_adds cats1 mem_add_last in Ht.
      Rewrite mem_adds in Ht; Case/setU1P: Ht => [[] | Ht] //.
      By Apply Hpac; Rewrite: /xp Dp cat_add_last -cat_adds mem_cat /setU Ht.
    Rewrite: ~/q -add_last_adds maps_add_last simple_add_last.
    Rewrite: [q](closed_connect (fbandF q) HhennyF) -simple_add_last.
    Case/andP: HUhp; Clear; Rewrite: -maps_add_last /xp Dp -cat_adds maps_cat.
    By Rewrite: simple_cat; Case/and3P.
  Rewrite: -(last_add_last x p1 enny) -/q; Apply Hrec; Auto.
    Apply: leq_trans Hn; Rewrite: /q Dp size_cat !size_add_last.
    By Rewrite: -addSnnS leq_addr.
  Step Hphz: (maps h xp (h z)) By Apply maps_f.
  Step Hxpenny: (fband (maps h xp) (h enny)) By Apply/hasP; Exists (h z).
  Rewrite: /rlink -{(h y)}Dn3m cface1 Enode in Hhyx. 
  Step Hnny: (fband (maps h xp) (node (node (h y)))).
    By Apply/hasP; Exists (h x); LeftBy Apply: setU11.
  Step Eqr: (chord_ring (maps h xp) (h enny)) = (maps h (rotr (1) (Adds x q))).
    Rewrite: /q -add_last_adds rotr1_add_last maps_adds; Congr Adds.
    Step [ ]: (h z) = (fproj (maps h xp) (h enny)).
      Case: (fprojP Hxpenny) => [Hpr Hypr].
      Rewrite: (same_cface HhennyF) in Hypr.
      By Apply (scycle_cface HUhp).
    Step [ ]: (h x) = (fproj (maps h xp) (edge (h enny))).
      Case: (fprojP Hnny) => [Hpr Hzpr]; Rewrite: (same_cface Hhyx) in Hzpr.
      By Rewrite: Dhenny De2m; Apply (scycle_cface HUhp); Rewrite: //= setU11.
    Case/andP: HUhp; Clear; Move/simple_uniq.
    Rewrite: /xp Dp cat_add_last maps_adds maps_cat !maps_adds.
    Apply: (!left_arc).
  Move=> u; Rewrite: -{(Adds x q)}(rot_rotr (1)) maps_rot diskF_rot -Eqr.
  Rewrite: diskF_chord_ring // /setD ?HpF ?andbF //.
      By Rewrite: /xp Dp; Case: {}p1 => [|x1 [|x2 p1']]; Case p2.
    Rewrite: Dhenny -(fclosed1 (diskE_edge Hpgm HUhp)) /diskE /setD Hhpnny.
    By Rewrite: -!(fclosed1 (diskN_node (maps h xp))) diskN_E /setU Hhxpy.
  By Rewrite: Dhenny De2m.
Rewrite: /rlink -{(edge enny)}Enode -cface1 /enny De2c Dn3c // in Hennyx.
Exact (Hacbc Hy).
Qed.

Remark HrcN: (fclosed node rc).
Proof.
Apply: (intro_closed (Snode ?)) => [x nx Dnx Hx].
By Rewrite: -(fconnect_cycle Hrc Hx) connect1.
Qed.

Lemma edge_perimeter : (x : gc) (orb (bc x) (bc (edge x))).
Proof.
Move=> x; Rewrite: /setC -negb_andb; Apply/andP=> [[Hx Hex]].
Step Dfx: (face x) = x.
  Apply (scycle_cface HUrc); Auto; LeftBy Rewrite: Sface fconnect1.
  By Rewrite: (fclosed1 HrcN) -{1 x}De2c Eedge.
Step HxF1: (fcycle face (seq1 x)) By Rewrite: /= /eqdf Dfx set11.
Move: (allP (embeddable_ring Hgc) ? Hx) => HxF3; Rewrite: /good_ring_arity in HxF3.
By Rewrite: (order_cycle HxF1) // in HxF3; Rewrite: /= setU11.
Qed.

Syntactic Definition erc := (maps edge rc).

Remark Drrrc: (rev_ring rrc) = erc.
Proof. By Rewrite: /rev_ring /rrc maps_rev rev_rev. Qed.

Remark HUrrc: (scycle rlink rrc).
Proof.
Rewrite: /rrc /scycle simple_rev UrcF andbT.
Case: {}rc Hrc => [|x p]; Rewrite: //= (cycle_path x) rev_adds.
Rewrite: last_add_last; Elim: p {1 4}x => [|z p Hrec] y; Rewrite: /= ?andbT.
  By Case/eqP; Rewrite: /rlink cface1 Enode connect0.
Move/andP=> [Dz Hp]; Rewrite: -cats1 rev_adds path_cat last_add_last /=.
By Rewrite: (Hrec ? Hp) -(eqP Dz) /rlink cface1 Enode connect0.
Qed.

Remark HUerc : (scycle rlink erc).
Proof. Rewrite: -Drrrc; Exact (scycle_rev_ring Hgc' HUrrc). Qed.

Hints Resolve HUrrc HUerc.

Lemma chordless_perimeter : (x : gc)
  (bc x) -> (bc (edge x)) -> (orb (ac x) (ac (edge x))).
Proof.
Step EercF: (fband erc) =1 (fband rc).
  Move=> x; Rewrite: -Drrrc (fband_rev_ring Hgc' HUrrc).
  By Apply: eq_has_r => [y]; Rewrite: /rrc mem_rev.
Case: (andP HUerc) => [Herc]; Move/simple_uniq=> Uerc x Hix Hiex.
Rewrite: /kernel /setC -negb_andb; Apply/andP=> [[Hx Hex]].
Step Perc : (proper_ring erc).
  Move: Hx Herc (edge_perimeter (head x rc)).
  Case: (rc) => [|x1 [|x2 [|x3 p]]] //=.
    By Clear; Rewrite: /rlink Sface Hbgc.
  Do 2 Clear; Rewrite: /setC /= /setU1 set11 /= orbF (inj_eqd (Iedge gc)).
  By Rewrite (eqd_sym x2); Case/norP.
Move: x Hix Hiex Hx Hex; Step Prrc: (proper_ring rrc).
  By Rewrite: -(proper_rev_ring Hgc') Drrrc.
Step HeiF0: (x : gc)
     (fband erc x) -> (fband erc (edge x)) -> (diskE erc x) ->
     (EX y | (diskF (chord_ring erc x) y)).
  Move=> x Hx Hex HxE; Pose rx := (chord_ring erc x).
  Step HUrx : (scycle rlink rx) By Apply: scycle_chord_ring.
  Step Prx: (proper_ring rx) By Rewrite: /rx proper_chord_ring.
  Step Hirx: (sub_set (behead rx) erc).
    Case: (fprojP Hx) (fprojP Hex) => [Hx' Hxx'] [Hex' Hexex'].
    Case: (cat_arc Uerc Hex' Hx').
      Apply/eqP=> [Dex'].
      By Rewrite: Sface Dex' -(same_cface Hxx') Hbgc in Hexex'.
    Move=> i Derc y Hy; Rewrite: -(mem_rot i) -Derc mem_cat /setU.
    By Apply/orP; Left.
  Step HirxN: (sub_set (diskN rx) bc).
    Move=> y Hy; Rewrite: /rx diskN_chord_ring // in Hy.
    Case/andP: Hy; Clear; Rewrite: -Drrrc diskN_rev_ring //.
    By Rewrite: {1}/setC diskN_E /setU /rrc mem_rev; Case/norP.
  Move: (leqnn (size rx)) HUrx Prx Hirx HirxN {Hx Hex HxE}.
  Elim: {x rx}(size rx) {-2}rx => [|n Hrec] p; LeftBy Case p.
  Move=> Hn HUp Pp Hip HipN; Apply: set0Pn; Apply/set0P=> [HpF0].
  Case/andP: {}HUp => [Hp]; Move/simple_uniq=> Up.
  Case Dp: p {}Pp => [|x p'] // _.
  Step Hpx: (p x) By Rewrite: Dp /= setU11.
  Step HpxN: (diskN p x) By Rewrite: diskN_E /setU Hpx.
  Step Hix: (bc x) By Apply HipN.
  Def: HpF := (fbandF p); Def: HpN := (diskN_node p).
  Pose efex := (edge (face (edge x))); Def: HpE := (diskE_edge Hpgc HUp).
  Step Eefex: (face efex) = (node x) By Rewrite: /efex -{1 x}(Dn3c Hix) !Enode.
  Case HefexE: (diskE p efex).
    Step Hefex: (fband p efex).
      Apply negbEf; Rewrite: (fclosed1 HpF) Eefex; Move: (HpF0 (node x)).
      By Rewrite: /diskF /setD andbC -(fclosed1 HpN) HpxN.
    Step Heefex: (fband p (edge efex)).
      Apply/hasP; Exists (next p x); LeftBy Rewrite mem_next.
      Rewrite: /efex De2c -cface1; Exact (next_cycle Hp Hpx).
    Pose y := (fproj p efex); Step Hp'y: (p' y).
      Case: (fprojP Hefex); Rewrite: -/y Dp /=; Case/setU1P=> // [[]].
      By Rewrite: -{1 x}Enode -cface1r cface1 Eefex Hbgc.
    Case/splitPr Dp': p' / Hp'y => [p1 p2].
    Step Dp1: (Adds efex p1) = (chord_ring p efex).
      Congr Adds; Rewrite: -/y /efex De2c /arc.
      Pose z := (fproj p (face (edge x))).
      Step [ ]: (1) = (index z p).
        Case: (fprojP Heefex); Rewrite: /efex De2c -/z; Move=> Hpz Hzex.
        Rewrite: -cface1 Sface in Hzex; Rewrite: Dp /=.
        Case: (z =P x) => [Dz | _]; LeftBy Rewrite: Dz Hbgc in Hzex.
        Move: Hp; Rewrite Dp; Case: (p') Dp => [|z' p''] //= Dp.
        Case/andP=> [Hzz' _].
        Case: (z =P z') => [_|[]] //; Apply: (scycle_cface HUp ? Hpz).
          By Rewrite: (same_cface Hzex).
        By Rewrite: Dp /= setU1r ?setU11.
      Rewrite: Dp rot1_adds -cats1 Dp' -catA index_cat.
      Rewrite: Dp /= Dp' uniq_cat andbA /= in Up.
      Case/and3P: Up; Clear; Case/norP => [Hp1y _] _.
      By Rewrite: (negbE Hp1y) /= set11 addn0 take_cat ltnn subnn take0 cats0.
    Case: {Hrec}(Hrec (Adds efex p1)).
              Rewrite: -ltnS /=; Apply: leq_trans Hn.
              By Rewrite: Dp Dp' /= size_cat /= addnS !ltnS leq_addr.
            By Rewrite Dp1; Apply scycle_chord_ring.
          By Rewrite Dp1; Apply proper_chord_ring.
        By Move=> /= z Hz; Apply Hip; Rewrite: Dp Dp' /= mem_cat /setU Hz.
      Move=> z; Rewrite: Dp1 diskN_chord_ring //.
      By Move=> H; Apply HipN; Case/andP: H.
    By Move=> z; Rewrite: Dp1 diskF_chord_ring // /setD HpF0 andbF.
  Rewrite: /efex -(fclosed1 HpE) /diskE /setD (fclosed1 HpN) Eedge in HefexE.
  Rewrite: HpxN andbT in HefexE; Move/idP: HefexE => Hpfex.
  Case: p' Dp => [|fex p'] Dp; LeftBy Rewrite Dp in Pp.
  Step Hpfex': (p fex) By Rewrite: Dp /= setU1r ?setU11.
  Step Dfex: fex = (face (edge x)).
    Apply: (scycle_cface HUp ? Hpfex' Hpfex).
    By Rewrite: Dp /scycle /= /rlink cface1 Sface -andbA in HUp; Case/andP: HUp.
  Pose enx := (edge (node x)); Step Henx: (fband p enx).
    Rewrite: (fclosed1 HpF) /enx Enode; Exact (subsetP (ring_fband ?) ? Hpx).
  Step Heenx: (fband p (edge enx)).
    Apply/hasP; Exists (next p fex); LeftBy Rewrite: mem_next.
    Rewrite: /enx De2c -Eefex /efex -cface1 Dfex; Exact (next_cycle Hp Hpfex).
  Step HenxE: (diskE p enx).
    Rewrite: /enx -(fclosed1 HpE) /diskE /setD -(fclosed1 HpN) HpxN andbT.
    Rewrite: Dp /=; Apply/setU1P=> [[Dnx | Hnx]].
      Move: (Hbgc (node x)).
      By Rewrite: cface1r Enode -Dnx connect0.
    Rewrite: Dp in Hip; Move: {Hnx Hip}(Hip ? Hnx) (Hip ? (setU11 ? ?)).
    Rewrite: -{(node x)}Eface -{(fex)}De2c Dfex -/efex !(mem_maps (Iedge gc)).
    Rewrite: -(fclosed1 HrcN); Move=> Hfnx Hefex; Pose q := (seq2 efex (node x)).
    Step Hq: (fcycle face q).
      Rewrite: /q /= /eqdf andbT Eefex set11 /=.
      Apply: (introT eqP (scycle_cface HUrc ? Hfnx Hefex)).
      By Rewrite: -Eefex -!cface1 connect0.
    Move: (allP (embeddable_ring Hgc) ? Hefex) (card_size q).
    Rewrite: /good_ring_arity /order.
    By Rewrite: (eq_card (fconnect_cycle Hq (setU11 ? ?))); Case/or4P; Case/eqP.
  Step Dp': (Adds enx p') = (chord_ring p enx).
    Congr Adds; Step [ ]: x = (fproj p enx).
      Case: (fprojP Henx) => [Hpy Hxy]; Apply: (scycle_cface HUp ? Hpx Hpy).
      By Rewrite: -{1 x}Enode -cface1.
    Case: p' Dp => [|z p'] Dp; Rewrite: Dp in Hp; Case/and3P: Hp => [_ Hz _];
      Rewrite: /rlink Dfex -/efex cface1 Eefex in Hz.
      By Rewrite: (adj_no_cface Hgc (adjN x)) in Hz.
    Step []: z = (fproj p (edge enx)).
      Move: (fprojP Heenx) => [Hpz' Hzz'].
      Rewrite: {1 (edge enx)}(De2c (node x)) (same_cface Hz) in Hzz'.
      By Apply: (scycle_cface HUp); Rewrite: // Dp /= /setU1 set11 !orbT.
    Symmetry; Move: Up; Rewrite: Dp -(cat1s fex); Apply: (!right_arc).
  Case: {Hrec}(Hrec (Adds enx p')).
            By Rewrite: -ltnS /=; Apply: leq_trans Hn; Rewrite: Dp /= leqnn.
          By Rewrite Dp'; Apply scycle_chord_ring.
        By Rewrite Dp'; Apply proper_chord_ring.
      By Move=> /= z Hz; Apply Hip; Rewrite: Dp /= /setU1 Hz orbT.
    Move=> z; Rewrite: Dp' diskN_chord_ring //.
    By Move=> H; Apply HipN; Case/andP: H.
  By Move=> z; Rewrite: Dp' diskF_chord_ring // /setD HpF0 andbF.
Step HeiFac: (x : gc)
     (fband erc x) -> (fband erc (edge x)) -> (diskE erc x) ->
     (diskF (chord_ring erc x)) =1 ac.
  Move=> x Hx Hex HxE; Pose rx := (chord_ring erc x).
  Step Hrxac: (sub_set (diskF rx) ac).
    Move=> y; Rewrite: /rx diskF_chord_ring // /kernel /setC -EercF.
    By Case/and3P.
  Step HUrx : (scycle rlink rx) By Apply: scycle_chord_ring.
  Step HrxF: (y : gc) (ac y) -> (diskN rx y) -> (diskF rx y).
    Move=> y Hy HyN; Rewrite: /diskF /setD HyN andbT.
    Rewrite: /kernel /setC -EercF in Hy.
    Rewrite: -(fband_chord_ring Hgc' HUerc Hx Hex) in Hy.
    By Case/norP: Hy.
  Move=> z; Apply/idP/idP; [Apply: Hrxac | Move=> Hz].
  Case: (HeiF0 ? Hx Hex HxE) => [y HyF].
  Def: Heey := (Hrxac ? HyF); Rewrite: -{1 y}De2c in Heey.
  Case: (Hhac ? ? Heey Hz) => [p [Hp Ep Ep0] [_ Hphac]].
  Step Hpac: (subset p ac).
    By Rewrite: all_setI -subset_all in Hphac; Case/andP: Hphac.
  Rewrite: /kernel subset_all /= in Hpac.
  Case: p Ep0 Ep Hp Hpac {Hphac} => //= [y1 p] _ Ep; Move/andP=> [Hyy1 Hp].
  Step Hy1: (diskF rx y1).
    By Rewrite: -(closed_connect (diskF_face rx) Hyy1) De2c; Auto. 
  Rewrite: -(closed_connect (diskF_face rx) Ep); Case/andP {Ep Hyy1}; Clear.
  Elim: p y1 Hy1 Hp => [|y2 p Hrec] y1 Hy1 //=.
  Move/andP=> [Hy12 Hp]; Move/andP=> [Hy2ac Hpac].
  Apply: (Hrec ? ? Hp Hpac) {p Hrec Hp Hpac}.
  Rewrite: /rlink cface1 in Hy12.
  Rewrite: -(closed_connect (diskF_face rx) Hy12).
  Apply HrxF; LeftBy Rewrite: /kernel /setC (closed_connect (fbandF rc) Hy12).
  By Rewrite: (fclosed1 (diskN_node rx)) Eedge; Case (andP Hy1).
Move=> x Hix Hiex; Rewrite: -!EercF; Move=> Hx Hex.
Step HexE: (diskE erc (edge x)).
  Rewrite: /diskE /setD (mem_maps (Iedge gc)) (negbE Hix) -Drrrc.
  Rewrite: (diskN_rev_ring Hgc' HUrrc Prrc).
  Apply/hasP=> [[y Hy]]; Case/connectP.
  Rewrite: /rrc mem_rev -{1 y}(f_finv (Inode gc)) -(fclosed1 HrcN) in Hy.
  Move=> [|z p]; LeftBy Move=> _ Dx; Rewrite: /setC -Dx /= Hy in Hiex.
  By Rewrite: /= {1}/dlink /rrc mem_rev Hy.
Case: (HeiF0 ? Hex); Rewrite: ?De2c //; Move=> y Hy; Move: {}Hy.
Rewrite: HeiFac in Hy; Rewrite: ?De2c // diskF_chord_ring ?De2c //.
Rewrite: -(fclosed1 (diskE_edge Hpgc HUerc)) in HexE.
By Rewrite: /setD HeiFac ?Hy.
Qed.

Lemma fcard_adj_perimeter : (x : gc) (negb (ac x)) ->
  (card (setI (cface x) [y](fband rc (edge y)))) = (2).
Proof.
Move=> x; Move/negbE2; Case/hasP=> [y Hiy Hxy].
Rewrite: (cardD1 y) (cardD1 (edge (node y))) /setD1 /setI Hxy.
Rewrite: cface1r Enode Hxy.
Step Hiny: (rc (node y)) By Rewrite: -(fclosed1 HrcN).
Case: (y =P (edge (node y))) => [Dy | _].
  By Move: (edge_perimeter (node y)); Rewrite: /setC De2c -Dy Hiy Hiny.
Step Hfey: (fband rc (edge y)).
  Apply/hasP; Exists (face (edge y)); RightBy Apply fconnect1.
  By Rewrite: (fclosed1 HrcN) Eedge.
Rewrite: De2c /setC (subsetP (ring_fband ?) ? Hiny) Hfey /=; Apply: eqP.
Apply/set0P=> [z]; Apply/and4P=> [[Hzeny Hzy Hyz Hz]]. 
Rewrite: (same_cface Hxy) in Hyz.
Case Hiz: (rc z); LeftBy Case/eqP: Hzy; Apply: (scycle_cface HUrc).
Case Hiez: (rc (edge z)).
  Case/eqP: Hzeny; Apply: (scycle_cface HUerc).
      By Rewrite: cface1 Enode.
    By Apply maps_f.
  By Rewrite: -{1 z}De2c; Apply maps_f.
Case/orP: (chordless_perimeter (negbI Hiz) (negbI Hiez)).
  By Case/hasP; Exists y; Rewrite: 1?Sface.
By Rewrite: /kernel /setC Hz.
Qed.

Lemma adj_kernel_min : (x : gc) (negb (ac x)) ->
  (EX y | (ac y) & (cface x (edge y))).
Proof.
Move=> x; Move/negbE2; Case/hasP=> [y Hiy Hxy].
Move: (allP (embeddable_ring Hgc) ? Hiy); Rewrite: /good_ring_arity /order.
Rewrite: -(cardIC [z](fband rc (edge z))) fcard_adj_perimeter.
  Case: (pickP (setI (cface y) (setC [z](fband rc (edge z))))) => [z Hz | Hy].
    Case/andP: Hz => [Hxez Hez] _; Exists (edge z); LeftDone.
    By Rewrite: De2c (same_cface Hxy).
  By Rewrite: (eq_card Hy) card0.
By Apply/idP=> [Hy]; Case/idP: (Hacbc Hy).
Qed.

Lemma adj_kernel_max : (x : gc) (negb (ac x)) ->
  (leq (card (setI (cface x) [y](ac (edge y)))) (4)).
Proof.
Move=> x; Move/negbE2; Case/hasP=> [y Hiy Hxy].
Move: (allP (embeddable_ring Hgc) ? Hiy).
Rewrite: /good_ring_arity -(arity_cface Hxy).
Rewrite: /order -(cardIC [z](fband rc (edge z))) fcard_adj_perimeter.
  Rewrite: /kernel /setC.
  Move: (card (setI (cface x) [z](negb (fband rc (edge z))))).
  Repeat Case=> //.
By Rewrite: (closed_connect HacF Hxy); Apply/idP=> [Hy]; Case/idP: (Hacbc Hy).
Qed.

Lemma embed_full : (x1, x2 : gc) (ac x1) -> (ac x2) ->
  (edge (h x1)) = (h x2) -> (edge x1) = x2.
Proof.
Cut ~(EX x1 | (EX p |
  (and3 (path rlink x1 p) (negb (last x1 p) =d x1) (sub_set p ac)) &
  (and  (edge (h (last x1 p))) = (h (edge x1)) (leq (size p) (5))))).
  Move=> Hgc5 x1 x2 Hx1 Hx2 Dhx; Apply: eqP; Apply/idPn=> [Hex12]; Case: Hgc5.
  Case: (radius2P ? (embeddable_kernel Hgc)) => [x0 Hx0 Hx0ac].
  Case: (at_radius2P HacF ? ? (Hx0ac ? Hx1)) => [x01 [x10 [Hx001 Hx110]]].
  Case: (at_radius2P HacF ? ? (Hx0ac ? Hx2)) => [x02 [x20 [Hx002 Hx220]]].
  Move=> [Hx02F Hex02] [Hx01F Hex01].
  Exists (edge x1); Exists (Seq x10 (edge x01) x02 (edge x20) x2).
    Rewrite eqd_sym; Split; Auto.
      Rewrite: /path /rlink !De2c Hx110 Sface Hex01 Hex02 -(same_cface Hx001).
      By Rewrite: Hx002 Sface Hx220.
    Apply: subsetP; Rewrite: subset_all /= Hx01F Hx2.
    Rewrite: -(closed_connect HacF Hx110) Hx1.
    Rewrite: -(closed_connect HacF Hx002) Hx0.
    By Rewrite: -(closed_connect HacF Hex02) Hx02F.
  By Split; Rewrite: //= De2c -Dhx De2m.
Cut ~(EX x | (EX p | (pre_hom_ring x p) /\ (negb (rlink (last x p) x))
                   & (leq (size p) (4)))).
  Move=> Hgc5 [x0 [p [Hp Ep Hpac] [Hhp Hp5]]].
  Cut (EX q | (and3 (path rlink x0 q) (last x0 q) = (last x0 p) (sub_set q ac))
           & (simple (maps h q)) /\ (leq (size q) (size p))).
    Move=> [[|x q] [Hq Eq Hqac] [Uq Hqp]].
      By Rewrite: -Eq /= set11 in Ep.
    Case: Hgc5; Exists x; Exists q; RightBy Exact (leq_trans Hqp Hp5).
    Step Hx: (ac x) By Exact (Hqac ? (setU11 ? ?)).
    Simpl in Hq Eq; Case/andP: Hq => [Hx0x Hq]; Split.
      Apply intro_pre_hom_ring; Rewrite: // Eq /rlink Hhp Sface.
      By Rewrite: /rlink Sface in Hx0x; Apply cface_ac_h.
    Apply/idP=> [Eqx]; Case/eqP: Ep; Apply Iedge.
    Step Hx0p: (ac (edge (last x0 p))).
      By Rewrite: -Eq (closed_connect HacF Eqx).
    Apply cface_inj_embed; Auto.
      By Rewrite: -Eq (same_cface Eqx) Sface.
    Rewrite: embed_functor // -Eq; Exact (Hqac ? (mem_last ? ?)).
  Elim: p x0 Hp Hpac Hp5 {Ep Hhp} => [|x1 p Hrec] x0.
    By Do 2 Clear; Exists (Seq0 gc); Split; Try Move=> y.
  Simpl; Move/andP=> [Dx1 Hp1] Hpac Hp5.
  Case: {Hrec Hp1}(Hrec ? Hp1 [z;Hz](Hpac ? (setU1r ? Hz)) (ltnW Hp5)).
  Move=> q [Hq Eq Hqac] [Uq Hqp].
  Case Hhqx1: (negb (fband (maps h q) (h x1))).
    Exists (Adds x1 q); Split; Auto; Try By Rewrite: /= Dx1.
      Move=> y; Case/setU1P=> [Dy | Hy]; RightBy Auto.
      By Apply Hpac; Rewrite: Dy setU11.
    By Rewrite: maps_adds simple_adds Hhqx1.
  Case/hasP: Hhqx1 => [u]; Rewrite: Sface; Case/mapsP=> [x2 Hqx2 []] {u} Hhx12.
  Step Hx2: (ac x2) By Apply Hqac.
  Case: (cface_h_ac Hx2 Hhx12) => [x3 Hx23 Hhx13].
  Step Hx3: (ac x3) By Rewrite: -(closed_connect HacF Hx23).
  Case/splitP: {q}Hqx2 Hq Eq Hqp Uq Hqac => [q1 q2].
  Rewrite: path_cat last_cat last_add_last cat_add_last size_cat /=.
  Move/andP=> [Hq1 Hq2] Eq2 Hqp Uq Hqac.
  Case Hx13: (x1 =d x3).
    Exists (Adds x2 q2); Split; Auto.
          By Rewrite: /= {1}/rlink (same_cface Dx1) (eqP Hx13) Sface Hx23.
        By Move=> z Hz; Apply Hqac; Rewrite: mem_cat /setU Hz orbT.
      By Rewrite: maps_cat simple_cat in Uq; Case/and3P: Uq.
    Apply: (leqW (leq_trans ? Hqp)); Exact (leq_addl ? ?).
  Step Hx1: (ac x1) By Exact (Hpac ? (setU11 ? ?)).
  Case: {q}Hgc5; Case: q1 Hqp Uq Hqac Hq1 => [|x q].
    Do 3 Clear; Move=> Hx12; Rewrite: /= andbT in Hx12.
    Rewrite: -(closed_connect HacF Hx12) in Hx2.
    Move/(cface_ac_h Hx2): Hx12.
    By Rewrite: Sface (embed_functor Hx1 Hx2) (same_cface Hhx12) Hbgm.
  Move=> Hqp Uq Hqac Hq; Exists x; Exists (add_last q x3);
    RightBy Rewrite size_add_last;
    Exact (leq_trans (leq_addr ? ?) (leq_trans Hqp Hp5)).
  Step Hx: (ac x) By Exact (Hqac ? (setU11 ? ?)).
  Rewrite: /= -cats1 path_cat in Hq; Case/andP: Hq => [Hx1x Hq].
  Step Hex1: (ac (edge x1)) By Rewrite: (closed_connect HacF Hx1x).
  Rewrite last_add_last; Split.
    Apply intro_pre_hom_ring; Auto.
      By Rewrite: -cats1 path_cat /= {2}/rlink Sface -(same_cface Hx23) Sface.
      By Rewrite: last_add_last Hhx13 /rlink -embed_functor // cface_ac_h.
      Move=> y Hy; Rewrite: -cats1 -cat_adds cats1 mem_add_last /= in Hy.
      Case/setU1P: Hy => [[] | Hy] //.
      By Apply Hqac; Rewrite: mem_cat /setU /= Hy.
    Move: Uq; Rewrite: -cats1 -cat_adds cats1 -cat_add_last !maps_cat simple_cat.
    Rewrite: !maps_add_last !simple_add_last; Move/and3P=> [Uq _ _].
    By Rewrite: -[q'](closed_connect (fbandF q') (cface_ac_h Hx2 Hx23)).
  Apply/idP=> [Hx3x]; Case/eqP: Hx13; Apply Iedge.
  Rewrite: /rlink Sface -(same_cface Hx1x) in Hx3x.
  Apply (cface_inj_embed Hex1 Hx3x).
  Rewrite: (embed_functor Hx1 Hex1) -Hhx13 (embed_functor Hx3) //.
  By Rewrite: -(closed_connect HacF Hx3x).
Cut ~(EX x | (EX p | (pre_hom_ring x p) /\ (negb (rlink (last x p) x))
  & [xp := (Adds x p)] (leq (fcard face (diskF (maps h xp))) (size xp) =d (5)))).
  Move=> Hgc5 [x [p Hp Hp5]]; Pose xp := (Adds x p).
  Step Hphp: (proper_ring (maps h xp)).
    Rewrite: ~/xp; Case: p Hp {Hp5} => [|y [|y' p']] //.
      Move=> [[_ _ H] _]; Move: H.
      By Rewrite: /scycle /= /rlink Sface Hbgm.
    Move=> [[Hxy Hac _] H]; Apply/eqP=> [Hhxy]; Case/idP: H.
    Move: {Hac}(Hac ? (setU11 ? ?)) (Hac ? (setU1r ? (setU11 ? ?))) => Hx Hy.
    Rewrite: /= andbT in Hxy; Simpl.
    Def: Hex := Hy; Rewrite: -(closed_connect HacF Hxy) in Hex.
    Rewrite: -(embed_functor Hx Hex) in Hhxy.
    By Rewrite: -(cface_inj_embed Hex Hxy Hhxy) /rlink De2c connect0.
  Case Hgc5; Exists x; Exists p; LeftDone.
  Rewrite: /= -(size_maps h) leqNgt; Apply/idP=> [HhpF].
  Case: Hp => [[Hp Hpac HUhp] Ep].
  Step Hhxy : (cface (h x) (edge (h (last x p)))).
    Case: (andP HUhp); Rewrite: (cycle_path (h x)) /= last_maps.
    By Rewrite Sface; Case/andP.
  Step Hx: (ac x) By Exact (Hpac ? (setU11 ? ?)).
  Case/lastP Dp: p / {}p => [|p' y]; LeftBy Rewrite: Dp /= Hbgm in Hhxy.
  Step Dy: y = (last x p) By Rewrite: Dp last_add_last.
  Step Hy: (ac y) By Rewrite Dy; Exact (Hpac ? (mem_last ? ?)).
  Case: (cface_h_ac Hx Hhxy) => [ry Hxry Dhry].
  Pose rp := (add_last (rev (maps edge (belast x p'))) ry).
  Pose rx := (edge (last x p')); Pose rxp := (Adds rx rp).
  Step Ehrp: (maps h rxp) = (rot (1) (rev_ring (maps h xp))).
    Rewrite: /xp lastI /rev_ring !maps_add_last rev_add_last rot1_adds -Dhry.
    Rewrite: Dp belast_add_last ~/rxp ~/rx ~/rp.
    Rewrite: -cats1 -cat_adds cats1 -rev_add_last -maps_add_last -lastI.
    Rewrite: maps_add_last; Congr add_last.
    Apply: (monic_move (!rev_rev ?)); Move: Hp (introT subsetP Hpac).
    Rewrite: ~Dp /subset {1}/setC disjoint_has /=.
    Elim: p' {}x => [|x2 p1 Hrec] x1; Rewrite: /= negb_orb negb_elim ?andbT.
      Move=> Hx1y; Move/andP=> [Hx1 _].
      Rewrite: -(closed_connect HacF Hx1y) in Hy.
      By Rewrite: (embed_functor Hx1 Hy).
    Move/andP=> [Hx12 Hp1]; Move/andP=> [Hx1 Hp1ac]; Move/norP: {}Hp1ac=> [Hx2 _].
    Rewrite: -(closed_connect HacF Hx12) negb_elim in Hx2.
    By Rewrite: rev_adds maps_add_last rev_add_last embed_functor ?Hrec.
  Case: Hgc5; Exists rx; Exists rp.
    Split.
      Split.
          Move: Hxry Hp; Rewrite: Sface /rx /rp ~{Dhry}Dp.
          Elim: {}p' {}ry {}x => [|x3 p1 Hrec] x1 x2 /= Hx12.
            By Clear; Rewrite: /rlink De2c Sface Hx12.
          Move/andP=> [Hx23 Hp1]; Rewrite: -cats1 rev_adds path_cat last_add_last.
          By Rewrite:  Hrec //= andbT /rlink De2c Sface.
        Move=> z; Rewrite: /rx /rp -cats1 -cat_adds cats1 mem_add_last.
        Rewrite: -rev_add_last /= /setU1 mem_rev -maps_add_last -lastI.
        Rewrite: -{2 z}De2c (mem_maps (Iedge gc)).
        Case/orP=> [Dz | Hz].
          By Rewrite: -(eqP Dz) -(closed_connect HacF Hxry).
        Move: Hp Hpac; Rewrite: ~Dp; Case/splitPl: Hz => [p1' p2' Dez].
        Rewrite: -cats1 -catA cats1 -{(add_last p2' y)}drop0.
        Rewrite: (drop_sub x) ?size_add_last // sub0 path_cat /= Dez.
        Rewrite: /rlink De2c; Move/and3P=> [_ Hez _] Hp'ac.
        Rewrite: (closed_connect HacF Hez); Apply Hp'ac.
        By Rewrite: /setU1 mem_cat /setU /= setU11 !orbT.
      Rewrite: Ehrp /scycle cycle_rot /simple maps_rot uniq_rot.
      Exact (scycle_rev_ring Hgm' HUhp).
    Rewrite: Dp -cats1 path_cat in Hp; Case/and3P: Hp => [_ Hp'y _].
    Rewrite: /rp /rx last_add_last /rlink Sface ~{Hp'y}(same_cface Hp'y).
    Apply/idP=> [Hyry]; Case/idP: Ep; Move: (monic_move De2m (esym Dhry)).
    Rewrite: (closed_connect HacF Hxry) in Hx.
    Def: Hery := Hy; Rewrite: (closed_connect HacF Hyry) in Hery.
    Rewrite: -Dy -(embed_functor Hx Hery); Move=> Dhy.
    By Rewrite: (cface_inj_embed Hy Hyry Dhy) /rlink De2c Sface.
  Step EhrpF: (diskF (maps h rxp)) =1 (diskF (rev_ring (maps h xp))).
    By Move=> z; Rewrite: Ehrp diskF_rot.
  Rewrite: -/rxp {rxp}lock /= -!lock.
  Step [ ]: (size (maps h xp)) = (size rxp).
    Rewrite: /rxp /xp /rp /= size_maps Dp !size_add_last size_rev size_maps.
    By Rewrite: size_belast.
  Rewrite: (eq_n_comp_r EhrpF) leqNgt.
  Rewrite: (eq_n_comp_r (diskF_rev_ring Hgm HUhp Hphp)).
  Rewrite: -(size_maps h) in Hp5; Apply/idP=> [HrpF].
  Case [H](elimF andP (birkhoff Hgm H HUhp)); Auto.
Move=> [x [p [Hp Ep] Hp5]].
Case Hp0: (leq (fcard face (diskF (maps h (Adds x p)))) (0)).
  By Case (negP Ep); Apply trivial_hom_ring.
Case: ((size (Adds x p)) =P (5)) Hp5 => [Dp5 | _];
  RightBy Exact (elimF idP Hp0).
Rewrite leqn0 in Hp0; Case/set0Pn: Hp0 => [u Hu].
Rewrite: /n_comp (cardD1 u) Hu; Case/andP: Hu; Case: Hp Dp5.
Def Dxp: xp := (Adds x p); Rewrite: -(size_maps h) /= add1n ltnS.
Pose hxp := (maps h xp); Move=> Hp Hpac HUhxp Dp5 Hu HuF HxpF.
Def: HxpFf := (closed_connect (diskF_face hxp)).
Step DxpF: (diskF hxp) =1 (cface u).
  Move=> y; Symmetry; Apply/idP/idP=> [Huy | HyF].
    By Rewrite: -(HxpFf ? ? Huy) HuF.
  Apply/(rootP (Sface ?)); Apply: eqP; Apply/idPn=> [Huy].
  Rewrite: leqn0 /setI /setD1 in HxpF; Move: (set0P HxpF (froot face y)).
  Rewrite: (eqP Hu) in Huy; Rewrite Huy.
  By Rewrite: (roots_root (Sface gm)) -(HxpFf ? ? (connect_root ? y)) HyF.
Clear HxpF Hu; Pose ru := (spoke_ring u); Pose frf := (froots (!face gm)).
Step ExpF: (fband hxp) =1 (fband ru).
  Step HpFr: (subset (setI frf (fband ru)) (setI frf (fband hxp))).
    Apply/subsetP=> [v']; Case Hv': (frf v'); Rewrite: /setI ~Hv' //=.
    Move/hasP=> [v Hv Hvv'].
    Rewrite: ~{v' Hvv'}(closed_connect (fbandF hxp) Hvv').
    Rewrite: /ru mem_spoke_ring in Hv.
    Step HvF: (diskF hxp v) = false.
      By Rewrite: DxpF (same_cface Hv) -{2 v}Enode -cface1r Hbgm.
    Step HvN: (diskN hxp v).
      Rewrite: (fclosed1 (diskN_node hxp)).
      By Rewrite: -DxpF in Hv; Case/andP: Hv.
    By Rewrite: /diskF /setD HvN andbT in HvF; Apply negbEf.
  Step EpFr: (fcard face (fband ru)) = (fcard face (fband hxp)).
    Apply: eqP; Rewrite: eqn_leq {1 2}/n_comp -/frf (subset_leq_card HpFr).
    Rewrite: (scycle_fcard_fband HUhxp) Dp5.
    Rewrite: (!scycle_fcard_fband gm rlink); RightBy Apply: scycle_spoke_ring.
    By Rewrite: /ru size_spoke_ring HgmF.
  Move=> v; Move: (subset_cardP EpFr HpFr (froot face v)).
  Rewrite: /setI (roots_root (Sface gm)) /=.
  By Rewrite: -![q](closed_connect (fbandF q) (connect_root ? v)).
Step Hhpu: (sub_set hxp ru).
  Case: (andP HUhxp) => [Hhp _] v Hv.
  Step Huv: (adj u v).
    Rewrite: -fband_spoke_ring -/ru -ExpF; Exact (subsetP (ring_fband ?) ? Hv).
  Step Huev: (adj u (edge v)).
    Rewrite: (adjFr (next_cycle Hhp Hv)) -fband_spoke_ring -/ru -ExpF.
    By Apply: (subsetP (ring_fband ?)); Rewrite mem_next.
  Case/orP: (adj11_edge Hgm Huv Huev); Auto.
  Rewrite: /ru mem_spoke_ring -DxpF; Case/andP; Clear.
  Rewrite: -(fclosed1 (diskN_node hxp)) diskN_edge_ring //.
  By Move: Dp5; Rewrite: /hxp Dxp; Case: (p) => [|y1 [|y2 p']].
Step Hhp1: (cycle [v](set1 (face (face (edge v)))) hxp).
  Case: (andP HUhxp) => [Hhp UUhp].
  Apply cycle_from_next; LeftBy Apply simple_uniq.
  Def: HUu := (scycle_spoke_ring Hgm u).
  Move=> v Hv; Def: Huv := (Hhpu ? Hv).
  Apply/eqP; Apply: (scycle_cface HUu).
      Rewrite: -!cface1; Exact (next_cycle Hhp Hv).
    By Move: (Huv); Rewrite: -mem_next (next_spoke_ring Hgm Huv).
  By Apply Hhpu; Rewrite mem_next.
Rewrite: (cycle_path (h x)) /hxp Dxp /= last_maps in Hhp1.
Case/andP: Hhp1 => [Dhx Hhpr].
Step Hxpnx: (subset (maps node xp) (cface (node x))).
  Move: (introT subsetP Hpac); Rewrite: Dxp /subset {1}/setC !disjoint_has.
  Rewrite: /= {1}/setC connect0 /=.
  Elim: (p) (x) Hp Hhpr => [|x2 p1 Hrec] x1 //=.
  Move/andP=> [Hx12 Hp1]; Move/andP=> [Dhx2 Hp1r].
  Rewrite: /= negb_orb negb_elim; Move/andP=> [Hx1 Hp1ac].
  Step Hnx12: (cface (node x1) (node x2)).
    Case: (norP Hp1ac) => [Hx2 _]; Rewrite: negb_elim in Hx2.
    Def: Hex1 := Hx2; Rewrite: -(closed_connect HacF Hx12) in Hex1.
    Def: Hfex1 := Hex1; Rewrite: (fclosed1 HacF) in Hfex1.
    Rewrite: -(embed_functor Hx1 Hex1) eqd_sym in Dhx2.
    Rewrite: -(HhF Hex1) -(HhF Hfex1) in Dhx2.
    Rewrite: /rlink 2!cface1 Sface in Hx12.
    Rewrite: -{(node x2)}De2c (cface_inj_embed Hx2 Hx12 (eqP Dhx2)) Eface.
    Rewrite: cface1r -{2 x1}Dn3c ?Enode ?connect0 //; Exact (Hacbc Hx1).
  Rewrite: {1}/setC Hnx12 /= -(eq_has 2!(setC (cface (node x2)))); Auto.
  By Move=> z; Rewrite: /setC (same_cface Hnx12).
Case Hnx: (ac (node x)).
  Case/idP: Ep; Pose y := (last x p); Rewrite: Dxp in Hpac.
  Step Hx: (ac x) By Exact (Hpac ? (setU11 ? ?)).
  Step Henx: (ac (edge (node x))) By Rewrite: (fclosed1 HacF) Enode.
  Step Hy: (ac y) By Exact (Hpac ? (mem_last ? ?)).
  Step Heny: (ac (edge (node y))) By Rewrite: (fclosed1 HacF) Enode.
  Step Hnxny: (cface (node x) (node y)).
    Apply (subsetP Hxpnx); Rewrite: (mem_maps (Inode gc)) Dxp.
    Exact (mem_last ? ?).
  Step Hny: (ac (node y)) By Rewrite: -(closed_connect HacF Hnxny).
  Step Dhny: (h (node y)) = (h (face (node x))).
    Rewrite: (HhF Hnx) -{(h (node x))}Eedge -(embed_functor Hnx Henx).
    Rewrite: -(HhF Henx) Enode -(eqP Dhx) -/y.
    Rewrite: -{(h y)}Dn3m Enode -{(node (node (h y)))}De2m Eedge Enode.
    By Rewrite: -{2 y}Enode (HhF Heny) (embed_functor Hny Heny) Eedge.
  Rewrite: cface1 Sface in Hnxny.
  Step Hrcy: (bc y) By Exact (Hacbc Hy).
  Rewrite: /rlink -(Dn3c Hrcy) 2!cface1 Enode -{(node (node y))}De2c.
  By Rewrite: (cface_inj_embed Hny Hnxny Dhny) Eface Enode connect0.
Step Hxpnxac: (subset (maps node xp) (setI (cface (node x)) [y](ac (edge y)))).
  Apply/subsetP=> [y Hy]; Rewrite: /setI (subsetP Hxpnx ? Hy).
  Case/mapsP: Hy => [z Hz []]; Rewrite: (fclosed1 HacF) Enode /=; Auto.
Move: (leq_trans (subset_leq_card Hxpnxac) (adj_kernel_max (negbI Hnx))).
Step Unxp: (uniq (maps node xp)).
  Case: (andP HUhxp); Clear; Move/simple_uniq=> Uhxp.
  Rewrite (uniq_maps (Inode gc)); Exact (maps_uniq Uhxp).
By Rewrite: /hxp size_maps in Dp5; Rewrite: (card_uniqP Unxp) size_maps Dp5.
Qed.

Lemma pre_embed_inj : (x, y : gc) (ac x) -> (ac y) -> (h x) = (h y) -> x = y.
Proof.
Move=> x y Hx Hy Dhx; Def: Heex := Hx; Rewrite: -{x}De2c in Heex.
Case: (Hhac ? ? Heex Hy) => [[|z [|z' p]] [Hp Ep Ep0] [_ Hpac]] {Ep0}//.
  Move/andP: Hp => [Hxz _]; Rewrite: /= -(same_cface Hxz) De2c in Ep.
  By Apply cface_inj_embed.
Move/and3P: Hp => [Hxz Hzz' _]; Rewrite: /rlink De2c in Hxz.
Step Hz: (ac z) By Rewrite: -(closed_connect HacF Hxz).
Step Hez: (ac (edge z)).
  By Rewrite: (closed_connect HacF Hzz'); Case/and3P: Hpac => [_]; Case/andP.
Move: (cface_ac_h Hx Hxz); Rewrite: Dhx; Move=> Hhyz.
Case: (cface_h_ac Hy Hhyz) (embed_functor Hz Hez) => [t Hyt [ ]] Hezt.
Step Ht: (ac t) By Rewrite: -(closed_connect HacF Hyt).
Rewrite: (Iedge ? (embed_full Ht Hez (esym Hezt))) in Hyt.
By Rewrite: Sface -(same_cface Hxz) in Hyt; Apply cface_inj_embed.
Qed.

Definition embed [x : gc] : gm :=
  if (ac x) then (h x) else
  if (ac (edge x)) then (edge (h (edge x))) else
  if (ac (node x)) then (face (edge (h (node x)))) else
  (edge (node (node (h (node (edge x)))))).

Syntactic Definition h1 := embed.

Lemma embed_cases : (x : gc)
  ((ac x) \/ (ac (edge x))) \/ ((ac (node x)) \/ (ac (node (edge x)))).
Proof.
Cut (x : gc) (bc x) -> ((ac x) \/ (ac (edge x))) \/ (ac (node x)).
  Move=> Hkic x; Move: (orP (edge_perimeter x)).
  Move=> [H | H]; Move: (Hkic ? H); Rewrite: ?De2c; Tauto.
Move=> x Hix; Case Hiex: (bc (edge x)).
  By Case: (orP (chordless_perimeter Hix Hiex)); Tauto.
Case Hienx: (bc (edge (node x))).
  Rewrite: /setC (fclosed1 HrcN) in Hix;
  Case: (orP (chordless_perimeter Hix Hienx)); Try Tauto.
  By Rewrite: (fclosed1 HacF) Enode; Tauto.
Rewrite: -{1 x}Eface De2c /setC -(fclosed1 HrcN) in Hiex.
Step Dfx: (face x) = (edge (node x)).
  Apply: (scycle_cface HUrc ? (negbEf Hiex) (negbEf Hienx)).
  By Rewrite: -cface1 cface1r Enode connect0.
Step EfxF: (cface (face x)) =1 (seq2 x (face x)).
  Apply fconnect_cycle; LeftBy Rewrite: /= /eqdf Dfx Enode !set11.
  By Rewrite: /= setU1r ?setU11.
Move: (allP (embeddable_ring Hgc) ? (negbEf Hiex)).
Rewrite: /good_ring_arity /order (eq_card EfxF).
By Move=> H; Move: H (card_size (seq2 x (face x))); Case/or4P; Case/eqP.
Qed.

Lemma embedE : (x : gc) (embed (edge x)) = (edge (embed x)).
Proof.
Cut (x : gc) (bc x) -> (embed (edge x)) = (edge (embed x)).
  Move=> HbcE x; Case: (orP (edge_perimeter x)) => [Hx | Hex]; Auto.
  By Rewrite: -{2 x}De2c (HbcE ? Hex) De2m.
Move=> x Hix; Rewrite: /embed; Rewrite: De2c.
Case Hx: (ac x); Case Hex: (ac (edge x)); Rewrite: ?De2m //.
  By Rewrite: embed_functor.
Case: (embed_cases x); Move/(introT orP); LeftBy Rewrite: Hx Hex.
Case Hnex: (ac (node (edge x))).
  Def: Hiex := (Hacbc Hnex); Rewrite: /setC -(fclosed1 HrcN) in Hiex.
  By Move: (chordless_perimeter Hix Hiex); Rewrite: Hx Hex.
By Rewrite orbF; Case/esym; Rewrite: -{2 (h (node x))}Dn3m Enode.
Qed.

Lemma embedN : (x : gc) (bc x) -> (embed (node x)) = (node (embed x)).
Proof.
Move=> x Hix; Rewrite: /embed.
Rewrite: (fclosed1 HacF (edge (node x))) Enode.
Rewrite: -{(node (node x))}Enode (Dn3c Hix) -(fclosed1 HacF).
Case Hx: (ac x).
  Rewrite: -{1 x}Enode -(fclosed1 HacF) in Hx.
  Apply Iedge; Rewrite: -{4 x}Enode (HhF Hx) Eface.
  By Case Hnx: (ac (node x)); [Rewrite embed_functor | Rewrite De2m].
Case Hex: (ac (edge x)).
  Case Hnx: (ac (node x)).
    Rewrite: -{(h (edge x))}Eface De2m -(HhF Hex) -{2 x}(Dn3c Hix) Enode.
    Rewrite: (fclosed1 HacF) -(Dn3c Hix) Enode in Hex.
    Rewrite: -{(node x)}Enode -(fclosed1 HacF) in Hnx.
    Rewrite: -{1 (node x)}Enode (HhF Hnx) (embed_functor Hex Hnx).
    By Apply Inode; Rewrite: Dn3m Eedge.
  Rewrite: -{(h (face (edge x)))}Dn3m Enode (HhF Hex).
  By Rewrite: -{1 (h (edge x))}De2m Eedge.
Case: (embed_cases x); Move/(introT orP); LeftBy Rewrite: Hx Hex.
Case Hnex: (ac (node (edge x))).
  Def: Hiex := (Hacbc Hnex); Rewrite: /setC -(fclosed1 HrcN) in Hiex.
  By Move: (chordless_perimeter Hix Hiex); Rewrite: Hx Hex.
By Rewrite orbF; Case/esym; Rewrite: Eedge.
Qed.

Lemma embed_inj : (x, y : gc) (bc x) -> (bc y) ->
  (embed x) = (embed y) -> x = y.
Proof.
Step HbcN: (x : gc) (bc x) -> (ac x) = false -> (ac (edge x)) = false ->
    (ac (node x)).
  Move=> x Hix Hx Hex.
  Case: (embed_cases x); Move/(introT orP); LeftBy Rewrite: Hx Hex.
  Case Hnex: (ac (node (edge x))); RightBy Rewrite orbF.
  Def: Hiex := (Hacbc Hnex); Rewrite: /setC -(fclosed1 HrcN) in Hiex.
  By Move: (chordless_perimeter Hix Hiex); Rewrite: Hx Hex.
Move=> x y Hix Hiy; Rewrite: /embed.
Case Hx: (ac x).
  Case Hy: (ac y); LeftBy Exact (pre_embed_inj Hx Hy).
  Case Hey: (ac (edge y)).
    By Move=> Dh; Rewrite: -{1 y}De2c (embed_full Hey Hx (esym Dh)) Hx in Hy.
  Move: (HbcN ? Hiy Hy Hey) => Hny; Rewrite Hny.
  Rewrite: -{1 x}Enode -(fclosed1 HacF) in Hx; Rewrite: -{1 x}Enode (HhF Hx).
  Move=> Dh; Rewrite: -(embed_full Hny Hx (Iface ? (esym Dh))) in Hx.
  By Rewrite: (fclosed1 HacF) Enode Hy in Hx.
Case Hex: (ac (edge x)).
  Case Hy: (ac y).
    By Move=> Dh; Rewrite: -(embed_full Hex Hy Dh) De2c Hx in Hy.
  Case Hey: (ac (edge y)).
    Exact [Dh](Iedge ? (pre_embed_inj Hex Hey (Iedge ? Dh))).
  Move: (HbcN ? Hiy Hy Hey) => Hny; Rewrite Hny.
  Rewrite: -{(node y)}Enode -(fclosed1 HacF) in Hny.
  Rewrite: -{(edge (h (edge x)))}Eedge De2m -(HhF Hex).
  Rewrite: (fclosed1 HacF) in Hex.
  Rewrite: -{(node y)}Enode (HhF Hny) -{(h (edge (node (node y))))}De2m.
  Rewrite: -{(edge (h (edge (node (node y)))))}Dn3m !Enode.
  Move=> Dh; Rewrite: -(embed_full Hny Hex (Inode ? (esym Dh))) in Hex.
  Rewrite: De2c -{(node (node y))}Enode (Dn3c Hiy) in Hex.
  By Rewrite: -(fclosed1 HacF) Hey in Hex.
Move: (HbcN ? Hix Hx Hex) => Hnx; Rewrite Hnx.
Case Hy: (ac y).
  Rewrite: -{1 y}Enode -(fclosed1 HacF) in Hy; Rewrite: -{1 y}Enode (HhF Hy).
  Move=> Dh; Rewrite: -(embed_full Hnx Hy (Iface ? Dh)) in Hy.
  By Rewrite: (fclosed1 HacF) Enode Hx in Hy.
Case Hey: (ac (edge y)).
  Rewrite: -{(node x)}Enode -(fclosed1 HacF) in Hnx.
  Rewrite: -{(edge (h (edge y)))}Eedge De2m -(HhF Hey).
  Rewrite: (fclosed1 HacF) in Hey.
  Rewrite: -{(node x)}Enode (HhF Hnx) -{(h (edge (node (node x))))}De2m.
  Rewrite: -{(edge (h (edge (node (node x)))))}Dn3m !Enode.
  Move=> Dh; Rewrite: -(embed_full Hnx Hey (Inode ? Dh)) in Hey.
  Rewrite: De2c -{(node (node x))}Enode (Dn3c Hix) in Hey.
  By Rewrite: -(fclosed1 HacF) Hex in Hey.
Move: (HbcN ? Hiy Hy Hey) => Hny; Rewrite Hny.
Exact [Dh](Inode ? (pre_embed_inj Hnx Hny (Iedge ? (Iface ? Dh)))).
Qed.

Local ddart : finSet := (subFin bc).

Definition embd_edge [x : gc] : gc :=
  if (bc (edge x)) then (edge x) else (edge (node (edge x))).

Remark Hdedge : (u : ddart) (bc (embd_edge (subdE u))).
Proof.
Move=> [x Hx]; Rewrite: /= /embd_edge; Case Hiex: (bc (edge x)); Auto.
Move: (edge_perimeter (node (edge x))).
By Rewrite: /setC -(fclosed1 HrcN) (negbEf Hiex).
Qed.

Remark Hdnode : (u : ddart) (bc (node (subdE u))).
Proof. By Move=> [x Hx]; Rewrite: /= /setC -(fclosed1 HrcN). Qed.

Definition embd_face [x : gc] : gc :=
  if (bc (face x)) then (face x) else (face (face x)).

Remark Hdface : (u : ddart) (bc (embd_face (subdE u))).
Proof.
Move=> [x Hx]; Rewrite: /= /embd_face.
Case Hfx: (bc (face x)) (edge_perimeter (face x)); Auto.
By Rewrite: /= -{1 (face x)}Eface De2c /setC -(fclosed1 HrcN).
Qed.

Local dedge [u : ddart] : ddart := (subdI (Hdedge u)).
Local dnode [u : ddart] : ddart := (subdI (Hdnode u)).
Local dface [u : ddart] : ddart := (subdI (Hdface u)).

Remark Hemb_disk : (monic3 dedge dnode dface).
Proof.
Hnf; Move=> [x Hx]; Apply: (subdE_inj ?); Rewrite: /= /embd_edge.
Case Hex: (bc (edge x)); RightBy Rewrite: /embd_face Enode Hex Eedge.
By Rewrite: /embd_face /setC (fclosed1 HrcN) Eedge (negbE Hx) /= Eedge.
Qed.

Definition emb_disk : hypermap := (Hypermap Hemb_disk).
Definition embd [u : emb_disk] : gc := (subdE u).

Lemma inj_embd : (injective embd). Proof. Exact (subdE_inj 2!?). Qed.

Lemma codom_embd : (codom embd) =1 bc.
Proof.
Move=> z; Apply/set0Pn/idP=> [[[y Hy] Dy] | Hz]; LeftBy Rewrite: (eqP Dy).
Exists ((subdI Hz)::emb_disk); Exact (set11 ?).
Qed.

Definition embd_ring : (seq emb_disk) := (preimage_seq embd erc).

Lemma maps_embd_ring : (maps embd embd_ring) = erc.
Proof.
Apply: maps_preimage => [x Hex]; Rewrite: codom_embd.
Rewrite: -{1 x}De2c (mem_maps (Iedge gc)) in Hex.
By Move: (edge_perimeter x); Rewrite: /setC orbC Hex.
Qed.

Lemma cface_embd: (u, v : emb_disk) (cface u v) = (cface (embd u) (embd v)).
Proof.
Move=> u v; Apply/idP/idP.
  Case/connectP=> [p Hp []] {v}.
  Elim: p u Hp => [|v p Hrec] [x Hx]; [Clear; Apply: connect0 | Simpl].
  Rewrite: {1}/eqdf -(inj_eqd inj_embd); Move/andP=> [Dv Hp].
  Apply: (connect_trans ? (Hrec ? Hp)); Rewrite: -(eqP Dv) /= /embd_face.
  By Case (bc (face x)); Rewrite: -!cface1r connect0.
Move/connectP=> [p Hp Ep].
Elim: {p}(S (size p)) u {-2}p (ltnSn (size p)) Hp Ep => [|n Hrec] // u.
Case=> [|y p] Hn; LeftBy Move=> _ Dv; Apply eq_connect0; Apply inj_embd.
Rewrite: cface1 /=; Case/andP; Case: u {Hrec}(Hrec (face u)) => [x Hx].
Rewrite: /= /embd_face; Move=> Hrec Dy Hp; Move: Hrec; Rewrite: (eqP Dy).
Case Hy: (bc y); LeftBy Move=> Hrec Ep; Apply (Hrec p).
Case: p Hn Hp => [|z p] /=.
  By Case: v => [z Hz] _ _ _ Dy'; Rewrite: Dy' /= Hz in Hy.
Move=> Hn; Move/andP=> [Dz Hp]; Rewrite (eqP Dz).
By Move=> Hrec Ep; Apply (Hrec p (ltnW Hn)).
Qed.

Lemma scycle_embd_ring : (sfcycle edge embd_ring).
Proof.
Step UrF : (simple embd_ring).
  Move: (scycle_simple HUerc); Rewrite: -maps_embd_ring.
  Elim: {}embd_ring => [|u q Hrec] //; Rewrite: simple_adds /= simple_adds.
  Move/andP=> [Hu Hq]; Apply/andP; Split; Auto; Clear: Hrec Hq.
  Apply/hasP=> [[v Hv Huv]]; Case/hasP: Hu.
  By Exists (embd v); [Apply maps_f | Rewrite: -cface_embd].
Rewrite: /scycle UrF andbT; Def: Ur := (simple_uniq UrF).
Apply: (cycle_from_next Ur) => [u Hu]; Apply/eqP; Apply inj_embd.
Rewrite: -(mem_maps inj_embd) maps_embd_ring -{(embd u)}De2c in Hu.
Rewrite: (mem_maps (Iedge gc)) in Hu.
Rewrite: -(next_maps inj_embd Ur) maps_embd_ring -{(embd u)}De2c.
Rewrite: (next_maps (Iedge gc) (simple_uniq UrcF)).
By Rewrite: -(eqP (next_cycle Hrc Hu)) /= -/(embd u) /embd_edge /setC Hu.
Qed.

Remark HidE: (fclosed edge embd_ring).
Proof.
Apply: (intro_closed (Sedge ?)).
Case: (andP scycle_embd_ring) => [Hr _] x y Dy Hx.
By Rewrite: -(fconnect_cycle Hr Hx) connect1. 
Qed.

Definition embdd [u : emb_disk] : gm := (embed (embd u)).

Lemma embdd_inj : (injective embdd).
Proof.
Move=> [x Hx] [y Hy] Dh; Apply: (inj_embd ?); Exact (embed_inj Hx Hy Dh).
Qed.

Lemma embddE : (u : emb_disk)
  (setC embd_ring u) -> (embdd (edge u)) = (edge (embdd u)).
Proof.
Move=> [x Hx]; Rewrite: /setC -(mem_maps inj_embd) maps_embd_ring /=.
Rewrite: /embdd /= -embedE -{1 x}De2c (mem_maps (Iedge gc)) /embd_edge.
By Move=> H; Rewrite: /setC H.
Qed.

Lemma embddN : (u : emb_disk) (embdd (node u)) = (node (embdd u)).
Proof. By Move=> [x Hx]; Rewrite: /embdd /= (embedN Hx). Qed.

Local rdom : (set gm) := (setC (image embdd (setC embd_ring))).
Local rdart : finSet := (subFin rdom).

Remark Hredge : (w : rdart) (rdom (edge (subdE w))).
Proof.
Move=> [u Hu]; Apply/set0Pn=> [[x]]; Move/andP=> [Du Hx].
Rewrite: /preimage /= (monic2F_eqd De2m) -(embddE Hx) in Du.
Case/set0Pn: Hu; Exists (edge x); Rewrite: /setI /preimage Du /=.
By Apply/idP=> [Hex]; Rewrite: /setC (fclosed1 HidE) /= Hex in Hx.
Qed.

Local erc1 [u : gm; x : emb_disk] : bool :=
  (andb (embd_ring x) u =d (embdd x)).

Definition embr_node [u : gm] : gm :=
  if (pick (erc1 u)) then [x](embdd (node (face x))) else (node u).

Remark Hrnode : (w : rdart) (rdom (embr_node (subdE w))).
Proof.
Move=> [u Hu]; Apply/set0Pn=> [[x]]; Move/andP=> [Du Hx]; Move: Du.
Rewrite: /preimage /= /embr_node.
Case: (pickP (erc1 u)) => [y Hy | Hu'].
  Case/andP: Hy => [Hy _] Dx; Case/idP: Hx.
  By Rewrite: -(embdd_inj (eqP Dx)) (fclosed1 HidE) Eface.
Rewrite: -{1 x}Eedge embddN (inj_eqd (Inode gm)); Move=> Du.
Case/set0Pn: Hu; Exists (face (edge x)); Rewrite: /setI /preimage Du.
By Apply/idP=> [Hfex]; Move: (Hu' (face (edge x))); Rewrite: /erc1 Du Hfex.
Qed.

Definition embr_face [u : gm] : gm :=
  if (pick (erc1 (edge u))) then [x](embdd (edge x)) else (face u).

Remark Hrface : (w : rdart) (rdom (embr_face (subdE w))).
Proof.
Move=> [u Hu]; Apply/set0Pn=> [[x]]; Move/andP=> [Du Hx]; Move: Du.
Rewrite: /preimage /= /embr_face.
Case: (pickP (erc1 (edge u))) => [y Hy | Hu'].
  Case/andP: Hy => [Hy _] Dx.
  By Rewrite: /setC -(embdd_inj (eqP Dx)) -(fclosed1 HidE) Hy in Hx.
Rewrite: (monic2F_eqd (Eface gm)) -embddN; Move=> Du.
Step Hnx: (setC embd_ring (node x)).
  Apply/idP=> [Hnx]; Move: (Hu' (node x)).
  By Rewrite: /erc1 Hnx (eqP Du) De2m set11.
Rewrite: -(embddE Hnx) in Du.
Case: (elimN set0Pn Hu); Exists (edge (node x)); Rewrite: /setI /preimage Du.
By Rewrite: /setC -(fclosed1 HidE) (negbE Hnx).
Qed.

Local redge [u : rdart] : rdart := (subdI (Hredge u)).
Local rnode [u : rdart] : rdart := (subdI (Hrnode u)).
Local rface [u : rdart] : rdart := (subdI (Hrface u)).

Remark Hemb_rem : (monic3 redge rnode rface).
Proof.
Move=> [u Hu]; Apply: subdE_inj; Rewrite: /= /embr_face De2m.
Case: (pickP (erc1 u)) => [y Hy | Hu']; Rewrite: /embr_node.
  Case/andP: Hy => [Hy Du].
  Case: (pickP (erc1 (embdd (edge y)))) => [z Hz | Hy'].
    Case/andP: Hz => [Hz Dey].
    By Rewrite: -(embdd_inj (eqP Dey)) Eedge -(eqP Du).
  By Move: (Hy' (edge y)); Rewrite: /erc1 set11 -(fclosed1 HidE) Hy.
Case: (pickP (erc1 (face (edge u)))) => [y Hy | _]; RightBy Apply Eedge.
Case/andP: Hy => [Hy Du]; Move: (negbI (Hu' (node y))).
Rewrite: /erc1 embddN -(eqP Du) Eedge set11 andbT; Move=> Hny.
Case/set0Pn: Hu; Exists (node y).
By Rewrite: /setI /preimage embddN -(eqP Du) Eedge set11.
Qed.

Definition emb_rem : hypermap := (Hypermap Hemb_rem).
Definition embr [u : emb_rem] : gm := (subdE u).

Lemma inj_embr : (injective embr). Proof. Exact (subdE_inj 2!?). Qed.

Lemma codom_embr : (codom embr) =1 rdom.
Proof.
Move=> z; Apply/set0Pn/idP=> [[[y Hy] Dy] | Hz]; LeftBy Rewrite: (eqP Dy).
Exists ((subdI Hz)::emb_rem); Exact (set11 ?).
Qed.

Definition embr_ring : (seq emb_rem) :=
   (preimage_seq embr (rev (maps embdd embd_ring))).

Lemma maps_embr_ring : (maps embr embr_ring) = (rev (maps embdd embd_ring)).
Proof.
Apply: maps_preimage => [u Hu]; Rewrite: codom_embr; Rewrite: mem_rev in Hu.
Case/mapsP: Hu => [x Hx Du]; Apply/set0Pn=> [[y]]; Move/andP=> [Dy Hy].
By Rewrite: (eqP Dy) in Du; Rewrite: /setC -(embdd_inj Du) Hx in Hy.
Qed.

Lemma ucycle_embr_ring : (ufcycle node embr_ring).
Proof.
Case: (andP scycle_embd_ring) => [Hrd]; Move/simple_uniq=> Urd.
Step Urdd: (uniq (maps embdd embd_ring)) By Rewrite (uniq_maps embdd_inj).
Step Ur : (uniq embr_ring).
  By Rewrite: -(uniq_maps inj_embr) maps_embr_ring uniq_rev.
Rewrite: /ucycle Ur andbT.
Apply: (cycle_from_next Ur) => [u Hu]; Apply/eqP; Apply inj_embr.
Rewrite: -(next_maps inj_embr Ur) maps_embr_ring (next_rev Urdd).
Rewrite: -(mem_maps inj_embr) maps_embr_ring mem_rev in Hu.
Rewrite: /= /embr_node -/(embr u); Case: (mapsP Hu) => [x Hx []] {u Hu}.
Case: (pickP (erc1 (embdd x))) => [y Hy | Hx'].
  Case/andP: Hy => [_ Dy]; Rewrite: (prev_maps embdd_inj Urd).
  Apply: (congr embdd (Iedge ? ?)); Rewrite: Eface -(embdd_inj (eqP Dy)).
  Apply: (esym (eqP ?)); Exact (prev_cycle Hrd Hx).
By Move: (Hx' x); Rewrite: /erc1 set11 Hx.
Qed.

Lemma emb_patch : (patch embdd embr embd_ring embr_ring).
Proof.
Split. Exact embdd_inj. Exact inj_embr.
Exact scycle_embd_ring. Exact ucycle_embr_ring. Exact maps_embr_ring.
Move=> u; Rewrite: /setU /setC codom_embr /rdom /setC.
  Case Hu: (codom embdd u).
    Rewrite: -(f_iinv Hu) (image_f embdd_inj) (mem_maps embdd_inj) /=.
    By Rewrite negb_elim.
  Apply: (introN set0Pn ?); Move=> [x H]; Case: {H}(andP H) => [Du _].
  By Case: (elimF set0Pn Hu); Exists x.
Exact embddE. Exact embddN. Done.
Move=> [u Hu]; Rewrite: /setC -(mem_maps inj_embr) maps_embr_ring /= mem_rev.
Move=> Hu'; Rewrite: /embr_node.
Case: (pickP (erc1 u)) => [x Hx | _]; RightBy Done.
By Case/andP: Hx => [Hx Du]; Rewrite: (eqP Du) (mem_maps embdd_inj) Hx in Hu'.
Qed.

Lemma planar_embr : (planar emb_rem).
Proof.
Move: (Hpgm); Rewrite: /planar (genus_patch emb_patch) addnC.
By Case (genus emb_rem).
Qed.

Lemma plain_embr : (plain emb_rem).
Proof. By Move: (HgmE); Rewrite: (plain_patch emb_patch); Case/andP. Qed.

Lemma cubic_embr : (quasicubic embr_ring).
Proof.
By Move: (Hgm :: (cubic ?)); Rewrite: (cubic_patch emb_patch); Case/andP.
Qed.

Syntactic Definition ccr := (maps embed cc).

Remark Ezh1: (p : (seq gc)) (insertE (maps h1 p)) = (maps h1 (insertE p)).
Proof. By Elim=> [|x p Hrec]; RightBy Rewrite: /= Hrec embedE. Qed.

Remark HccE: (x : gc) (insertE cc x) -> (insertE cc (edge x)).
Proof.
Move=> x; Elim: (cc) => [|y p Hrec] //=; Rewrite: /setU1.
Rewrite: -{3 y}De2c !(inj_eqd (Iedge gc)) !orbA (orbC y =d x).
By Case (orb (edge y) =d x y =d x); Simpl; Auto.
Qed.

Lemma embed_sparse : (sparse (insertE ccr)).
Proof.
Move: Hcc => [[H1 H2 _ _] _]; Move: H1 H2; Rewrite: disjoint_has has_sym.
Rewrite: /sparse !simple_recI Ezh1 /=; Elim: (insertE cc) => [|x p Hrec] //=.
Move/norP=> [Hix Hip]; Move/andP=> [Hx Hp].
Rewrite: ~{Hrec Hp}(Hrec Hip Hp) andbT /=.
Apply/hasP=> [[u]]; Case/mapsP=> [y Hy []] /= Hxy {u}; Case/hasP: Hx.
Exists y; Auto; Case/connectP: Hxy; Move=> q.
Elim: q x Hix => [|u q Hrec] x Hx /=.
  By Move=> _ Dy; Rewrite: (embed_inj Hx (hasPn Hip ? Hy) Dy) connect0.
Case/andP; Case/eqP; Rewrite: -(embedN Hx).
By Rewrite: /setC (fclosed1 HrcN) in Hx; Rewrite cnode1; Auto.
Qed.

Remark cface_ac_h1 : (x : gc) (ac x) ->
   (y : gc) (cface (h1 x) (h1 y)) = (cface x y).
Proof.
Move=> x Hx; Cut (y : gc) (bc y) -> (cface (h1 x) (h1 y)) = (cface x y).
  Move=> Hxbc y; Case Hy : (bc y) (edge_perimeter y); Auto.
  Rewrite: /= -{1 2 y}Eface De2c /setC -(fclosed1 HrcN); Move=> Hfy.
  By Rewrite: embedE (embedN Hfy) cface1r Enode (Hxbc ? Hfy) -cface1r.
Move=> y Hy; Rewrite: -codom_embd in Hy; Rewrite: -(f_iinv Hy).
Step Hxd: (bc x) By Exact (Hacbc Hx).
Rewrite: -codom_embd in Hxd; Rewrite: -(f_iinv Hxd) -cface_embd.
Symmetry; Apply: (patch_face_d emb_patch) {y Hy}.
Apply/set0Pn=> [[u]]; Case/andP; Rewrite: codom_embr; Move=> Hxu; Case/set0Pn.
Rewrite: /embdd f_iinv /embed Hx in Hxu.
Case: {Hxu}(cface_h_ac Hx Hxu) => [y Hxy []] {u}.
Rewrite: (closed_connect HacF Hxy) in Hx.
Step Hy: (bc y) By Exact (Hacbc Hx).
Rewrite: -codom_embd in Hy; Exists (iinv Hy).
Rewrite: /setI /preimage /embdd f_iinv /embed Hx set11 /= /setC.
Rewrite: -(mem_maps inj_embd) f_iinv maps_embd_ring -{1 y}Eface.
Rewrite: (mem_maps (Iedge gc)) -(fclosed1 HrcN).
Apply: (introN idP [Hfy](elimN hasP Hx ?)); Exists (face y); Auto.
Apply fconnect1.
Qed.

Remark cface_h1 : (x, y : gc) (cface x y) -> (cface (h1 x) (h1 y)).
Proof.
Cut (x, y : gc) (bc x) -> (cface x y) -> (cface (h1 x) (h1 y)).
  Move=> Hbc x y Hxy; Case Hx: (bc x); Auto; Case Hy: (bc y).
    By Rewrite Sface; Apply (Hbc y x Hy); Rewrite Sface.
  By Rewrite: (scycle_cface HUrc Hxy (negbEf Hx) (negbEf Hy)) connect0.
Cut (x, y : gc) (bc x) -> (bc y) -> (cface x y) -> (cface (h1 x) (h1 y)).
  Move=> Hbc x y Hx Hxy; Case Hy: (bc y) (edge_perimeter y); Auto.
  Rewrite: /= -{1 2 y}Eface De2c /setC -(fclosed1 HrcN); Move=> Hfy.
  Rewrite: embedE (embedN Hfy) cface1r Enode.
  By Apply Hbc; Rewrite: -?cface1r.
Move=> x y; Rewrite: -!codom_embd; Move=> Hx Hy.
Rewrite: -(f_iinv Hx) -(f_iinv Hy) -cface_embd.
Exact (patch_face_d' emb_patch 10!?).
Qed.

Remark adj_ac_h1 : (x, y : gc) (ac x) -> (ac y) ->
   (adj (h1 x) (h1 y)) = (adj x y).
Proof.
Move=> x y Hx Hy; Rewrite: /embed Hx Hy; Apply/adjP/adjP.
  Move=> [u Hxu Huy].
  Case/(cface_h_ac Hx): Hxu Huy => [z Hxz []] {u} Hzy; Exists z; Auto.
  Step Hz: (ac z) By Rewrite: -(closed_connect HacF Hxz).
  Rewrite: /rlink Sface in Hzy.
  Case/(cface_h_ac Hy): Hzy => [t Hyt Hzt].
  Step Ht: (ac t) By Rewrite: -(closed_connect HacF Hyt).
  By Case: (embed_full Hz Ht (esym Hzt)) Hyt; Rewrite Sface.
Move=> [z Hxz Hzy]; Step Hz: (ac z) By Rewrite: -(closed_connect HacF Hxz).
Rewrite: /rlink Sface in Hzy.
Step Hez: (ac (edge z)) By Rewrite: -(closed_connect HacF Hzy).
Exists (h z); LeftBy Exact (cface_ac_h Hx Hxz).
By Rewrite: /rlink Sface -(embed_functor Hz Hez) (cface_ac_h Hy Hzy).
Qed.

Remark orbitF_h1 : (x : gc) (ac x) ->
  (orbit face (h1 x)) = (maps h1 (orbit face x)).
Proof.
Move=> x Hx; Rewrite: /orbit -/(arity (h1 x)) {2}/embed Hx (HhFn Hx) -/(arity x).
Elim: {x}(arity x) {1 2 4}x Hx => //= [n Hrec] x Hx; Congr Adds.
Rewrite: (fclosed1 HacF) in Hx.
By Rewrite: -{1 x}Eface embedE (embedN (Hacbc Hx)) Enode Hrec.
Qed.

Lemma embed_valid_contract : (valid_contract seq0 ccr).
Proof.
Split; Try Exact embed_sparse; Rewrite: ?disjoint_has // size_maps ?Ezh1;
  Case: Hcc => [[Hrcc _ H3 H4] _] // H0; Case/set0Pn: {H3 H4 H0}(H4 H0) => [x].
Move/and3P=> [Hx Hx2 Hx4]; Rewrite: disjoint_has has_sym in Hrcc.
Apply/set0Pn; Exists (h1 x); Apply/and3P; Split; Try Done.
  Apply: (leq_trans Hx2) {Hx2 Hx4}; Rewrite: orbitF_h1 // /orbit.
  Elim: {x Hx}(arity x) {1 3}x => [|n Hrec] x //=.
  Move: {Hrec}(Hrec (face x)) => Hrec.
  Case Hccx: (fband (insertE cc) (edge x));
    Case Hcchx: (fband (maps h1 (insertE cc)) (edge (h1 x)));
    Rewrite: // ltnW //.
  Case: (elimF hasP Hcchx); Case: {Hcchx Hccx}(hasP Hccx) => [y Hy Hyx].
  By Exists (h1 y); [Apply maps_f | Rewrite: -embedE; Apply cface_h1].
Apply/idP=> [Hhx]; Case/subsetP: Hx4 {Hx2} => [] y Hy.
Step Hey: (insertE cc (edge y)) By Apply HccE.
Step Hhcc: (z : gc) (insertE cc z) -> (adj (h1 x) (h1 z)).
  By Move=> z Hz; Apply: (subsetP Hhx); Apply maps_f.
Step Hiey: (bc (edge y)) By Apply: (hasPn Hrcc).
Step Hhxn: (orb (cface x (node y)) (cface x (node (edge y)))).
  Rewrite: -!(cface_ac_h1 Hx) (embedN (hasPn Hrcc ? Hy)).
  Rewrite: (embedN Hiey) embedE -!mem_spoke_ring.
  By Apply adj11_edge; Auto; Rewrite: -embedE; Auto.
Case/orP: Hhxn => [Hxny | Hxney]; Apply/adjP.
  By Exists (node y); Rewrite: // /rlink cface1 Enode connect0.
Exists (edge (face y)); RightBy Rewrite: /rlink De2c -cface1 connect0.
By Rewrite: -{1 y}De2c -(Dn3c Hiey) cface1r !Enode.
Qed. 

Definition embed_cotrace : colseq -> Prop := (ring_trace (rotr (1) embr_ring)).

Lemma embed_closure : (kempe_closed embed_cotrace).
Proof.
Apply: kempe_map; Split; [Split | Exact planar_embr].
  Split; LeftBy Exact plain_embr.
  Apply/subsetP=> [w]; Rewrite: /setC mem_rotr; Exact (subsetP cubic_embr w).
Rewrite: ucycle_rotr; Exact ucycle_embr_ring.
Qed.

Lemma embed_contract : (EX et | (cc_ring_trace cc rrc et) & (embed_cotrace et)).
Proof.
Case: Hcc => [[Hrcc _ _ _] _]; Rewrite: disjoint_has has_sym in Hrcc.
Case: (contract_coloring Hgm embed_valid_contract) => [k [HkE HkF]].
Pose k' := [x](k (h1 x)); Exists (trace (maps k' rrc)).
  Exists k'; Split.
    Step HbcE: (x : gc) (bc x) -> (invariant edge k' x) = (insertE cc x).
      Move=> x Hx; Rewrite: /invariant /k' embedE; Apply: (etrans (HkE ?)).
      Rewrite: Ezh1; Apply/mapsP/idP; RightBy Exists x.
      By Move=> [y Hy Exy]; Rewrite: -(embed_inj (hasPn Hrcc ? Hy) Hx Exy).
    Move=> x; Case: (orP (edge_perimeter x)) => [Hx | Hex]; Auto.
    Rewrite: mem_insertE // (eq_has (cedge1 x)) -mem_insertE // -HbcE //.
    By Rewrite: /invariant De2c eqd_sym.
  Move=> x; Rewrite: /invariant /k'.
  By Rewrite: -(fconnect_invariant HkF (cface_h1 (fconnect1 face x))) set11.
Exists [w](k (embr w)).
  Split.
    Move=> [u Hu]; Rewrite: /invariant /eqdf /= {-1}/eqd /=.
    Apply: (etrans (HkE ?)); Rewrite: Ezh1.
    Apply/mapsP=> [[x Hx Ex]].
    Step Hxd: (codom embd x) By Rewrite: codom_embd; Apply: (hasPn Hrcc).
    Case/set0Pn: Hu; Exists (iinv Hxd); Rewrite: /setI /preimage /setC.
    Rewrite: -(mem_maps inj_embd) maps_embd_ring /embdd f_iinv Ex set11.
    Rewrite: -{x}De2c (mem_maps (Iedge gc)); Apply: (hasPn Hrcc).
    By Move: Hx; Rewrite: !mem_insertE // (eq_has (cedge1 x)).
  Move=> [u Hu]; Rewrite: /invariant /eqdf /= {-1}/eqd /setA /= /embr_face.
  Case: (pickP (erc1 (edge u))) => [[x Hx] Hxu | _]; RightBy Apply: HkF.
  Case/andP: Hxu; Rewrite: -(mem_maps inj_embd) maps_embd_ring /embdd /=.
  Rewrite: -{1 2 x}De2c (mem_maps (Iedge gc)) embedE (inj_eqd (Iedge gm)).
  Move=> Hiex Du; Rewrite: (eqP Du) /embd_edge /setC Hiex /=.
  Apply/eqP; Apply: (fconnect_invariant HkF); Apply: cface_h1.
  By Rewrite: cface1 Enode connect0.
Rewrite: (maps_comp k embed) (maps_comp k embr) !maps_rotr.
Rewrite: maps_embr_ring /embdd (maps_comp embed embd) maps_embd_ring.
Rewrite: /rrc !maps_rev -rev_rot; Congr trace; Congr rev.
Case: {}rc Hrc => //= [x p]; Rewrite: rot1_adds.
Elim: p {1 3}x => [|z p Hrec] y /=.
  Rewrite andbT; Case/eqP; Congr Adds.
  Apply: (fconnect_invariant HkF); Apply: cface_h1.
  By Rewrite: cface1r Enode connect0.
Case/andP=> [Dz Hp]; Congr Adds; Auto.
Case/eqP: Dz; Apply: (fconnect_invariant HkF); Apply: cface_h1.
By Rewrite: cface1r Enode connect0.
Qed.

Theorem not_embed_reducible : False.
Proof.
Move: {}embed_contract => [et Hetc Hetr].
Case: {et Hetc Hetr}(c_reducible_coclosure Hcc Hetc embed_closure Hetr).
Move=> et [kc [HkcE HkcF] Detc] [kr Hkr Detr].
Case: (minimal_counter_example_is_noncolorable Hgm).
Move: (colorable_patch emb_patch) => [_ H]; Apply: H{H}.
Exists (rev et);
   RightBy Rewrite: rev_rev Detr -trace_rot -!maps_rot rot_rotr; Exists kr.
Exists [u](kc (embd u)).
  Split.
    Move=> [x Hx]; Rewrite: /invariant {-1}/eqd /= /embd_edge.
    Case: (bc (edge x)); LeftBy Apply: HkcE.
    Rewrite: -(eqcP (HkcF (edge (node (edge x))))) Enode; Apply: HkcE.
  Move=> u; Apply/eqP; Apply: (fconnect_invariant HkcF).
  By Rewrite: -cface_embd -cface1 connect0.
Rewrite: (maps_comp kc embd) maps_embd_ring Detc /rrc maps_rev.
Rewrite: trace_rev rev_rot rev_rev; Symmetry; Apply: (monic_move (!rotr_rot ? ?)).
Rewrite: -trace_rot; Congr trace.
Case: {}rc (andP HUrc) => [|x p] [Hp _] //; Move: Hp.
Rewrite: /= rot1_adds; Elim: p {1 4}x => [|z p Hrec] y /=.
  Case/andP; Case/eqP; Clear; Congr Adds; Symmetry.
  Apply: eqP; Rewrite: -{1 y}Enode; Apply: HkcF.
Case/andP; Case/eqP; Move=> Hp; Congr Adds; Auto.
Symmetry; Apply: eqP; Rewrite: -{1 y}Enode; Apply: HkcF.
Qed.

End Embeddings.

Unset Implicit Arguments.
