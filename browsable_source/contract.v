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
Require walkup.
Require geometry.
Require color.
Require coloring.
Require patch.
Require snip.
Require revsnip.
Require birkhoff.

Set Implicit Arguments.

(* The proof that there exists a contract coloring for any valid contract. *)
(* We will show in embed.v that contract validity is lifted by the         *)
(* embedding, except for the ring condition, which becomes moot.           *)

Definition contract_ring [g : hypermap; cc, r : (seq g)] : Prop :=
  (and3 (scycle rlink r) (proper_ring r) (sub_set (behead r) (insertE cc))).

Section Contract.

Variable g : hypermap.
Hypothesis Hg: (minimal_counter_example g).

Local Hpg : (planar g) := Hg.
Local Hbg : (bridgeless g) := Hg.
Local HgE : (plain g) := Hg.
Local HgN : (cubic g) := Hg.
Local HgF : (pentagonal g) := Hg.
Local Hcg : (connected g) := Hg.
Local Hkg := (minimal_counter_example_is_noncolorable Hg).
Local Hmg := (minimal_counter_example_is_minimal Hg).
Local De2 := (plain_eq Hg).
Local He1 := (plain_neq Hg).
Local Dn3 := (cubic_eq Hg).
Local Hg' : (planar_bridgeless_plain_connected g) := Hg. (* revring assumption *)

Lemma sparse_contract_ring : (cc : (seq g)) (sparse (insertE cc)) ->
  (p : (seq g)) (contract_ring cc p) -> (nontrivial_ring (0) p).
Proof.
Intros cc Hcc; Rewrite: /sparse simple_recI /= in Hcc.
Step HccF: (p : (seq g)) (contract_ring cc p) -> ~ (diskF p) =1 set0.
  Move=> p; Elim: {p}(S (size p)) {-2}p (ltnSn (size p)) => // [n Hrec] p Hn.
  Move=> [Hp HpE Hpcc] HpF; Case Dp: p {}HpE => [|x [|x' p']] // _.
  Move: (negbI (HpF (node x))) (negbI (HpF (node (node x)))).
  Step Hpx: (diskN p x) By Rewrite: diskN_E /setU Dp /= setU11.
  Rewrite: /diskF /setD -!(fclosed1 (diskN_node p)) Hpx !andbT !negb_elim.
  Case: (andP Hp); Clear; Move/simple_uniq=> Up Hnx Hnnx.
  Case HnxE: (diskE p (node x)).
    Step Henx: (fband p (edge (node x))).
      Apply/hasP; Exists x; LeftBy Rewrite: Dp /= setU11.
      By Rewrite: -{2 x}Enode fconnect1.
    Rewrite: (fclosed1 (diskE_edge Hpg Hp)) in HnxE.
    Pose q := (chord_ring p (edge (node x))).
    Case: (fprojP Hnx) (fprojP Henx) => [Hpnx Hnxpnx] [Hpenx Hxpenx].
    Step Dpenx: (fproj p (edge (node x))) = x.
      Rewrite: cface1 Enode Sface in Hxpenx.
      By Apply (scycle_cface Hp Hxpenx Hpenx); Rewrite: Dp /= setU11.
    Case Hxpnx: ((fproj p (node x)) =d x).
      By Move: Hnxpnx; Rewrite: (eqP Hxpnx) -{2 x}Enode -cface1r (set0P Hbg). 
    Case Hxpnx': ((fproj p (node x)) =d x').
      Move: Hnxpnx; Rewrite: (eqP Hxpnx').
      Case: (andP Hp); Rewrite Dp; Move/andP=> [Dx' _] _.
      Rewrite: Sface -(same_cface Dx') -{(node x)}Enode -cface1r.
      By Rewrite: -{1 x}Dn3 cface1 Enode (set0P Hbg).
    Case: (cat_arc Up Hpenx Hpnx); LeftBy Rewrite: Dpenx eqd_sym Hxpnx.
    Rewrite: {4 fproj}lock Dpenx -lock -{2 (node x)}De2; Move=> i Eip.
    Apply (Hrec q).
        Rewrite: ltnS -(size_rot i) in Hn; Apply: (leq_trans ? Hn).
        Rewrite: -Eip size_cat {1 p}Dp {1}/arc /= set11 /= Hxpnx Hxpnx'.
        By Rewrite: /= !addSnnS leq_addl.
      Split; Try By Apply: scycle_chord_ring; Rewrite: ?De2.
        By Apply: (proper_chord_ring Hg ?); Rewrite: ?De2.
      Move=> y Hy; Simpl in Hy; Apply Hpcc.
      Step Hpy: (p y) By Rewrite: -(mem_rot i) -Eip mem_cat /setU Hy orbT.
      Move: Hpy; Rewrite: Dp /= /setU1; Case: (x =P y) => // [Dy].
      Rewrite: -(uniq_rot i) -Eip uniq_cat in Up.
      Case/and3P: Up; Clear; Case/hasP; Exists y; LeftDone.
      By Rewrite: {1 p}Dp /arc /= set11 /= Hxpnx /= -Dy setU11.
    By Move=> y; Rewrite: /q diskF_chord_ring ?De2 // /setD HpF andbF.
  Step Hpnx: (p (node x)).
    Rewrite: /diskE /setD -(fclosed1 (diskN_node p)) Hpx andbT in HnxE.
    Exact (negbEf HnxE).
  Case HnnxE: (diskE p (node (node x))).
    Step Hennx: (fband p (edge (node (node x)))).
      Apply/hasP; Exists (node x); LeftDone.
      By Rewrite: -{2 (node x)}Enode fconnect1.
    Pose q := (chord_ring p (edge (node (node x)))).
    Case: (fprojP Hnnx) (fprojP Hennx) => [Hpnnx Hnnxpnnx] [Hpennx Hnxpennx].
    Step Dpennx: (fproj p (edge (node (node x)))) = (node x).
      Rewrite: cface1 Enode Sface in Hnxpennx.
      By Apply (scycle_cface Hp Hnxpennx Hpennx Hpnx).
    Step Ep': (last x' p') = (node x).
      Apply: (monic_inj 1!g (prev_next Up) ?).
      Rewrite: -(next_rotr (1) Up) {1 p}Dp lastI rotr1_add_last /= set11.
      Apply (scycle_cface Hp); Rewrite: ?mem_next //;
        RightBy Rewrite: Dp /= setU11.
      Case/andP: Hp => [Hp _]; Rewrite: Sface -(same_cface (next_cycle Hp Hpnx)).
      By Rewrite: -{2 x}Enode fconnect1.
    Case Hpnnxnx: ((fproj p (node (node x))) =d (node x)).
      Move: Hnnxpnnx; Rewrite: (eqP Hpnnxnx) -{2 (node x)}Enode.
      By Rewrite: -cface1r (set0P Hbg). 
    Case Hpnnxx: ((fproj p (node (node x))) =d x).
      Move: Hnnxpnnx; Rewrite: (eqP Hpnnxx) -{(node (node x))}Enode Dn3.
      By Rewrite: Sface -cface1r (set0P Hbg).
    Case: (cat_arc Up Hpennx Hpnnx).
      By Rewrite: Dpennx eqd_sym Hpnnxnx.
    Rewrite: {4 fproj}lock Dpennx -lock -{1 p}(rot_rotr (1)).
    Rewrite: arc_rot ?uniq_rotr ?mem_rotr //.
    Rewrite: {1 p}Dp lastI rotr1_add_last {1}/arc /= Ep' set11 /= Hpnnxnx Hpnnxx.
    Rewrite: -{2 (node (node x))}De2; Move=> i Eip.
    Apply (Hrec q).
        Rewrite: ltnS -(size_rot i) in Hn; Apply: (leq_trans ? Hn).
        By Rewrite: -Eip size_cat /= !addSnnS leq_addl.
      Split; Rewrite: /q.
          By Apply: scycle_chord_ring; Rewrite: ?De2.
        Apply: (proper_chord_ring Hg ?); Rewrite: ?De2 //.
        By Rewrite: -(fclosed1 (diskE_edge Hpg Hp)).
      Move=> y Hy; Simpl in Hy; Apply Hpcc.
      Step Hpy: (p y) By Rewrite: -(mem_rot i) -Eip mem_cat /setU Hy orbT.
      Move: Hpy; Rewrite: Dp /= /setU1; Case: (x =P y) => // [Dy].
      Rewrite: -(uniq_rot i) -Eip uniq_cat in Up.
      Case/and3P: Up; Clear; Case/hasP; Exists y; LeftDone.
      By Rewrite: -Dy /= setU1r ?setU11.
    Move=> y; Rewrite: /q diskF_chord_ring ?De2 //.
      By Rewrite: /setD HpF andbF.
    By Rewrite: -(fclosed1 (diskE_edge Hpg Hp)). 
  Def: Hnxx := (cubic_neq HgN x).
  Step Hccnx: (insertE cc (node x)).
    Rewrite: Dp /= /setU1 eqd_sym Hnxx in Hpnx.
    By Apply Hpcc; Rewrite Dp.
  Step Hccnnx: (insertE cc (node (node x))).
    Rewrite: /diskE /setD -!(fclosed1 (diskN_node p)) Hpx andbT in HnnxE.
    Rewrite: Dp /= /setU1 -(monic2F_eqd 3![y](node (node y)) Dn3) in HnnxE.
    By Rewrite Hnxx in HnnxE; Apply Hpcc; Apply negbEf; Rewrite Dp.
  Clear: Hrec Hn Hp HpE Hpcc HpF x' p' Dp Hpx Up Hnx Hnnx HnxE Hpnx HnnxE.
  Elim: {n p}cc Hcc Hccnx Hccnnx => [|y cc Hrec] //=.
  Rewrite: /setU1; Case/and3P; Move/norP => [_ Hy] Hey Hcc.
  Case: (y =P (node x)) => [Dy | _].
    Case: ((edge y) =P (node (node x))) => [Dey | _] _.
      Clear; Move: (set0P Hbg x).
      By Rewrite: 2!cface1r -{2 x}Dn3 -Dey Dy !Enode connect0.
    Rewrite: Dy (inj_eqd (Inode g)) eqd_sym Hnxx.
    Move=> Hnnx; Case/hasP: Hy; Exists (node (node x)); Auto.
    By Rewrite: Dy fconnect1.
  Case: ((edge y) =P (node x)) => [Dey | _].
    Case: (y =P (node (node x))) => [Dy | _] _.
      Clear; Move: (set0P Hbg x).
      By Rewrite: 2!cface1r -{2 x}Dn3 -Dy -{1 y}De2 Dey !Enode connect0.
    Rewrite: Dey (inj_eqd (Inode g)) eqd_sym Hnxx.
    Move=> Hnnx; Case/hasP: Hey; Exists (node (node x)); Auto.
    By Rewrite: Dey fconnect1.
  Simpl; Case: (y =P (node (node x))) => [Dy | _] Hnx.
    By Case/hasP: Hy; Exists (node x); Rewrite: //= Dy Snode fconnect1.
  Case: ((edge y) =P (node (node x))) => [Dey | _]; EAuto.
  By Case/hasP: Hey; Exists (node x); Rewrite: //= Dey Snode fconnect1.
Move=> p Hpcc; Apply/(nontrivial0P p); Split.
  Exact (set0Pn (introN set0P (HccF p Hpcc))).
Case: Hpcc => [HUp HpE Hpcc].
Step HUp1: (scycle rlink (rot (1) p)) By Rewrite: scycle_rot.
Case: [H](set0Pn (introN set0P (HccF (rev_ring (rot (1) p)) H))).
  Split; Try By Apply: scycle_rev_ring.
    By Rewrite: proper_rev_ring // proper_ring_rot.
  Move=> y Hy; Step Hccey: (insertE cc (edge y)).
    Apply Hpcc; Case: (p) Hy => [|x p'] //=.
    Rewrite: rot1_adds /rev_ring -maps_rev rev_add_last /= -{1 y}De2.
    By Rewrite: (mem_maps (Iedge g)) mem_rev.
  By Move: Hccey; Rewrite: !mem_insertE // -(eq_has (cedge1 y)).
Move=> y; Rewrite: diskF_rev_ring ?proper_ring_rot //.
Move=> H; Exists y; Apply: etrans H.
Rewrite: /diskFC /setD /diskN /setC /fband.
Rewrite:  -!disjoint_has !(eq_disjoint (mem_rot (1) p)) !(disjoint_sym p).
Congr andb; Apply: eq_disjoint => [y']; Apply: eq_connect => [z z'].
By Rewrite: /dlink mem_rot.
Qed.

Remark contract_ring_max : (cc, p : (seq g))
  (contract_ring cc p) -> (leq (size p) (S (size cc))).
Proof.
Move=> cc p [Hp Hpr Hpcc].
Pose df := [x](setI cc (set2 x (edge x))).
Step Hf: (x : g) (behead p x) -> ~ (df x) =1 set0.
  Move=> x H Hccx; Move: {H}(Hpcc ? H) => Hx.
  Rewrite: mem_insertE // in Hx; Case/hasP: Hx => [y Hy Hxy].
  By Rewrite: plain_orbit // mem_seq2 in Hxy; Case/andP: (Hccx y); Split.
Pose f := [u : (subFin (behead p))]
   let (x, Hx) = u in
   if (pickP (df x)) then [y; _]y else
   [Hx']Cases (Hf ? Hx Hx') of end.
Step Uf: (injective f).
  Move=> [x Hx] [y Hy]; Simpl.
  Case: (pickP (df x)) => [x' Hx' | H]; RightBy Case (Hf ? Hx H).
  Case: (pickP (df y)) => [y' Hy' | H]; RightBy Case (Hf ? Hy H).
  Move=> H; Case: H {Hx' Hy'}(andP Hx') (andP Hy') => [ ] [_ Dx] [_ Dy]. 
  Apply: (subdE_inj ?); Simpl.
  Move: {Hx Hy}(mem_behead Hx) (mem_behead Hy) => Hx Hy.
  Case/orP: Dx; Move/eqP=> Dx'; Rewrite: -Dx' in Dy.
    Case/orP: Dy => [Dy | Dy]; LeftBy Exact (esym (eqP Dy)).
    Case: (elimF idP (diskN_edge_ring Hg Hp Hpr Hy)).
    By Rewrite: (eqP Dy) diskN_E /setU Hx.
  Case/orP: Dy => [Dy | Dy]; RightBy Exact (Iedge ? (esym (eqP Dy))).
  Case: (elimF idP (diskN_edge_ring Hg Hp Hpr Hx)).
  By Rewrite: -(eqP Dy) diskN_E /setU Hy.
Step Up: (uniq (behead p)).
  Case: {}p (andP Hp) => [|x p'] [_ Up]; LeftDone.
  By Case (andP (simple_uniq Up)).
Rewrite: -add1n -leq_sub_add subn1 -size_behead -(card_uniqP Up).
Rewrite: -card_sub_dom -(card_image Uf).
Apply: (leq_trans (subset_leq_card ?) (card_size ?)).
Apply/subsetP=> [y]; Case/set0Pn=> [[x Hx]] /=; Case/andP.
Move/eqP=> H _; Rewrite: ~H /=.
By Case: (pickP (df x)) => [x' Hx' | H]; [Case (andP Hx') | Case (Hf ? Hx H)].
Qed.

Lemma contract3_valid : (cc : (seq g))
    (sparse (insertE cc)) ->
    (leq (size cc) (3)) -> 
  (p : (seq g)) ~(contract_ring cc p).
Proof.
Move=> cc HccN Hcc p Hpcc; Case: {}Hpcc => [Hp _ _].
Step Hpn: (leq (size p) (4)) By Apply: (leq_trans (contract_ring_max Hpcc) ?).
Rewrite: -ltnS ltn_neqAle in Hpn; Case/andP: Hpn => [Ep5 Hp5].
Case/idP: (birkhoff Hg Hp5 Hp); Rewrite: (negbE Ep5). 
By Apply (sparse_contract_ring HccN).
Qed.

Lemma triad_valid : (cc : (seq g); x0 : g)
    (sparse (insertE cc)) ->
    (size cc) =d (4) -> (triad (insertE cc) x0) ->
  (p : (seq g)) ~(contract_ring cc p).
Proof.
Move=> cc x0 HccN Hcc Hx0 p Hpcc.
Step Hp5: (leq (size p) (5)).
  By Rewrite: -(eqP Hcc); Exact (contract_ring_max Hpcc).
Case: Hpcc (sparse_contract_ring HccN Hpcc) => [Hp HprE Hpcc] Hpr.
Move: (birkhoff Hg Hp5 Hp).
Case Ep5: (size p) =d (5); [Move=> Hpr' | By Rewrite: /= Hpr].
Step [y0 Hy0p]: (EX y0 | (sub_set (adj y0) (fband p))).
  Case: (pickP [y](subset (adj y) (fband p))) => [y Hy | Hp''].
    By Exists y; Exact (subsetP Hy).
  Case/(nontrivial0P ?): Hpr => [[y0 Hy0] [y1 Hy1]].
  Case/(nontrivial1P ?): Hpr'; Split.
    Exists y0; [Done | Case/set0Pn: (Hp'' y0) => [y]; Case/andP].
    Move/adjP=>[y' Hy0y' Hy'y] Hpy; Rewrite: /rlink cface1 in Hy'y.
    Exists (face (edge y')).
      Rewrite: /diskF /setD (closed_connect (fbandF p) Hy'y) (negbE Hpy).
      Rewrite: (fclosed1 (diskN_node p)) Eedge.
      By Rewrite: (closed_connect (diskF_face p) Hy0y') in Hy0; Case/andP: Hy0.
    By Rewrite: (same_cface Hy0y') -cface1r (set0P Hbg).
  Exists y1; [Done | Case/set0Pn: (Hp'' y1) => [y]; Case/andP].
  Move/adjP=> [y' Hy1y' Hy'y] Hpy; Rewrite: /rlink cface1 in Hy'y.
  Exists (face (edge y')).
    Rewrite: /diskFC /setD (closed_connect (fbandF p) Hy'y) (negbE Hpy).
    Rewrite: /setC (fclosed1 (diskN_node p)) Eedge.
    By Rewrite: (closed_connect (diskFC_face p) Hy1y') in Hy1; Case/andP: Hy1.
  By Rewrite: (same_cface Hy1y') -cface1r (set0P Hbg).
Step Hpy0: (sub_set (fband p) (adj y0)).
  Move=> x Hx; Apply/idPn=> [Hy0x].
  Move: (HgF y0); Rewrite: -size_spoke_ring.
  Move: (scycle_spoke_ring Hg y0) => HUy0.
  Rewrite: -(eqP Ep5) leqNgt; Case/idP.
  Rewrite: -(scycle_fcard_fband Hp) -(scycle_fcard_fband HUy0).
  Rewrite: {2}/n_comp (cardD1 (froot face x)) {1}/setI (roots_root (Sface g)).
  Rewrite: -(closed_connect (fbandF p) (connect_root ? x)) Hx.
  Apply: subset_leq_card; Apply/subsetP=> [y]; Move/andP=> [Hy Hy0y].
  Rewrite: fband_spoke_ring in Hy0y.
  Rewrite: /setI /setD1 Hy (Hy0p ? Hy0y) -(eqP Hy).
  By Rewrite: (sameP eqP (rootPx (Sface g) x y)) (no_adj_adj Hy0x Hy0y).
Case: (pickP (setD (insertE cc) (fband p))) => [z Hz | Hccp].
  Case/andP: Hz => [Hpz Hccz]; Rewrite: mem_insertE // in Hccz.
  Move/hasP: Hccz => [z' Hz' Hzz']; Case/rot_to: Hz' => [i cc' Dcc].
  Rewrite: -(size_rot i) Dcc /= eqdSS in Hcc.
  Rewrite: eqn_leq Hp5 ltnNge -(eqP Hcc) in Ep5; Case/idP: Ep5.
  Apply: contract_ring_max; Split; Auto.
  Move=> t Ht; Move/mem_behead: Ht (Hpcc ? Ht) => Ht.
  Rewrite: !mem_insertE // -(has_rot i) Dcc /=; Case/orP=> //.
  Rewrite: Sedge -(same_cedge Hzz') plain_orbit // mem_seq2.
  Case/orP; Move/eqP=> Dt; Case/hasP: Hpz.
    By Exists t; RightBy Rewrite: Dt connect0.
  Exists (next p t); LeftBy Rewrite: mem_next.
  By Rewrite: -{z}De2 Dt; Case/andP: Hp => [Hp _]; Apply: (next_cycle Hp).
Case Hxy0: (cface x0 y0); Case/andP: Hx0.
  Clear; Case/subsetP=> [x Hx]; Rewrite: (adjF Hxy0); Apply Hpy0.
  By Apply negbEf; Move: (Hccp x); Rewrite: /setD Hx andbT.
Rewrite: ltnNge; Case/idP.
Apply: (leq_trans ? (fcard_adj_max Hg (negbI Hxy0))).
Pose acc := (fband (insertE cc)).
Apply: (!leq_trans (count acc (spoke_ring x0))).
  Rewrite: /spoke_ring leq_eqVlt; Apply/setU1P; Left.
  Elim: (orbit face x0) => [|z q Hrec] //=.
  Rewrite: rev_adds -cats1 maps_cat count_cat -~Hrec addnC; Congr addn.
  By Rewrite: /= /spoke -(fclosed1 (fbandF (insertE cc))) addn0.
Rewrite: count_filter -simple_fcard_fband.
  Apply: subset_leq_card; Apply/subsetP=> [z]; Rewrite: /setI.
  Case: (froots face z) => //; Case/hasP=> [t]; Rewrite: mem_filter /=.
  Move/andP=> [Ht Hx0t] Hzt; Apply/andP; Split.
    Case/hasP: Ht => [t' Ht' Htt']; Rewrite: (adjFr Hzt) (adjFr Htt').
    Move: (Hccp t'); Rewrite: /setD Ht' andbT; Move/idP; Auto.
  By Rewrite: -fband_spoke_ring; Apply/hasP; Exists t.
Case/andP: (scycle_spoke_ring Hg x0); Clear.
Rewrite: !simple_recI; Elim: (spoke_ring x0) => [|z q Hrec] //=.
Move/andP=> [Hz Hq]; Case: (acc z) => /=; Auto; Apply/andP; Split; Auto.
Apply/hasP=> [[t Ht Hzt]]; Case/hasP: Hz; Exists t; RightDone.
By Rewrite: mem_filter in Ht; Case/andP: Ht.
Qed.

Theorem contract_coloring : (r, cc : (seq g))
  (valid_contract r cc) -> (cc_colorable cc).
Proof.
Move=> r cc [_ HccN Hcc4 HccT].
Step Hccg: (ltn (0) (ltn (0) (size cc))) By Case: (size cc) Hcc4. 
Rewrite: -(leq_add2r (card g)) add1n in Hccg.
Step Hccp: (p : (seq g)) ~(contract_ring cc p).
  Case/or4P: Hcc4 => [Dcc]; Try By Apply (contract3_valid HccN); Case/eqP: Dcc.
  Rewrite: eqd_sym in Dcc; Case/set0Pn: (HccT (eqP Dcc)) => [x0].
  Move/andP=> [_ Hx0]; Exact (triad_valid HccN Dcc Hx0).
Move: {2}(size cc) (leqnn (size cc)) Hccg Hccp {r HccN HccT Hkg Hcg} => n.
Move: {-2}(card g) Hmg (Hg :: (planar_bridgeless_plain_precubic g)) => ng Hng.
Elim: n {}g cc {Hcc4 HccN HccT} => [|n Hrec] g0 [|x cc] Hg0  //=.
    By Move=> _ Hng0 _; Case: (Hng ? Hg0 Hng0)=> [k Hk]; Exists k.
  Clear; Exact (Hrec g0 seq0 Hg0 (leq0n n)).
Rewrite: /= add1n !ltnS; Move=> Hn Hng0 Hcc.
Def: Hg0E : (plain g0) := Hg0; Def: De20 := (plain_eq Hg0).
Def: Hbg0 := (bridgeless_cface Hg0).
Step EcEx: (y : g0) (cedge x y) = (orb x =d y (edge x) =d y).
  By Move=> y; Rewrite: (plain_orbit Hg0) mem_seq2.
Pose g1 := (walkupF x); Pose h1 := [u : g1]((subdE u) :: g0).
Step Hh1 : (injective h1) By Exact (subdE_inj 2!?).
Step Hex : (setC1 x (edge x)) By Rewrite: /setC1 eqd_sym (plain_neq Hg0).
Pose uex := ((subdI Hex) :: g1).
Pose g2 := (walkupF uex); Pose h2 := [w : g2]((subdE w) :: g1).
Step Hh2 : (injective h2) By Exact (subdE_inj 2!?).
Pose h := [w](h1 (h2 w)); Step Hh : (injective h) By Exact (inj_comp Hh1 Hh2).
Step Eh : (codom h) =1 [y](negb (cedge x y)).
  Move=> y; Rewrite: EcEx; Apply/set0Pn/norP=> [[w Dy] | [Hxy Hexy]].
    Rewrite (eqP Dy); Split; [Exact (subd_mem (h2 w)) | Exact (subd_mem w)].
  Exists (!subdI g1 (setC1 uex) (subdI 2!(setC1 x) Hxy) Hexy); Exact (set11 y).
Step HcEh: (w' : g2) (cedge x (h w')) = false.
  By Move=> w'; Apply negbE; Rewrite: -Eh codom_f.
Step HhN : (w, w' : g2) (cnode w w') = (cnode (h w) (h w')).
  Move=> *; Apply: (etrans (fconnect_skip (Iface ?) ? ?)); Apply: fconnect_skip.
Step HhE : (w, w' : g2) (cedge w w') = (cedge (h w) (h w')).
  Move=> *; Apply: (etrans (fconnect_skip (Inode ?) ? ?)); Apply: fconnect_skip.
Step HhE1 : (w : g2) (h (edge w)) = (edge (h w)).
  Move=> w; Step Hew: (codom h (edge (h w))).
    By Rewrite: Eh -cedge1r -Eh codom_f.
  Rewrite: -(f_iinv Hew); Apply: (congr h (esym ?)).
  Do 2 Apply: (subdE_skip (Inode ?)); Exact (f_iinv Hew).
Pose cfx := [y](has (cface y) (seq2 x (edge x))).
Step HhF : (w, w' : g2)
   (cface w w') = (if (cfx (h w)) then (cfx (h w')) else (cface (h w) (h w'))).
  Move=> w w'; Transitivity (cface (h2 w) (h2 w')).
    Apply: etrans (fconnect_skip (Iedge ?) w w').
    Apply: (eq_fconnect (glink_fp_skip_edge ?)).
    By Rewrite: /glink /relU /setU /eqdf /eqd /= /skip1 /= De20 !set11 /= orbT.
  Case Hw: (cfx (h w)).
    By Apply: cskip_edge_merge; [Rewrite: /cross_edge /= Hbg0 | Exact Hw].
  By Apply: (same_cskip_edge (negbI ?)).
Step De22: (w : g2) (edge (edge w)) = w.
  By Move=> w; Apply Hh; Rewrite: !HhE1 De20.
Step Hg2E: (plain g2).
  By Apply/plainP=> [w _]; Split; Rewrite: // -(inj_eqd Hh) HhE1 plain_neq.
Step Hg2: (planar_bridgeless_plain_precubic g2).
  Repeat Split; Auto; Try Exact (planar_walkupF ? (planar_walkupF ? Hg0)).
    Apply/set0Pn=> [[w Hw]].
    Step [y Hy Hwy]: (EX y | (cedge x y) & (cycle rlink (seq2 (h w) y))).
      Move: Hw; Rewrite: HhF HhE1 /= Hbg0.
      Case Hwx: (cfx (h w)); [Move: Hwx; Rewrite: /cfx /= /setU1 !orbF | Done].
      Case/orP=> [Hw | Hw].
        Rewrite: Sface -(same_cface Hw) Hbg0 /=.
        Move=> Hew; Exists (edge x); LeftBy Apply fconnect1.
        By Rewrite: /= /rlink Hew De20 Sface Hw.
      Rewrite: orbC Sface -(same_cface Hw) Hbg0 /=.
      Move=> Hew; Exists x; LeftBy Apply connect0.
     By Rewrite: /= /rlink Hew Sface Hw.
    Case (Hcc (seq2 (h w) y)); Split.
        Rewrite: /scycle Hwy simple_recI /=.
        Case/andP: Hwy => [Hewy _].
        By Rewrite: Sface -(same_cface Hewy) Sface Hbg0.
      By Apply/eqP=> [Dy]; Move: (codom_f h w); Rewrite: Eh cedge1r Dy Hy.
    By Move=> y'; Rewrite: /= /setU1 orbF orbA -EcEx; Case/eqP; Rewrite Hy.
  Apply/subsetP=> [w _]; Apply: leq_trans (precubic_leq Hg0 (h w)).
  Rewrite: /order -(card_image Hh); Apply subset_leq_card; Apply/subsetP=> [y].
  By Case/set0Pn=> [w']; Move/andP=> [Dy Hww']; Rewrite: (eqP Dy) -HhN.
Pose cc1 := (filter (setC (cedge x)) cc).
Step Ecc1 : cc1 =1 (setD cc (cedge x)) By Exact (mem_filter ? ?).
Step Ezcc1 : (insertE (Adds x cc)) =1 (setU (cedge x) (insertE cc1)).
  Move=> y; Rewrite: /= /setU1 orbA -EcEx /setU !mem_insertE //.
  Rewrite: !(eq_has (plain_orbit Hg0 y)) !(has_sym (seq2 y (edge y))) /= !orbF.
  By Rewrite: !Ecc1 /setD -cedge1r; Case (cedge x y).
Pose cc2 := (preimage_seq h cc1).
Step Ecc2 : (maps h cc2) = cc1.
  Apply: (maps_preimage [y; Hy]?); Rewrite: Eh.
  By Rewrite Ecc1 in Hy; Case: (andP Hy).
Step Ezcc2: (w' : g2) (insertE cc1 (h w')) = (insertE cc2 w').
  Move=> w'; Rewrite: !mem_insertE // -Ecc2 has_maps -(eq_has 2!(cedge w')) //.
  By Move=> w''; Rewrite HhE.
Step Hscc2: (leq (size cc2) (size cc)).
  Rewrite: -(count_setC (cedge x) cc) addnC count_filter -/cc1 -Ecc2 size_maps.
  By Rewrite leq_addr.
Case: {Hrec}(Hrec g2 cc2 Hg2 (leq_trans Hscc2 Hn)).
    Step [ ]: (pred (pred (card g0))) = (card g2).
      Symmetry; Apply: (etrans (card_walkup ?)); Congr pred; Apply: card_walkup.
    Case (ltn (0) (size cc2)).
      Rewrite: /= add1n ltnS; Apply: (leq_trans ? Hng0).
      By Rewrite: -!subn1 subn_sub leq_subr.
    Apply: (leq_trans ? Hng0).
    By Rewrite: (cardD1 x) /= add1n ltnS -subn1 leq_subr.
  Move=> [|w p] [HUp Hp2 Hpcc] //.
  Case: (andP HUp) => [Hp UpF]; Def: Up := (simple_uniq UpF).
  Step Uhp: (simple (maps h (Adds w p))).
    Elim: (Adds w p) UpF => [|w1 q Hrec] //.
    Rewrite: maps_adds !simple_adds.
    Move/andP=> [Hw1 Uq]; Rewrite: andbC ~Hrec //.
    Apply/hasP=> [[hw2]]; Case/mapsP=> [w2 Hw2 []] {hw2} Hw12.
    Case/hasP: Hw1; Exists w2; Rewrite: // Sface HhF.
    Case Hxw2: (cfx (h w2)); RightBy Rewrite Sface.
    By Rewrite: /cfx (eq_has (same_cface Hw12)).
  Step Hhpcc: (sub_set (maps h p) (insertE cc)).
    Move=> y; Case/mapsP=> [w' Hw' []] {y}.
    Move: (Ezcc1 (h w')); Rewrite: /setU /= /setU1 orbA -EcEx Ezcc2.
    By Rewrite: HcEh (Hpcc ? Hw').
  Case HUhp: (scycleb rlink (maps h (Adds w p))).
    Case (Hcc (maps h (Adds w p))); Split; Auto.
      By Case: {}p Hp2 => [|w' [|w'' p']]; Rewrite: // /= -HhE1 (inj_eqd Hh).
    By Move=> y Hy; Rewrite: /= /setU1 (Hhpcc ? Hy) !orbT.
  Step Hw1: (has [w1](negb (rlink (h (prev (Adds w p) w1)) (h w1))) (Adds w p)).
    Apply/hasPn=> [Hhp]; Case/andP: HUhp; Split; Auto.
    Apply cycle_from_prev; LeftBy Apply simple_uniq.
    Move=> y1; Case/mapsP=> [w1 Hw1 []] {y1}.
    Move: (Hhp w1); Rewrite: (prev_maps Hh Up) Hw1 negb_elim; Auto.
  Case/hasP: Hw1 => [w1 Hw1 Hw1p].
  Step Hcfxw1: (cfx (h w1)).
    Apply/idPn=> [Hcfxw1]; Case/idP: Hw1p; Move: (prev_cycle Hp Hw1).
    By Rewrite: {1}/rlink Sface HhF HhE1 (negbE Hcfxw1) Sface.
  Move: {}Hcfxw1; Rewrite: {1}/cfx; Move/hasP=> [x1 Hx1 Hw1x1].
  Case: (rot_to Hw1) Hp {}Up => [i1 p1 Dp1].
  Rewrite: -(cycle_rot i1) -(uniq_rot i1) Dp1 (cycle_path w1) /=.
  Move/andP=> [Ep1 Hp1]; Move/andP=> [Uw1 _].
  Rewrite: /rlink Sface HhF HhE1 Hcfxw1 /cfx in Ep1.
  Case/hasP: Ep1 => [x2 Hx2 Ep1].
  Step Hp1x: (negb (has [w2](cfx (h w2)) p1)).
    Apply/hasP=> [[w2 Hw2 Hw2x]]; Case/idP: Uw1.
    Step Hw12: (cface w1 w2) By Rewrite: HhF Hcfxw1.
    By Rewrite: (scycle_cface HUp Hw12 Hw1) // -(mem_rot i1) Dp1 /= setU1r.
  Step Ex12: (edge x2) = x1.
    Step Ex12: (cedge x2 x1).
      Rewrite: -plain_orbit // in Hx2.
      By Rewrite: -(same_cedge Hx2) plain_orbit.
    Rewrite: plain_orbit // mem_seq2 in Ex12.
    Case/orP: Ex12; Move/eqP=> Dx1; RightDone.
    Step Ew1p: (negb (rlink (h (last w1 p1)) (h w1))).
      Move: Hw1p; Rewrite: -(prev_rot i1 Up) -(prev_rotr (1)) ?uniq_rot // Dp1.
      By Rewrite: lastI rotr1_add_last; Case p1; Rewrite: /= set11.
    By Case/idP: Ew1p; Rewrite: /rlink (same_cface Ep1) Dx1 Sface.
  Pose q1 := (Adds x2 (maps h (Adds w1 p1))).
  Step Hq1 : (cycle rlink q1).
    Rewrite: (cycle_path x) /= {1 2}/rlink Ex12 (Sface g0 x1) last_maps.
    Apply/and3P; Split; Auto.
    Clear: i1 Dp1 Uw1 Ep Hw1 Hw1p Hcfxw1 Hw1x1 Ep1 q1.
    Elim: p1 w1 Hp1x Hp1 => [|w2 q Hrec] w1 //=.
    Move/norP=> [Hw2x Hqx]; Move/andP=> [Hw12 Hq].
    Apply/andP; Split; RightBy Exact (Hrec ? Hqx Hq).
    By Move: Hw12; Rewrite: {1}/rlink Sface HhF HhE1 (negbE Hw2x) Sface.
  Step Hq1w: (q1 (h w)).
    By Rewrite: /q1 -Dp1 /= /setU1 (mem_maps Hh) mem_rot /= setU11 orbT.
  Case: (rot_to Hq1w) => [i2 q2 Dq2].
  Step HUq2: (scycle rlink (Adds (h w) q2)).
    Rewrite: -Dq2 /scycle cycle_rot Hq1 /= simple_rot /q1 simple_adds.
    Apply/andP; Split; RightBy Rewrite: -Dp1 /= maps_rot simple_rot.
    Apply/hasP=> [[x3]]; Case/mapsP=> [w3 Hw3 []] {x3} Hw3x2.
    Simpl in Hw3; Case/setU1P: Hw3 => [Dw3 | Hw3].
      By Rewrite: Dw3 -(same_cface Hw3x2) -Ex12 Hbg0 in Hw1x1.
    Case/hasP: Hp1x; Exists w3; LeftDone.
    By Apply/hasP; Exists x2; RightBy Rewrite Sface.
  Case (Hcc (Adds (h w) q2)); Split; Auto.
    Rewrite: -Dq2 proper_ring_rot // /q1.
    By Move: Hp2; Rewrite: -(proper_ring_rot i1) // Dp1; Case p1.
  Move=> y Hy; Rewrite: /= /setU1 orbA.
  Move: (mem_behead Hy); Rewrite: -Dq2 mem_rot /q1 -Dp1 /=.
  Move/setU1P=> [Dy | Hyp].
    By Rewrite: Dy mem_seq2 /set2 in Hx2; Rewrite Hx2.
  Case/mapsP: Hyp => [w' Hw' Dy]; Rewrite: mem_rot /= in Hw'.
  Case/setU1P: Hw' => [Dw' | Hw'].
    Case/andP: HUq2; Clear; Move/simple_uniq; Case/andP; Case/idP.
    By Rewrite: Dw' Dy.
  Move: (Ecc1 y) (Ecc1 (edge y)); Rewrite: /setD -cedge1r -Eh -Dy codom_f /=.
  Rewrite: mem_insertE // (eq_has (plain_orbit Hg0E (h w'))) has_sym /= orbF.
  Do 2 Case; Apply/orP; Right; Rewrite: -Ecc2 -HhE1 !(mem_maps Hh).
  Move: (Hpcc ? Hw'); Rewrite:  mem_insertE //.
  By Rewrite: (eq_has (plain_orbit Hg2E w')) has_sym /= orbF.
Move=> k [HkE H]; Move/fconnect_invariant: H => HkF.
Pose a := [y; w](cface y (h w)).
Step Hah : (w' : g2) ~ (a (h w')) =1 set0.
  By Move=> w' H; Move: (H w'); Rewrite: /a connect0.
Step Ha0: (y : g0) (a y) =1 set0 -> (a (edge y)) =1 set0.
  Rewrite: /a; Move=> y Hy w'; Apply/idP=> [Hw'].
  Case Hxy: (codom h y).
    By Move: (Hy (iinv Hxy)); Rewrite: /a f_iinv connect0.
  Rewrite Eh in Hxy; Move/idP: Hxy => Hxy.
  Case Hxfy: (codom h (face y)).
    By Move: (Hy (iinv Hxfy)); Rewrite: /a f_iinv fconnect1.
  Rewrite Eh in Hxfy; Move/idP: Hxfy => Hxfy.
  Rewrite: (same_cedge Hxy) plain_orbit // mem_seq2 /set2 orbC in Hxfy.
  Case/orP: Hxfy; Move/eqP=> Dfy.
    By Move: (Hbg0 y); Rewrite: Dfy fconnect1.
  Move: (precubic_leq Hg0 y) (f_finv (Inode?) y); Rewrite: /finv.
  Case: (order node y) (orderSpred node y) => [|[|[|[|ny]]]] //= _ _ Ey.
      By Move: (Hbg0 y); Rewrite: -{1 y}Enode Ey Sface fconnect1.
    Step HyF: (fcycle face (seq1 (edge y))).
      By Rewrite: /= /eqdf -{1 y}Ey Enode {1 y}Dfy -{1 y}De20 Eedge set11.
    Rewrite: (fconnect_cycle HyF (setU11 ? ?)) mem_seq1 in Hw'.
    Move: (HcEh w'); Rewrite: (same_cedge Hxy) plain_orbit // mem_seq2.
    By Rewrite: (eqP Hw') set22.
  Move: (Hbg0 (face (edge y))).
  By Rewrite: -cface1 -{2 y}Ey cface1r !Enode {2 y}Dfy -{2 y}De20 Eedge connect0.
Pose k' := [y]if pick w in (a y) then (k w) else Color0.
Step Ek'h: (w : g2)(k' (h w)) = (k w).
  Move=> w; Rewrite: /k'; Case: (pickP (a (h w))) => [w' Hww' | Hw0].
    Apply: HkF; Rewrite: HhF {2}/cfx (eq_has (same_cface Hww')) Sface.
    By Case Hw': (cfx (h w')).
  By Case (Hah ? Hw0).
Step Ek'x: (k' x) = (k' (edge x)).
  Rewrite: /k'; Case: (pickP (a x)) => [w Hwx | Hx0].
    Case: (pickP (a (edge x))) => [w' Hw'ex | Hex0].
      Apply: HkF; Rewrite: /a in Hwx Hw'ex; Rewrite: HhF /cfx /= Sface Hwx /=.
      By Rewrite: orbC Sface Hw'ex.
    By Rewrite: -{x}De20 (Ha0 ? Hex0) in Hwx.
  By Case: (pickP (a (edge x))) => // [w' Hw'ex]; Rewrite: (Ha0 ? Hx0) in Hw'ex.
Exists k'; Split.
  Move=> y; Rewrite: Ezcc1 /setU /invariant in HkE *.
  Case Hy: (cedge x y).
    Rewrite: plain_orbit // mem_seq2 in Hy.
    By Case/orP: Hy; Case/eqP; Rewrite: ?De20  -Ek'x set11.
  Move/idPn: Hy => Hy; Rewrite: -Eh in Hy.
  By Rewrite: -(f_iinv Hy) -HhE1 !Ek'h HkE Ezcc2.
Move=> y; Apply/eqP; Rewrite: /k' -(eq_pick 2!(a y)) //.
By Move=> w; Rewrite: /a cface1.
Qed.
  
End Contract.

Unset Implicit Arguments.
