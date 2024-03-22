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
Require hypermap.
Require walkup.

Set Implicit Arguments.

Section Planarity.

Theorem even_genusP : (g : hypermap) (even_genus g).
Proof.
Move=> g; Elim: {g}(card g) {-3 -4}g (erefl (card g)) => [|n Hrec] g Dn.
  Step Hc0: (a : (set g)) (card a) = (0).
    Move=> a; Apply: eqP; Rewrite: -leqn0 -Dn; Apply max_card.
  By Rewrite: /even_genus /genus /genus_rhs /genus_lhs /n_comp Dn !Hc0.
Case [H](set0Pnx g H); LeftBy Rewrite: /set0b Dn.
Move=> z _; Apply (even_genus_walkup 2!z); Apply Hrec.
By Rewrite: card_walkup Dn.
Qed.

Theorem genus_le : (g : hypermap) (leq (genus_rhs g) (genus_lhs g)).
Proof. Move=> g; Rewrite even_genusP; Apply leq_addl. Qed.

Remark node_is_last : (g : hypermap; x : g; p : (seq g))
  (EX y | (node y) = (last x p) & y = (finv node (last x p))).
Proof.
By Move=> g x p; Exists (finv node (last x p)); Rewrite: ?(f_finv (Inode g)).
Qed.

Theorem planar_jordan : (g : hypermap) (planar g) -> (jordan g).
Proof.
Move=> g Hg; Elim:{g}(card g) {-4 -5}g Hg (erefl (card g)) => [|n Hrec] g Hg Dn.
  By Move=> [|x p]; RightBy Move: (max_card (set1 x)); Rewrite: card1 Dn.
Step HcE : (z : g) (jordan (walkupE z)).
  By Move=> z; Apply: (Hrec ? (planar_walkupE z Hg)); Rewrite: card_walkup Dn.
Step HcN : (z : g) (jordan (walkupN z)).
  Move=> z; Apply: (Hrec ? (planar_walkupN z Hg)).
  By Apply: (etrans (card_walkup ?)); Rewrite: /= Dn.
Step HcF : (z : g) (jordan (walkupF z)).
  Move=> z; Apply: (Hrec ? (planar_walkupF z Hg)).
  By Apply: (etrans (card_walkup ?)); Rewrite: /= Dn.
Clear: n Dn Hrec.
Step HpE: (z, x : g; p : (seq g); Hp : (path clink x p))
          (negb (Adds x p z)) ->
  let g' = (walkupE z) in (EX x' : g' | (subdE x') = x &
    (EX p' | (path clink x' p') & (maps 1!g' (subdE 2!?) p') = p)).
  Move=> z x p; Rewrite: /= /setU1 eqd_sym; Move=> Hp; Move/norP=> [Hx Hpz].
  Exists (subdI 2!(setC1 z) Hx); Trivial.
  Elim: p x Hx Hp Hpz  => [|y p Hrec] x Hx; LeftBy Exists (Seq0 (walkupE z)).
  Rewrite: /= /setU1 eqd_sym; Move/andP=> [Hxy Hp]; Move/norP=> [Hy Hpz].
  Case: {Hrec Hp Hpz}(Hrec y Hy Hp Hpz) => [p' Hp' Dp].
  Exists (Adds (subdI 2!(setC1 z) Hy) p'); RightBy Rewrite: /= Dp.
  Apply/andP; Split; [Apply/clinkP | Done].
  Case/clinkP: Hxy => [Dny | Dfx]; [Left | Right]; Apply: subdE_inj.
    By Rewrite: /= /skip1 -Dny (negbE Hx).
  By Rewrite: /= /skip1 Dfx (negbE Hy).
Step HpN: (z, x : g; p : (seq g); Hp : (path clink x p))
          (negb (Adds x p z)) -> (negb (p (face z))) ->
  let g' = (walkupN z) in (EX x' : g' | (subdE x') = x &
    (EX p' | (path clink x' p') & (maps 1!g' (subdE 2!?) p') = p)).
  Move=> z x p; Rewrite: /= /setU1 eqd_sym; Move=> Hp; Case/norP=> [Hx Hpz] Hpfz.
  Exists (subdI 2!(setC1 z) Hx); Trivial.
  Elim: p x Hx Hp Hpz Hpfz => [|y p Hrec] x; LeftBy Exists (Seq0 (walkupN z)).
  Rewrite: /= /setU1 !(eqd_sym y); Move=> Hx; Move/andP=> [Hxy Hp].
  Move/norP => [Hy Hpz]; Move/norP => [Hyfz Hpfz].
  Case: {Hrec Hp Hpz Hpfz}(Hrec y Hy Hp Hpz Hpfz) => [p' Hp' Dp].
  Exists (Adds (subdI 2!(setC1 z) Hy) p'); RightBy Exact (congr ? Dp).
  Apply/andP; Split; [Apply/clinkP | Done].
  Case/clinkP: Hxy => [Dny | Dfx]; [Left | Right]; Apply: subdE_inj.
    Rewrite: /= /skip_edge1 /= -(monic2F_eqd (Eface g)) -Dny (negbE Hx).
    By Rewrite: (negbE Hyfz) if_same.
  By Rewrite: /= /skip1 /= Dfx (negbE Hy).
Step HpF: (z, x : g; p : (seq g); Hp : (path clink x p))
          (negb (Adds x p z)) -> (negb (p (face (edge z)))) ->
  let g' = (walkupF z) in (EX x' : g' | (subdE x') = x &
    (EX p' | (path clink x' p') & (maps 1!g' (subdE 2!?) p') = p)).
  Move=> z x p; Rewrite: /= /setU1 eqd_sym; Move=> Hp; Move/norP=> [Hx Hpz] Hpfez.
  Exists (subdI 2!(setC1 z) Hx); Trivial.
  Elim: p x Hx Hp Hpz Hpfez => [|y p Hrec] x; LeftBy Exists (Seq0 (walkupF z)).
  Rewrite: /= /setU1 (eqd_sym y); Move=> Hx; Move/andP=> [Hxy Hp].
  Move/norP => [Hy Hpz]; Move/norP => [Hyfez Hpfez].
  Case: {Hrec Hp Hpz Hpfez}(Hrec y Hy Hp Hpz Hpfez) => [p' Hp' Dp].
  Exists (Adds (subdI 2!(setC1 z) Hy) p'); RightBy Exact (congr ? Dp).
  Apply/andP; Split; [Apply/clinkP | Done].
  Case/clinkP: Hxy => [Dny | Dfx]; [Left | Right]; Apply: subdE_inj.
    By Rewrite: /= /skip1 /= -Dny (negbE Hx).
  Rewrite: /= /skip_edge1 /= Dfx (negbE Hy) !(eqd_sym z).
  By Rewrite: (monic2F_eqd (Enode g)) (negbE Hyfez) if_same.
Move=> [|x p]; [Done | Apply/and3P].
Case: (node_is_last x p) => [y Dny []] [Hp2 Up Hp].
Pose HeI := [z : g](subdE_inj 2!(setC1 z)).
Case: (pickP (setC (Adds x p))) => [z Hz | Hpg].
  Case: {Hp}(HpE ? ? ? Hp Hz) => [x' Dx [p' Hp' Dp]].
  Simpl in Dp; Case/and3P: (HcE z (Adds x' p')); Split; Auto.
    Case: (node_is_last x' p') => [[y' Hy'] Dny' []]; Simpl in Dny'.
    Rewrite: -(mem2_maps 2!(walkupE z) (HeI z)) /= Dp Dx /skip1.
    Rewrite: -Dp -Dx last_maps /= -Dny' /= /skip1 in Dny.
    Case: (z =P (node x)) => [Dz | _].
      By Rewrite: Dz /setC /= (setU1r x (mem2r Hp2)) in Hz.
    Case: (z =d (node y')) Dny => [|] Dny; RightBy Rewrite: -(Inode g Dny).
    By Rewrite: -(Inode g Dny) /setC /= (setU1r x (mem2l Hp2)) in Hz.
  By Rewrite: -(uniq_maps 1!(walkupE z) (HeI z)) /= Dx Dp.
Move: (cardC (Adds x p)); Rewrite: (card_uniqP Up) (eq_card Hpg) card0 addn0.
Case: p x (mem2l Hp2) Hp Up Hp2 Dny Hpg => [|x1 p] x0 //=.
Case Hx0y: (x0 =d y); LeftBy Move=> H _; Rewrite: (eqP Hx0y) H.
Clear; Move/andP=> [Hx01 Hp]; Move/andP=> [Hpx0 Up] Hp2 Dny.
Rewrite: mem2_adds in Hp2.
Case/clinkP: Hx01 => [Dnx1 | Dfx0].
  Case: {Hp}(HpE ? ? ? Hp Hpx0) => [x' Dx1 [p' Hp' Dp]].
  Case/and3P: (HcE x0 (Adds x' p')); Split; Auto.
    Case: (x1 =P y) Hp2 => [Dy | _] Hp2.
      By Rewrite: Dnx1 {2 x1}Dy Dny mem_lastU in Hpx0.
    Case: (node_is_last x' p') => [[y' Hy'] Dny' [ ]].
    Rewrite: -(mem2_maps 2!(walkupE x0) (HeI x0)) Dp /= /skip1 Dx1 -Dnx1 set11.
    Rewrite: -Dp -Dx1 last_maps -Dny' /= /skip1 in Dny.
    Case: (x0 =d (node y')) Dny => [|] Dny; RightBy Rewrite: -(Inode g Dny).
    By Rewrite: (Inode g Dny) set11 in Hx0y.
  By Rewrite: -Dp -Dx1 in Up; Rewrite: -(uniq_maps 1!(walkupE x0) (HeI x0)).
Case: p Hp Hp2 Dny Up Dfx0 Hpx0 => [|x2 p].
  Simpl; Case (x1 =d y); Rewrite: // /setU1 orbF /=.
  By Move=> _ H Dny; Rewrite: -(inj_eqd (Inode g)) Dny eqd_sym H in Hx0y.
Simpl; Move/andP=> [Hx1p Hp] Hp2 Dny; Move/andP=> [Hpx1 Up] Dfx0.
Move/norP => [Hx10 Hpx0]; Pose u01 := (subdI 2!(setC1 x1) Hx10).
Case/clinkP: Hx1p => [Dnx2 | Dfx1].
  Case: {Hp}(HpF ? ? ? Hp Hpx1); LeftBy Rewrite: Dnx2 Enode; Case/andP: Up.
  Case Hx1nx0: (x1 =d (node x0)).
    By Rewrite: (eqP Hx1nx0) in Dnx2; Rewrite: (Inode g Dnx2) setU11 in Hpx0.
  Move=> x' Dx2 [p' Hp' Dp].
  Case/and3P: (HcF x1 (Adds u01 (Adds x' p'))); Split.
      Rewrite: last_adds -(mem2_maps 2!(walkupF x1) (HeI x1)).
      Case: (node_is_last x' p') => [[y' Hy'] Dny' [ ]]; Simpl in y' Hy'.
      Rewrite: -Dp -Dx2 last_maps -Dny' /= /skip1 /= in Dny; Simpl in Dp Dx2.
      Rewrite: /= Dp Dx2 /skip1 /= Hx1nx0.
      Case: (x1 =P (node y')) Dny => [Dx1 | _] Dny.
        Rewrite: Dx1 in Dnx2; Rewrite: (Inode g Dnx2) mem2_adds set11.
        By Rewrite: (Inode g Dny) set11 /setU1 Hx1nx0 in Hp2.
      By Rewrite: (Inode g Dny) (negbE Hy') in Hp2 *.
    Simpl in Dp Dx2; Rewrite: -(uniq_maps 1!(walkupF x1) (HeI x1)) /= Dp Dx2.
    By Rewrite Hpx0.
  Apply/andP; Split; [Apply/clinkP; Right; Apply: subdE_inj | Done].
  Rewrite: Dx2 /= /skip_edge1 /= -{1 x1}Dfx0 (inj_eqd (Iface g)).
  Rewrite: (eqd_sym x0) (negbE Hx10) Dfx0 set11.
  Case: (x1 =P (node x1)) => [Dx1 | _]; RightBy Rewrite: Dnx2 Enode.
  By Rewrite: Dx1 in Dnx2; Rewrite: (Inode g Dnx2) setU11 in Hpx1.
Rewrite: -if_negb in Hp2; Case Hx1y: (negb x1 =d y) Hp2.
  Case: {Hp}(HpE ? ? ? Hp Hpx1) => [x' Dx2 [p' Hp' Dp]] Hp2.
  Case/and3P: (HcE x1 (Adds u01 (Adds x' p'))); Split.
      Rewrite: -(mem2_maps 2!(walkupE x1) (HeI x1)) last_adds.
      Case: (node_is_last x' p') => [[y' Hy'] Dny' [ ]]; Simpl in y' Hy'.
      Rewrite: -Dp -Dx2 last_maps -Dny' /= /skip1 in Dny; Simpl in Dp Dx2.
      Rewrite: /= Dp Dx2 /skip1 /=.
      Case: (x1 =P (node x0)) => [Dx1 | _].
        By Rewrite: -Dx1 in Hp2; Rewrite: -mem_adds (mem2r Hp2) in Hpx1.
      Case: (x1 =d (node y')) Dny => [|] Dny; RightBy Rewrite: -(Inode g Dny).
      By Rewrite: (Inode g Dny) set11 in Hx1y.
    Simpl in Dp Dx2; Rewrite: -(uniq_maps 1!(walkupF x1) (HeI x1)) /= Dp Dx2.
    By Rewrite Hpx0.
  Apply/andP; Split; [Apply/clinkP; Right; Apply: subdE_inj | Done].
  By Rewrite: Dx2 /= /skip1 Dfx0 set11 Dfx1.
Case/eqP: Hx1y Dny => [ ] Dnx1 Hp2.
Case Hnx1: (x1 =d (node x1)).
  By Rewrite: (eqP Hnx1) Dnx1 mem_lastU in Hpx1.
Case Hx1nx0: (negb x1 =d (node x0)).
  Rewrite: /setU1 (negbE Hx1nx0) /= in Hp2; Case: {Hp}(HpN ? ? ? Hp Hpx1).
    By Rewrite: Dfx1; Case: (andP Up).
  Move=> x' Dx2 [p' Hp' Dp].
  Case/and3P: (HcN x1 (Adds u01 (Adds x' p'))); Split.
      Rewrite: -(mem2_maps 2!(walkupN x1) (HeI x1)) last_adds.
      Case: (node_is_last x' p') => [[y' Hy'] Dny' [ ]]; Simpl in y' Hy'.
      Rewrite: -Dp -Dx2 last_maps -Dny' /= /skip_edge1 /= in Dnx1.
      Simpl in Dp Dx2; Rewrite: /= Dp Dx2 /skip_edge1 /=; Move: Dnx1.
      Rewrite: (negbE Hx1nx0) -!(monic2F_eqd (Eface g)) Hnx1 Dfx1.
      Case: (x2 =P x0) => [Dx0 | _]; LeftBy Rewrite: -Dx0 setU11 in Hpx0.
      Case: (x2 =P y') => [Dy' | _]; LeftBy Rewrite: -Dy' mem2_adds set11.
      Case: (x1 =d (node y')) {Dny'} => [|] Dnx1.
        By Rewrite: (Inode g Dnx1) setU11 in Hpx1.
      By Rewrite: /setC1 (Inode g Dnx1) set11 in Hy'.
    Simpl in Dp Dx2; Rewrite: -(uniq_maps 1!(walkupF x1) (HeI x1)) /= Dp Dx2.
    By Rewrite Hpx0.
  Apply/andP; Split; [Apply/clinkP; Right; Apply: subdE_inj | Done].
  By Rewrite: Dx2 /= /skip1 /= Dfx0 set11 Dfx1.
Move: {Hx1nx0}(esym (eqP (negbEf Hx1nx0))) {Hnx1 Hp2} => Dnx0.
Case: p Hp Up Hpx0 Hpx1 Dfx1 Dnx1 => [|x3 p].
  Rewrite: /= /setU1 !orbF; Move=> _ _ Hx20 Hx21 Dfx1 Dnx1 Hpg Hcg.
  Step Hge1: (e : (rel g))
             (connect_sym e) -> (e x0 x1) -> (e x1 x2) -> (n_comp e g) = (1).
    Move=> e He He01 He12; Rewrite: -(card1 (root e x1)); Apply: eq_card => [x].
    Rewrite: /setI andbT; Congr (!eqd g); Apply: (rootP He).
    Case/or3P: (Hpg x); Rewrite: ?orbF; Case/eqP.
        By Apply connect1.
      By Rewrite connect0.
    By Rewrite He; Apply connect1.
  Step Dex0: (edge x0) = x1.
    Apply: eqP; Rewrite: (monic2F_eqd (Eedge g)) Dfx1; Move/idP: (Hpg (node x2)).
    Rewrite: /setU1 -Dnx0 -{3 x2}Dnx1 !(inj_eqd (Inode g)) -!(eqd_sym x2).
    By Rewrite: (negbE Hx20) (negbE Hx21) !orbF.
  Step Dex1: (edge x1) = x2.
    Apply: (Iface g (eqP ?)); Rewrite: -Dnx0 Enode; Move/idP: (Hpg (face x2)).
    Rewrite: /setU1 -Dfx0 -{3 x2}Dfx1 !(inj_eqd (Iface g)) -!(eqd_sym x2).
    By Rewrite: (negbE Hx20) (negbE Hx21) !orbF.
  Move: Hg; Rewrite: /planar /genus /genus_lhs /genus_rhs.
  Rewrite: -Hcg !Hge1 //; Try By Apply/eqP.
    Exact (Sface g). Exact (Snode g). Exact (Sedge g). Exact (Sglink g).
    By Rewrite: -Dfx0 glinkF.
    By Rewrite: -Dfx1 glinkF.
Simpl; Move/andP=> [Hx2p Hp]; Move/andP=> [Hpx2 Up].
Move/norP=> [Hx20 Hpx0]; Move/norP=> [Hx21 Hpx1] Dfx1 Dnx1.
Pose u02 := (subdI 2!(setC1 x2) Hx20).
Pose u12 := (subdI 2!(setC1 x2) Hx21).
Case/clinkP: Hx2p => [Dnx3 | Dfx2].
  Case: {Hp}(HpF ? ? ? Hp Hpx2); LeftBy Rewrite: Dnx3 Enode; Case (andP Up).
  Move=> x' Dx3 [p' Hp' Dp].
  Case/and3P: (HcF x2 (Adds u02 (Adds u12 (Adds x' p')))); Split.
      Rewrite: -(mem2_maps 2!(walkupF x2) (HeI x2)) !last_adds.
      Case: (node_is_last x' p') => [[y' Hy'] Dny' [ ]]; Simpl in y' Hy'.
      Rewrite: -Dp -Dx3 last_maps -Dny' /= /skip1 /= in Dnx1; Simpl in Dp Dx3.
      Rewrite: /= Dp Dx3 /skip1 /= Dnx0 (negbE Hx21).
      Case: (x2 =d (node y')) Dnx1 => [|] Dnx1.
        By Case/eqP: {}Hx21; Apply Inode.
      By Rewrite: (Inode g Dnx1) mem2_adds set11 setU11.
    Simpl in Dp Dx3; Rewrite: -(uniq_maps 1!(walkupF x2) (HeI x2)) /= Dp Dx3.
    By Rewrite: {1}/setU1 negb_orb Hx10 Hpx0 Hpx1.
  Apply/and3P; Split; Auto; Apply/clinkP; Right; Apply: subdE_inj.
    Rewrite: /= /skip_edge1 /= Dfx0 (negbE Hx21) Dnx3 (inj_eqd (Inode g)).
    Case: (x3 =P x1) => [Dx1 | _]; LeftBy Rewrite: -Dx1 setU11 in Hpx1.
    By Rewrite: if_same.
  Rewrite: Dx3 /= /skip_edge1 /= Dfx1 set11 -{1 x2}Dfx1 (inj_eqd (Iface g)).
  Rewrite: (eqd_sym x1)(negbE Hx21) {1 x2}Dnx3 (inj_eqd (Inode g)).
  Case: (x3 =P x2) => [Dx2 | _]; LeftBy Rewrite: -Dx2 setU11 in Hpx2.
  By Rewrite: Dnx3 Enode.
Case: {Hp}(HpE ? ? ? Hp Hpx2) => [x' Dx3 [p' Hp' Dp]].
Case/and3P: (HcE x2 (Adds u02 (Adds u12 (Adds x' p')))); Split.
    Rewrite: -(mem2_maps 2!(walkupE x2) (HeI x2)) !last_adds.
    Case: (node_is_last x' p') => [[y' Hy'] Dny' [ ]]; Simpl in y' Hy'.
    Rewrite: -Dp -Dx3 last_maps -Dny' /= /skip1 in Dnx1; Simpl in Dp Dx3.
    Rewrite: /= Dp Dx3 /skip1 /= Dnx0 (negbE Hx21).
    Case: (x2 =d (node y')) Dnx1 => [|] Dnx1.
      By Case/eqP: {}Hx21; Apply Inode.
    By Rewrite: (Inode g Dnx1) mem2_adds set11 setU11.
  Simpl in Dp Dx3; Rewrite: -(uniq_maps 1!(walkupF x2) (HeI x2)) /= Dp Dx3.
  By Rewrite: {1}/setU1 negb_orb Hx10 Hpx0 Hpx1.
Apply/and3P; Split; Auto; Apply/clinkP; Right; Apply: subdE_inj.
  By Rewrite: /= /skip1 /= Dfx0 (negbE Hx21).
By Rewrite: /= /skip1 Dfx1 set11 Dfx2.
Qed.

Lemma euler_tree : (g : hypermap; Hj : (jordan g); x : g)
  (negb (disjoint (cedge x) [y](orb (clink y y) (negb (cross_edge y))))).
Proof.
Move=> g Hj x0; Apply/set0P=> [Hx0].
Move: (!root g (eqdf face)) (rootPx (Sface g)) => rf rfP.
Cut ~(EX x | (cedge x0 x) &
     (EX p |  (fpath edge x p) /\ (uniq (maps rf (Adds x p)))
          &  (rf (node (face x))) = (rf (last x p)))).
  Case; Def: Hp' := (fconnect1 edge x0); Rewrite Sedge in Hp'.
  Case/connectP: Hp' => [p' Hp' Ep']; Pose p := (Adds (edge x0) p').
  Step Hp: (fpath edge x0 p) By Rewrite: /= /eqdf set11.
  Step Up: (negb (uniq (maps rf (Adds x0 p)))).
    By Rewrite: /= -{2 x0}Ep' -(last_maps rf) mem_lastU.
  Step Ep : (last x0 p) = x0 By Done.
  Elim Dp: p {1 2 4}x0 Hp Ep Up {p' Hp' Ep'} => [|ex p' Hrec] x //.
  Rewrite: -Dp {1 2 p}Dp /=; Move/andP=> [Dex Hp] Ep.
  Case Up: (uniq (maps rf p)); RightBy Move: (negbI Up); Rewrite Dp; EAuto.
  Rewrite: andbT negb_elim Dp ~{Hrec}; Move/mapsP=> [y Hpy Drfy].
  Step Hx0x': (cedge x0 ex) By Rewrite Sedge; Apply/connectP; Exists p'.
  Case/splitPl: {p' Ep}Hpy Dp Hp => [p1 p2 Ep1]; Rewrite: -cat_adds; Move=> Dp Hp.
  Rewrite: path_cat in Hp; Case/andP: Hp => [Hp1 _].
  Rewrite: Dp maps_cat uniq_cat in Up; Case/andP: Up => [Up1 _].
  By Exists ex; RightBy Exists p1; [Split | Rewrite: Ep1 -(eqP Dex) Eedge].
Case; Move=> x Hx0x; Pose fx := (face x); Pose nfx := (node fx).
Move=> [pe [Hpe Upe] Erpe]. 
Step [pc [Hpc Epc] [Upc _ Hnpc]] : (EX pc |
       (path clink fx pc) /\ (last fx pc) = nfx
    & let xpc = (Adds fx pc) in
      (and3 (uniq xpc) (maps rf xpc) =1 (maps rf (Adds x pe))
        (y : g) (xpc (face y)) -> (negb (belast fx pc y)) -> (last x pe) = y)).
  Step Hfpcp: (y : g; p : (seq g))(fpath face y p) -> (path clink y p).
    Move=> y p; Elim: p y => [|y' p Hrec] y //=; Move/andP=> [Dy Hp].
    By Rewrite: (Hrec ? Hp) -(eqP Dy) clinkF.
  Move: Hpe Upe Erpe {Hx0x}; ClearBody nfx; Rewrite: ~/fx.
  Elim: pe x => [|ex p Hrec] x /=.
    Do 2 Clear; Rewrite: (rfP x ? (fconnect1 ? ?)).
    Move/esym; Move/(introT (rfP ? ?)); Case/connectP; Move=> pc0.
    Case/shortenP=> [pc Hpc Upc _] {pc0} Epc; Exists pc; Split; Auto.
      Move=> z; Rewrite: /setU1 orbF; Case ((rf (face x)) =P z); LeftDone.
      Move=> H; Apply/mapsP=> [[y Hy Dz]]; Case: H; Case: {z}Dz.
      Exact (rfP ? ? (path_connect Hpc (setU1r ? Hy))).
    Case: Epc => [] y; Rewrite: /setU1 (inj_eqd (Iface g)).
    Case: (x =P y) => [Dx|_] // H; Case/splitPr: H Hpc {Upc} => [p1 p2].
    Rewrite: path_cat belast_cat mem_cat /= /setU /setU1.
    Rewrite: {2}/eqdf (inj_eqd (Iface g)) eqd_sym.
    By Case (y =d (last (face x) p1)); Rewrite: /= ?orbT ?andbF.
  Move/andP=> [Dex Hp]; Move/andP=> [Hpx Up] Ep.
  Case: {Hrec Hp Up}(Hrec ? Hp Up Ep) => [q2 [Hq2 Eq2] [Uq2 Hrq2 Hfq2]].
  Case/connectP: (etrans (Sface ? ? x) (fconnect1 ? ?)).
  Move=> q0; Case/shortenP=> [q1 Hq1 Uq1 _] {q0} Eq1.
  Step Hrq1: (y : g) (Adds (face x) q1 y) -> (rf y) = (rf x).
    Move=> y Hq1y; Symmetry; Apply: rfP; Rewrite cface1.
    Exact (path_connect Hq1 Hq1y).
  Exists (cat q1 (Adds (face ex) q2)).
    Rewrite: path_cat last_cat Eq1 /=; Split; RightDone.
    By Rewrite: (Hfpcp ? ? Hq1) -(Eedge g x) (eqP Dex) clinkN.
  Split.
      Rewrite: -uniq_adds -cat_adds uniq_cat Uq1 Uq2 andbT.
      Apply/hasP=> [[y Hq2y Hq1y]]; Case/idP: Hpx.
      Apply: (etrans (esym (Hrq2 ?))); Apply/mapsP; Exists y; Auto.
    Move=> y; Rewrite: maps_cat {1 2}/setU1 mem_cat /setU Hrq2 orbA; Congr orb.
    Apply/(mapsPx ? (Adds ? ?) ?)/eqP=> [[z Hq1z []] | []].
      By Apply esym; Auto.
    By Exists x; LeftBy Rewrite: -{2 x}Eq1 mem_last.
  Move=> y; Rewrite: -cat_add_last belast_cat belast_add_last last_add_last.
  Rewrite: -mem_adds cat_add_last -cat_adds !mem_cat /setU.
  Step Hcq1: (fcycle face (Adds (face x) q1)).
    By Rewrite: /= -cats1 path_cat Eq1 Hq1 /= /eqdf set11.
  Rewrite: -!(fconnect_cycle Hcq1 (mem_last ? ?)) Eq1 !(Sface g x) -cface1.
  By Case Hyx: (cface y x); RightBy Exact (Hfq2 y).
Step Hnfx: (cedge x nfx) By Rewrite: Sedge -(Eface g x) /nfx fconnect1.
Step Hfx: (cedge x fx).
  Step Hnx: (fclosed node (cedge x)); RightBy Rewrite: (fclosed1 Hnx).
  Apply: (intro_closed (Snode g)) =>  [y1 y2 Dy2 Hy1].
  Apply: (connect_trans Hy1).
  Move: (negbI (Hx0 y1)); Rewrite: -(eqP Dy2)/setI (connect_trans Hx0x Hy1).
  By Rewrite: /= negb_orb negb_elim /cross_edge; Case/andP.
Step Hpefx: (negb (Adds x pe fx)).
  Case/andP: Upe => [Hpx _]; Apply/orP=> [[Dx | Hpfx]].
    Case/andP: (Hx0 x); Split; RightBy Rewrite: {2 x}(eqP Dx) /fx clinkF.
    Rewrite (eqP Dx); Exact (connect_trans Hx0x Hfx).
  By Case/mapsP: Hpx; Exists fx; RightBy Exact (esym (rfP ? ? (fconnect1 ? ?))).
Case: (fx =P nfx) => [Dfx | Hfxn].
  Case/andP: (Hx0 nfx); Split; LeftBy Exact (connect_trans Hx0x Hnfx).
  By Rewrite: -{2 nfx}Dfx /nfx clinkN.
Clear: x0 Hx0 rf rfP Hx0x Upe Erpe.
Step [qe [Hqe Eqe] Hqepe]: (EX qe | (fpath edge fx qe) /\ (last fx qe) = nfx
                                  & (negb (Adds fx qe (last x pe)))).
  Case: (connectP Hnfx); Rewrite: Sedge in Hnfx.
  Move=> q0; Case/shortenP=> [q Hq Uq _] {q0} Eq.
  Step Hqfx: (Adds x q fx).
    Apply: (etrans (esym ?) Hfx); Apply: fconnect_cycle; Rewrite: /= ?setU11 //.
    By Rewrite: -cats1 path_cat Hq Eq /= /eqdf /nfx /fx Eface set11.
  Case/splitPl: {q Hnfx Hfx Hnpc}Hqfx Hq Uq Eq => [q1 qe Eq1].
  Rewrite: path_cat last_cat Eq1; Move/andP=> [Hq1 Hqe] Uq Eqe.
  Exists qe; [By Split | Simpl; Apply/norP; Split].
    By Apply/eqP=> [Dfx]; Rewrite: Dfx mem_last in Hpefx.
  Case: {fx nfx npc Hpc Upc Epc Hfxn Eq1 Eqe Hqe}Eq1 Hpefx Hpe.
  Elim: q1 pe x Hq1 Uq => [|y q1 Hrec] pe x /=; LeftBy Rewrite: setU11.
  Move/andP=> [Dy Hq1]; Move/andP=> [Hqx Uq]; Case/norP.
  Case: pe => [|y' pe] _ Hpeq1 /=.
    By Rewrite: /setU1 mem_cat /setU orbA in Hqx; Case/norP: Hqx.
  Move/andP=> [Dy' Hpe]; Rewrite: /eqdf (eqP Dy) in Dy'.
  By Case: (eqP Dy') Hpeq1 Hpe; Auto.
Cut (EX qc | (path clink nfx qc) /\ (last nfx qc) = fx
           & (negb (has (Adds fx pc) qc))).
  Move=> [qc [_ Eqc] Hqpc]; Case/idP: Hqpc; Rewrite: has_sym /=.
  Case: qc Eqc => [|y qc] Eqc; LeftBy Case Hfxn.
  By Simpl in Eqc; Rewrite: -Eqc mem_last.
Elim: qe {-5}fx Eqe Hqe Hqepe => [|y' qe Hrec] /=; LeftBy Exists (Seq0 g); Auto.
Move=> y Eqe; Move/andP=> [Dy' Hqe]; Move/norP=> [_ Hqepe].
Case: {Hrec Hqe Eqe}(Hrec ? Eqe Hqe Hqepe) => [qc [Hqc Eqc] Hqcpc].
Def: Hny := (fconnect1 (!node?) (face (edge y))); Rewrite: Snode Eedge in Hny.
Case/connectP: Hny => [p Hp Ep]; Apply (proj2 ~ y = nfx).
Elim: p {-3}y Hp Ep => [|z' p Hrec] z /=.
  Move=> _ Dz; Case Hpcz: (Adds fx pc z).
    Case/idP: Hqepe; Rewrite Dz in Hpcz; Rewrite: (Hnpc ? Hpcz).
      By Rewrite: (eqP Dy') setU11.
    Apply/idP=> [Hey]; Case/hasP: Hqcpc.
    Exists (edge y); [Move: (mem_last nfx qc) | By Apply mem_belast].
    Rewrite: Eqc (eqP Dy') /= /setU1; Case: (nfx =P y') => [Dnfx|H] //.
    By Rewrite: lastI Epc Dnfx -(eqP Dy') -cats1 uniq_cat /= Hey andbC in Upc.
  Split; LeftBy Move=> Dnfx; Rewrite: Dnfx -Epc mem_last in Hpcz.
  Exists (add_last qc z).
    Split; RightBy Rewrite: last_add_last.
    By Rewrite: -cats1 path_cat Hqc Eqc -(eqP Dy') Dz /= clinkF.
  By Rewrite: -cats1 has_cat /= -mem_adds Hpcz orbF.
Move/andP=> [Dz' Hp] Ep; Clear: Hnpc y' qe Dy' Hqepe qc Hqc Ehqc Eqc Hqcpc.
Case: {y Hrec Hp Ep}(Hrec ? Hp Ep); Move=> Hz'nfx; Case; Move=> qc0; Case.
Case/shortenP=> [qc Hqc Uqc Hqc0] Eqc.
Case Hpcqc: (has (Adds fx pc) qc).
  Case/hasP; Case/hasP: Hpcqc => [y Hqcy Hpcy]; Exists y; Auto.
Clear; Case Hpcz: (Adds fx pc z) {qc0 Hqc0}.
  Case/and3P: (Hj (Adds fx (cat pc qc))); Split.
      Rewrite: last_cat Epc Eqc -(eqP Dz') (finv_f (Inode g)) -/nfx -Epc.
      Rewrite: mem2_cat -orbA; Apply/orP; Left; Simpl in Hpcz; Case/orP: Hpcz.
        By Move=> Dfx; Case Hz'nfx; Rewrite: /nfx (eqP Dfx) (eqP Dz').
      Case: pc Epc {Upc Hpcqc Hpc} => [|fx' pc] *; LeftBy Case Hfxn.
      By Rewrite: /= mem2_last.
    By Rewrite: -cat_adds uniq_cat Upc Hpcqc; Case/andP: Uqc.
  By Rewrite: path_cat Hpc Epc.
Split; LeftBy Move=> Dz; Rewrite: Dz -Epc mem_last in Hpcz.
Exists (add_last qc z).
  Split; RightBy Rewrite: last_add_last.
  By Rewrite: -cats1 path_cat Hqc Eqc -(eqP Dz') /= clinkN.
By Simpl in Hpcqc; Rewrite: -cats1 has_cat /= -mem_adds Hpcqc Hpcz.
Qed.

Theorem jordan_planar : (g : hypermap) (jordan g) -> (planar g).
Proof.
Move=> g Hg; Elim:{g}(card g) {-4 -5}g Hg (erefl (card g)) => [|n Hrec] g Hg Dn.
  Step Hc0: (a : (set g)) (card a) = (0).
    Move=> a; Apply: eqP; Rewrite: -leqn0 -Dn; Apply max_card.
  By Rewrite: /planar /genus /genus_rhs /genus_lhs /n_comp Dn !Hc0.
Case Hg0: (set0b g); LeftBy Rewrite: (eqnP Hg0) in Dn.
Case/set0Pn: Hg0 => [x _].
Case/set0Pn: (euler_tree Hg x); Move=> z; Move/andP=> [_ Hz].
Rewrite: /planar -(genus_walkupE_eq 2!z).
  By Apply: (Hrec ? (jordan_walkupE Hg)); Rewrite: card_walkup Dn.
Case/orP: Hz; [Case/clinkP=> [Dz|Dz]; Left | By Right].
  By Rewrite: {2 z}Dz glinkN.
By Rewrite: -{2 z}Dz glinkF.
Qed.

Theorem planarP : (g : hypermap) (reflect (jordan g) (planarb g)).
Proof. Exact [g](iffP idP (!planar_jordan g) (!jordan_planar g)). Qed.

End Planarity.

Unset Implicit Arguments.

