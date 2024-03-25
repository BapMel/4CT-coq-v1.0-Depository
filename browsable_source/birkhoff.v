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
Require jordan.
Require geometry.
Require color.
Require chromogram.
Require coloring.
Require patch.
Require snip.
Require sew.
Require revsnip.
Require kempe.
Require ctree.
Require initctree.
Require gtree.
Require initgtree.
Require ctreerestrict.
Require gtreerestrict.
Require cfmap.
Require cfcolor.
Require kempetree.

Set Implicit Arguments.

(* The birkhoff theorem: a minimal coloring counter-example must be *)
(* internally 5-connected. *)

Section BirkhoffCheck.

Variables h, m : nat.

Fixpoint ctree_pick_rev_rec [et : colseq; e : color; t', t : ctree] : colseq :=
  Cases t of
    (Ctree_leaf _) =>
       if (ctree_mem t' (etrace (belast e et))) then (Adds e et) else seq0
  | (Ctree_node t1 t2 t3) =>
    if (ctree_pick_rev_rec (Adds Color1 et) (addc e Color1) t' t1) then
      if (ctree_pick_rev_rec (Adds Color2 et) (addc e Color2) t' t2) then
        (ctree_pick_rev_rec (Adds Color3 et) (addc e Color3) t' t3)
      else Adds else Adds
  | _ => seq0
  end.

Definition ctree_pick_rev : (t, t' : ctree) colseq :=
  (ctree_pick_rev_rec seq0 Color0).

Lemma sumt_ctree_pick_rev : (t, t' : ctree)
  (sumt (ctree_pick_rev t t')) = Color0.
Proof.
Move=> t' t; Rewrite: /ctree_pick_rev; Pose cs0 := (seq0 :: colseq).
Step Ecs0 : (addc Color0 (sumt cs0)) = Color0 By Done.
Elim: t cs0 {1 3}Color0 Ecs0 => [t1 Ht1 t2 Ht2 t3 Ht3 | lf _ |] et e //.
  Move=> Het /=; Pose cprr := ctree_pick_rev_rec.
  Case Det1: (cprr (Adds Color1 et) (addc e Color1) t' t1) => [|e1 et1].
    Case Det2: (cprr (Adds Color2 et) (addc e Color2) t' t2) => [|e2 et2].
      By Apply: Ht3; Rewrite: {Color3}lock /= -addcA addc_inv.
    By Rewrite: -Det2; Apply: Ht2; Rewrite: {Color2}lock /= -addcA addc_inv.
  By Rewrite: -Det1; Apply: Ht1; Rewrite: {Color1}lock /= -addcA addc_inv.
By Move=> Het; Simpl; Case (ctree_mem t' (etrace (belast e et))).
Qed.

Lemma size_ctree_pick_rev : (t, t' : ctree)
  (ctree_proper h t') -> (set2 (0) (S h) (size (ctree_pick_rev t t'))).
Proof.
Move=> t' t; Rewrite: /ctree_pick_rev; Pose cs0 := (seq0 :: colseq).
Step Ecs0: (addn (size cs0) h) = h By Done.
Elim: {1 3}h t cs0 {1}Color0 Ecs0 => [|n Hrec] [t1 t2 t3 | lf |] et e //=.
  Rewrite: addn0; Case: (ctree_mem t' (etrace (belast e et))) => // [] Het.
  By Rewrite: /set2 /= Het set11.
Rewrite: -addSnnS; Move=> Het [_ Ht1 Ht2 Ht3].
Pose cprr := ctree_pick_rev_rec.
Case Det1: (cprr (Adds Color1 et) (addc e Color1) t' t1) => [|e1 et1].
  Case Det2: (cprr (Adds Color2 et) (addc e Color2) t' t2) => [|e2 et2].
    Auto.
  Rewrite: -Det2; Auto.
Rewrite: -Det1; Auto.
Qed.

Section BirkhoffTree.

Variable check_basis : ctree -> bool.

Definition do_bkf_check2 [et : colseq; ctu : ctree; gtu : gtree;
                          chk : ctree -> gtree -> bool] : bool :=
  let ctr = (ctree_of_ttail (etrace et)) in
  if (et Color0) then false else
  let (ctu', gtru') = (kempe_tree_closure (pred h) h ctu ctr gtu) in
  if gtru' is (Gtree_pair Gtree_empty gtu') then
    (orb (check_basis ctu') (chk ctu' gtu'))
  else false.

Fixpoint bkf_check2 [ctu1 : ctree; gtu1 : gtree; n : nat]
                  : ctree -> gtree -> bool :=
  [ctu2; gtu2]if n is (S n') then
    if (ctree_pick_rev ctu1 ctu2) is (Adds e et) then
       (andb (do_bkf_check2 (belast e et) ctu1 gtu1 (bkf_check2 ctu2 gtu2 n'))
             (do_bkf_check2 (rev et) ctu2 gtu2 (bkf_check2 ctu1 gtu1 n')))
    else false
  else false.

End BirkhoffTree.

Definition bkf_check1 [cp : cprog] : bool :=
  (and3b (cubic_prog cp)
         (ltn (S (card (cpmap cp))) (plus (mult (6) m) (mult (4) h)))
         (cprsize cp) =d (S h)).

Inductive birkhoff_check : Prop :=
  BkfCheck : (niter : nat; cps : (seq (seqData cpstepData)))
  let ctu = (ctree_init_tree h) in let gtu = (gtree_init_tree h) in
  let basis = (maps cpcolor cps) in
  let chkb = [t](has (ctree_disjoint t) basis) in
    (all bkf_check1 cps) -> (bkf_check2 chkb ctu gtu niter ctu gtu) ->
  birkhoff_check.

End BirkhoffCheck.

Lemma birkhoff2 : (birkhoff_check (1) (0)).
Proof. By Exists (1) (Seq (Cprog)). Qed.

Lemma birkhoff3 : (birkhoff_check (2) (0)).
Proof. By Exists (1) (Seq (Cprog Y)). Qed.

Lemma birkhoff4 : (birkhoff_check (3) (0)).
Proof. By Exists (4) (Seq (Cprog U) (Cprog 1 U)). Qed.

Lemma birkhoff5 : (birkhoff_check (4) (1)).
Proof.
By Exists (10) (Seq (Cprog U Y) (Cprog 1 U Y) (Cprog 2 U Y) (Cprog 3 U Y)
                    (Cprog 4 U Y) (Cprog H 4 Y Y Y)).
Qed.

Section Birkhoff.

Variable g : hypermap.
Hypothesis Hg: (minimal_counter_example g).

Local Hpg : (planar g) := Hg.
Local Hbg : (bridgeless g) := Hg.
Local HgE : (plain g) := Hg.
Local HgN : (cubic g) := Hg.
Local Hcg : (connected g) := Hg.
Local Hkg := (minimal_counter_example_is_noncolorable Hg).
Local Hmg := (minimal_counter_example_is_minimal Hg).
Local De2 := (plain_eq Hg).
Local He1 := (plain_neq Hg).
Local Dn3 := (cubic_eq Hg).

Section BirkhoffValid.

Variable n : nat.
Hypothesis Hn : (r : (seq g))
  (scycle rlink r) -> (leq (size r) n) -> (nontrivial_ring (0) r) = false.

Lemma birkhoff_valid : (m : nat) (birkhoff_check n m) ->
  (r : (seq g)) (scycle rlink r) -> (size r) = (S n) ->
    (nontrivial_ring m r) = false.
Proof.
Move=> m [nm cps ctu0 gtu0 basis chkb Hbk1 Hbk2].
Step Hchkb : (r : (seq g); HUr : (scycle rlink r))
    (size r) = (S n) -> (nontrivial_ring m r) ->
    (ctu : ctree) (chkb ctu) ->
       (EX et | (ring_trace (snipd_ring Hpg HUr) (ctrace et))
              & (negb (ctree_mem ctu (etrace et)))).
  Move=> r HUr Hrn Hrm ctu; Move: Hbk1 {Hbk2}; Rewrite: ~/chkb ~/basis.
  Elim: cps => [|cp cps Hrec] //=; Case/andP; Move/and3P=> [Hqcp Hkcp Hrcp] Hbk1.
  Case/orP; Auto; Move {cps Hbk1 Hrec} => Hctu.
  Def: Hcp := (cpmap_proper Hqcp).
  Pose gr := (cpmap cp); Pose bgr := (rotr (1) (rev (cpring gr))).
  Step Hbgr : (ufcycle (!node gr) bgr).
    Rewrite: /ucycle /bgr /rotr uniq_rot uniq_rev uniq_cpring.
    By Rewrite: cycle_rot cycle_rev_cpring.
  Pose gd := (snip_disk Hpg HUr); Pose bgd := (snipd_ring Hpg HUr).
  Step Hbgd : (sfcycle (!edge gd) bgd) By Exact (scycle_snipd_ring Hpg HUr).
  Step Hbgdr : (size bgd) = (size bgr).
    Rewrite: /bgr /rotr size_rot size_rev /gr size_ring_cpmap (eqP Hrcp) -Hrn.
    By Rewrite: -{2 r}(maps_snipd_ring Hpg HUr) size_maps.
  Def: Hpp := (sew_map_patch Hbgd Hbgr Hbgdr).
  Def: Hppr := (snip_patch Hpg HUr); Fold bgd in Hppr.
  Pose g' := (sew_map Hbgd Hbgr Hbgdr).
  Move: {}HgE {}HgN; Rewrite: (plain_patch Hppr) (cubic_patch Hppr).
  Move/andP=> [HgdE HgrrE]; Move/andP=> [HgdN HgrrN].
  Step Hpg' : (planar g').
    Rewrite: /planar /g' (genus_patch Hpp).
    Rewrite: (? =P (0) (cpmap_planar Hqcp)) addn0; Apply: planar_snipd.
  Step Hg'E : (plain g').
    By Rewrite: (plain_patch Hpp); Apply/andP; Split; RightBy Apply: cpmap_plain.
  Step Hg'N : (cubic g').
    Rewrite: (cubic_patch Hpp); Apply/andP; Split; LeftDone.
    Apply: (etrans (eq_subset ? ?) (cpmap_cubic Hqcp)) => [x].
    By Rewrite: /setC /bgr mem_rotr.
  Step Hbg' : (bridgeless g').
    Apply: (bridgeless_patch Hpp ? (cpmap_bridgeless Hqcp) ?).
      By Case (patch_bridgeless Hppr Hbg).
    Apply/idPn=> [Hch].
    Case: (ring_disk_chord Hg Hrm Hch) => [r' HUr' [Hr' Hrr']].
    By Rewrite: Hrn ltnS in Hrr'; Case/idP: (Hn HUr' Hrr').
  Step Hkg' : (four_colorable g').
    Apply Hmg; Try By Repeat Split; Try Apply cubic_precubic.
    Rewrite: ltnNge -(leq_add2l (size bgd)).
    Move: (card_patch Hpp) (card_patch Hppr); Rewrite: !size_maps -/g'.
    Rewrite: -/gd -/bgd; Move=> [ ] [ ]; Rewrite: leq_add2l -ltnNge -ltnS.
    Apply: (leq_trans Hkcp); Pose bgrr := (snipr_ring Hpg HUr).
    Step Ebgrr: (size bgrr) = (S n).
      By Rewrite: -Hrn -(size_rev r) -(maps_snipr_ring Hpg HUr) size_maps.
    Case Dbgrr: bgrr {}Ebgrr => // [bgrr0 bgrr'] _.
    Step Hbgrr: (ucycle_plain_quasicubic_connected bgrr).
      Split; LeftBy Split; [Split | Apply: ucycle_snipr_ring].
      By Apply: (patch_connected_r Hppr Hcg); Apply/set0Pn; Exists bgrr0.
    Move: (planar_snipr Hpg HUr); Rewrite: -/bgrr (quasicubic_Euler Hbgrr) Ebgrr.
    Rewrite: (patch_fcard_face_r Hppr) /outer -/gr.
    Move: (card (snip_rem Hpg HUr)) => ngrr.
    Pose arF := (setU (diskFC r) (fband r)).
    Step HarF: (fcard face arF) = (addn (S n) (fcard face (diskFC r))).
      Symmetry; Rewrite: -Hrn -(scycle_fcard_fband HUr) /n_comp -cardUI addnC.
      Rewrite: -(!eq_card g set0) ?card0.
        Apply: eq_card => [x]; Rewrite: /setI /arF /diskFC /setU /setD.
        By Case (fband r x); Rewrite: /= andbF ?orbF.
      Move=> x; Rewrite: /setI /diskFC /setD.
      By Case (fband r x); Rewrite: /= !andbF.
    Rewrite: Dbgrr -(eq_n_comp_r 2!arF) {mult}lock /=.
      Rewrite: -(leq_add2r (addn (double (S n)) (12))) !addSn; Case/eqP.
      Rewrite: -!lock HarF /= addnI double_addnn !addSn !addn0 !addnS !ltnS addn0.
      Rewrite: -addnA addnC -addn1 -!addnA !(addnCA (fcard face (diskFC r)) n).
      Rewrite: !leq_add2l add1n -addSn.
      Case/andP: Hrm => [_ Hrm]; Apply: (leq_add2 Hrm); Move/ltnW: Hrm => Hrm.
      By Repeat Apply: (leq_add2 Hrm). 
    Def: Ddgr := (codom_snipr Hpg HUr); Move=> x; Apply/idP/set0Pn.
      Rewrite: /arF /diskFC /setU /setD; Case Hx: (fband r x).
        Case: (hasP Hx) => [y Hy Hxy] _; Exists y.
        By Rewrite: /setI Hxy Ddgr /setC /diskE /setD Hy.
      Move=> HxN; Rewrite: /= orbF in HxN; Exists x; Rewrite: /setI connect0.
      By Rewrite: Ddgr /setC /diskE /setD (negbE HxN) andbF.
    Case; Move=> y; Move/andP=> [Hxy Hy]; Rewrite: Ddgr in Hy.
    Rewrite: /arF /diskFC /setU /setD.
    Case Hx: (fband r x); [By Rewrite orbT | Rewrite: /= orbF].
    Case HxF: (diskF r x).
      Rewrite: (closed_connect (diskF_face r) Hxy) in HxF.
      Case: (andP HxF) => [H HyN]; Case: {H}(elimN hasP H).
      Rewrite: /setC /diskE /setD HyN andbT negb_elim in Hy.
      By Exists y; RightBy Apply connect0.
    By Rewrite: /diskF /setD Hx /= in HxF; Rewrite: /setC HxF.
  Case: (colorable_patch Hpp) => [H _]; Case: {H}(H Hkg').
  Case/lastP => [|et e] Hetd Hetr.
    Case: Hetr => [k _ Det]; Move: (congr size Det).
    By Rewrite: /bgr size_trace size_maps size_rotr size_rev head_cpring.
  Step De: (sumt et) = e.
    Case: Hetd => [k _ Det]; Move: (congr sumt Det); Rewrite: sumt_trace /=.
    Rewrite: -{2 e}add0c; Case; Elim: et {Hetr Det} => [|e' et Hrec] /=.
      By Rewrite: addcC addc_inv.
    By Rewrite: Hrec addcA.
  Exists et; LeftBy Rewrite: /ctrace De.
  Apply: (negbI (ctree_mem_disjoint Hctu ?)) {Hetd}.
  Apply/(ctree_mem_cpcolor ? ?); Split; LeftBy Apply even_etrace.
  Rewrite: /etrace; Pose h := (etrace_perm et); Rewrite: sumt_permt De.
  Case: Hetr => [k Hk Det]; Exists (comp h k).
    Apply: (coloring_inj 2!h) Hk => //; Apply permc_inj.
  Rewrite: -/gr (maps_comp h k) -/(permt h) trace_permt.
  Rewrite: -(rev_rev (cpring gr)) maps_rev trace_rev.
  Rewrite: -(rot_rotr (1) (rev (cpring gr))) maps_rot trace_rot -/bgr -Det.
  By Rewrite: -rev_rotr rotr_rot -rev_rotr rev_rev rotr1_add_last.
Move=> r HUr Hrn; Apply/idP=> [Hrm].
Case Dn: n => [|n'].
  Case: (r) Hrn (andP HUr) => [|x [|x' r']]; Try By Rewrite Dn.
  By Move=> _ [H _]; Case: {H}(andP H); Rewrite: /rlink Sface (set0P Hbg x).
Def: HUr2 := (scycle_rev_ring Hg HUr).
Pose kv := [P](kempe_valid n' [et]~(P et) ctu0 Ctree_empty Gtree_empty gtu0).
Step Hkv0 : (kv (ring_trace (snipd_ring Hpg HUr)))
          /\ (kv (ring_trace (snipd_ring Hpg HUr2))).
  By Split; Rewrite: /kv /ctu0 /gtu0 Dn; Exact (kempe_valid_init ? ?).
Case/negPf: Hbk2; Move: Hrn Hrm HUr HUr2 Hkv0; Rewrite: ~/kv.
Elim: nm r ctu0 gtu0 {2 4}ctu0 {2 4}gtu0 => [|nm Hrec]; Auto.
Move=> r1 ctu1 gtu1 ctu2 gtu2 Hr1n Hr1m HUr1; Pose r2 := (rev_ring r1).
Move=> HUr2 [Hk1 Hk2] /=.
Step Hr2n : (size r2) = (S n) By Rewrite: /r2 /rev_ring size_rev size_maps.
Step Hr2m : (nontrivial_ring m r2) By Apply: (nontrivial_rev_ring Hg).
Def: Hcl1 := (!ring_disk_closed ? Hg Hpg ? HUr1 ? Hr1m HgN).
Def: Hcl2 := (!ring_disk_closed ? Hg Hpg ? HUr2 ? Hr2m HgN).
Case Det: (ctree_pick_rev ctu1 ctu2) => [|e et] //=.
Apply/andP=> [[Hck1 Hck2]]; Case Hkg.
Apply (!colorable_from_ring ? Hg Hpg ? HUr1 ? Hr1m (Adds e et)). 
  Case (decide_ring_trace (snipd_ring Hpg HUr1) (Adds e et)); Auto.
  Move=> Het; Move: Hck1 {Hck2}; Rewrite: /do_bkf_check2 {1 n}Dn /pred.
  Pose ctr := (ctree_of_ttail (etrace (belast e et))).
  Case Het0: (belast e et Color0); LeftDone.
  Case (!kempe_tree_closure_correct n'
          [et]~(ring_trace (snipd_ring Hpg HUr1) et) n ctu1 ctr gtu1).
    Apply: (kempe_valid_restrict [et'; Het']? Hk1).
    Case: {Het'}[H](esym (ctree_of_ttail_mem ? H Het')).
      By Rewrite: /etrace memc0_permt Het0.
    Rewrite: /etrace ctrace_permt {2}/permt size_maps; Split.
      Def: ge := (etrace_perm (belast e et)).
      Move/(Hcl1 ?)=> [Het' _]; Case: Het; Move: (Het' (inv_eperm ge)).
      Step [ ]: (Adds e et) = (ctrace (belast e et)).
        Def: Hets := (sumt_ctree_pick_rev ctu1 ctu2).
        Rewrite: Det in Hets; Rewrite: -(trace_untrace Color0 Hets) /trace /=.
        By Rewrite: (pairmap_scanl addc_inv).
      By Rewrite: /permt (monic_maps (inv_permc ge)).
    Case: {}Hk2 => [Hctu2 _]; Move: (size_ctree_pick_rev ctu1 Hctu2).
    By Rewrite: -Dn size_belast Det /set2 /= eqdSS; Move=> H; Rewrite (eqP H).
  Case: (kempe_tree_closure n' n ctu1 ctr gtu1) => [ctu' [gtr gtu']].
  Case: gtr=> // [] Hctu' _; Case/orP=> [Hck | Hck].
    Case: {Hchkb Hrec Hck}(Hchkb ? HUr1 Hr1n Hr1m ? Hck) => [et1 Het1 Hctu1].
    Step Hset1: (size et1) = (S n').
      Symmetry; Rewrite: -Dn -{n}/(pred (S n)) -Hr1n.
      Rewrite: -(maps_snipd_ring Hpg HUr1) size_maps.
      Case: Het1 => [k _ Det1]; Rewrite: -(size_maps k) -size_trace -Det1.
      By Rewrite: /ctrace size_add_last. 
    Case: (kempe_validP Hctu' Hset1 Hctu1 Hcl1 Het1) => [s H H']; Case (H H').
  Move: HUr1 {Hk1 Hcl1 Het} Hctu'; Rewrite: -(rev_rev_ring Hg r1) -/r2.
  Move=> HUr1 Hk1; Case/negPf: Hck; EApply (Hrec r2); Auto; Split; EAuto.
Case (decide_ring_trace (snipd_ring Hpg HUr2) (rev (Adds e et))).
  Rewrite: /rev_snipd_ring /rev_snipd_disk.
  By Rewrite: (bool_eqT (scycle_rev_ring Hg HUr1) HUr2).
Move=> Het; Move: Hck2 {Hck1}; Rewrite: /do_bkf_check2 {1 n}Dn /pred.
Pose ctr := (ctree_of_ttail (etrace (rev et))).
Case Het0: (rev et Color0); LeftDone.
Case (!kempe_tree_closure_correct n'
        [et]~(ring_trace (snipd_ring Hpg HUr2) et) n ctu2 ctr gtu2).
  Apply: (kempe_valid_restrict [et'; Het']? Hk2).
  Case: {Het'}[H](esym (ctree_of_ttail_mem ? H Het')).
    By Rewrite: /etrace memc0_permt Het0.
  Rewrite: /etrace ctrace_permt {2}/permt size_maps; Split.
    Def: ge := (etrace_perm (rev et)); Move/(Hcl2 ?) => [Het' _].
    Case: Het; Move: (Het' (inv_eperm ge)).
    Step []: (rev (Adds e et)) = (ctrace (rev et)).
      Step Hrets: (sumt (rev (Adds e et))) = Color0.
        Rewrite: -(rotr_rot (1) (rev (Adds e et))).
        Def: Hets := (sumt_ctree_pick_rev ctu1 ctu2).
        Rewrite: Det in Hets; Rewrite: -(trace_untrace Color0 Hets) -trace_rev.
        Rewrite: -(rot_rotr (1) (rev (untrace Color0 (Adds e et)))).
        By Rewrite: trace_rot rotr_rot sumt_trace.
      Rewrite: -(trace_untrace Color0 Hrets) rev_adds /untrace /=.
      By Rewrite: belast_add_last /trace /= (pairmap_scanl addc_inv).
    By Rewrite: /permt (monic_maps (inv_permc ge)).
  Case: (Hk2) => [Hctu2 _]; Move: (size_ctree_pick_rev ctu1 Hctu2).
  By Rewrite: -Dn size_rev Det /set2 /= eqdSS; Move=> H; Rewrite (eqP H).
Case: (kempe_tree_closure n' n ctu2 ctr gtu2) => [ctu' [gtr gtu']].
Case: gtr; Try Done; Move=> Hctu' _ H; Case: {H}(orP H) => [Hck | Hck].
  Case: {Hchkb Hrec Hck}(Hchkb ? HUr2 Hr2n Hr2m ? Hck) => [et2 Het2 Hctu2].
  Step Hset2: (size et2) = (S n').
    Symmetry; Rewrite: -Dn {(n)}(erefl (pred (S n))) -Hr2n.
    Rewrite: -(maps_snipd_ring Hpg HUr2) size_maps.
    Case: Het2 => [k _ Det2]; Rewrite: -(size_maps k) -size_trace -Det2. 
    By Rewrite: /ctrace size_add_last.
  Case: (kempe_validP Hctu' Hset2 Hctu2 Hcl2 Het2) => [s H H']; Case (H H').
By Case/negPf : Hck; EApply (Hrec r1); Auto; Split; EAuto.
Qed.

End BirkhoffValid.

Theorem birkhoff : (r : (seq g)) (leq (size r) (5)) -> (scycle rlink r) ->
  (nontrivial_ring (size r) =d (5) r) = false.
Proof.
Elim: {1 3}(5) (leqnn (5)) => [|n Hrec] Hn.
  Move=> [|x r] // _ _; Rewrite: /nontrivial_ring /n_comp eq_card0 //.
  By Move=> x; Rewrite: /setI andbC.
Move: {Hrec}(Hrec (ltnW Hn)) => Hrec.
Move=> r Hrn; Rewrite: leq_eqVlt in Hrn; Case/orP: Hrn; Auto.
Move=> Hrn Hr; Apply: (birkhoff_valid ? ? Hr (eqP Hrn)).
  Move{r Hrn Hr}=> r Hr Hrn; Rewrite: -(Hrec r Hrn Hr).
  By Rewrite: -ltnS in Hrn; Rewrite: eqn_leq andbC leqNgt (leq_trans Hrn Hn).
Rewrite: (eqP Hrn); Case: n Hrn Hn {Hrec} => [|n].
  Case: r Hr => [|x [|x' r']] //=.
  By Rewrite: /scycle /= /rlink Sface (set0P Hbg x).
Case: n => [|[|[|[|n]]]] _ // _.
Exact birkhoff2.
Exact birkhoff3.
Exact birkhoff4.
Exact birkhoff5.
Qed.

Lemma nontrivial_cycle2 : (x, y : g) let r = (seq2 x y) in
  (scycle rlink r) -> (negb (edge x) =d y) -> (nontrivial_ring (0) r).
Proof.
Move=> x y r HUr Hexy; Apply/(nontrivial0P ?); Split.
  Exists (node x); Rewrite: /diskF /setD -(fclosed1 (diskN_node r)).
  Rewrite: diskN_E /setU /= setU11 /= -{2 x}Enode -cface1r (set0P Hbg) /=.
  Case: (andP HUr); Move/and3P=> [Hxy Hyx _] _.
  Rewrite: Sface -(same_cface Hxy) -{(node x)}Enode -{1 x}Dn3.
  By Rewrite: cface1 Enode -cface1r (set0P Hbg).
Pose nex := (node (edge x)); Case Hnex: (fband r nex).
  Rewrite: /fband in Hnex; Case: (hasP Hnex) => [z Hz Hnexz].
  Rewrite: /= /setU1 orbF in Hz; Case/orP: Hz => [Dz | Dz].
    Rewrite: -{1 nex}Enode /nex -{1 x}Eface De2 Dn3 -cface1 Sface in Hnexz.
    By Rewrite: -(eqP Dz) cface1 (set0P Hbg) in Hnexz.
  Case: (andP HUr); Move/andP=> [Hxy _].
  Rewrite: Sface -(eqP Dz) -(same_cface Hxy) in Hnexz.
  By Rewrite: -{(edge x)}Enode -/nex -cface1 Sface (set0P Hbg) in Hnexz.
Exists nex; Rewrite: /diskFC /setD Hnex /= /setC /nex.
Rewrite: -(fclosed1 (diskN_node r)) diskN_E /setU.
Rewrite: -(fclosed1 (diskE_edge Hpg HUr)) /diskE /setD /= setU11 /= /setU1.
By Rewrite: eqd_sym He1 eqd_sym (negbE Hexy).
Qed.

Lemma double_dart : (x, y : g)
  (cface x y) -> (cface (edge x) (edge y)) -> x = y.
Proof.
Move=> /= x y HxyF Hexey; Apply: eqP; Apply/idPn=> [Hxy].
Step HUp: (scycle rlink (seq2 x (edge y))).
  By Rewrite: srcycleI //= Hexey De2 Sface.
Rewrite: -(inj_eqd (Iedge g)) in Hxy.
By Apply: (elimF idP (birkhoff ? HUp) (nontrivial_cycle2 HUp Hxy)).
Qed.

Section SpokeRing.

Variable x : g.

Local p : (seq g) := (orbit face x).

Remark Hpx : (p x). Proof. By Rewrite: /p -fconnect_orbit connect0. Qed.

Remark HUp : (ufcycle (!face?) p).
Proof. By Rewrite: /p /ucycle uniq_orbit (cycle_orbit (Iface g)). Qed.

Remark Ep : (cface x) =1 p. Proof. By Apply: fconnect_orbit. Qed.

Definition spoke [y : g] : g := (face (edge y)).

Lemma inj_spoke : (injective spoke).
Proof. Apply: (monic_inj 4!node); Apply: Eedge. Qed.

Definition spoke_ring : (seq g) := (maps spoke (rev p)).

Lemma mem_spoke_ring : (y : g) (spoke_ring y) = (cface x (node y)).
Proof.
Move=> y; Rewrite: /spoke_ring -{1 y}Enode -/(spoke (node y)).
By Rewrite: (mem_maps inj_spoke) mem_rev Ep.
Qed.

Syntactic Definition r := spoke_ring.
Syntactic Definition Er := mem_spoke_ring.

Lemma next_spoke_ring : (y : g) (r y) -> (next r y) = (face (spoke y)).
Proof.
Case: (andP HUp) => [Hp Up] y Hy.
Rewrite: /spoke_ring -{1 y}Enode -/(spoke (node y)).
Rewrite: (next_maps inj_spoke); RightBy Rewrite uniq_rev.
Rewrite: (next_rev Up) -(Eface g (prev p (node y))) /spoke De2.
By Rewrite: Er Ep in Hy; Rewrite: (eqP (prev_cycle Hp Hy)) -{1 y}Eedge Dn3.
Qed.

Lemma scycle_spoke_ring : (scycle rlink spoke_ring).
Proof.
Case: (andP HUp) => [Hp Up]; Apply/andP; Split.
  Apply cycle_from_next.
    By Rewrite: /spoke_ring (uniq_maps inj_spoke) ?uniq_rev.
  Move=> y Hy; Rewrite: (next_spoke_ring Hy) /rlink -cface1r; Apply: fconnect1.
Rewrite: /simple /spoke_ring !maps_rev uniq_rev -maps_comp /comp.
Step HpF: (sub_set p (cface x)) By Move=> y Hy; Rewrite Ep.
Elim: {p}(p) HpF {Hp} Up => [|y q Hrec] Hq //=; Move/andP=> [Hqy Uq].
Rewrite: ~{Hrec Uq}(Hrec [z; H](Hq z (setU1r ? H)) Uq) andbT.
Apply/mapsP=> [[z Hz Hyz]]; Case/idP: Hqy.
Rewrite: (!double_dart y z) //.
  Rewrite: -(same_cface (Hq ? (setU11 ? ?))); Exact (Hq ? (setU1r ? Hz)).
By Rewrite: cface1 cface1r; Apply/(rootP (Sface ?)).
Qed.

Syntactic Definition HUr := scycle_spoke_ring.

Lemma diskF_spoke_ring : (diskF spoke_ring) =1 (cface x).
Proof.
Move=> y; Symmetry; Apply/idP/idP.
  Move=> Hxy; Apply/andP; Split.
    Apply/hasP=> [[z1 Hz1 Hyz1]]; Rewrite: Er in Hz1.
    Case/idP: (set0P Hbg (node z1)).
    Rewrite: cface1r Enode -(same_cface Hz1); Exact (connect_trans Hxy Hyz1).
  Rewrite: /= -{1 y}Eedge -(fclosed1 (diskN_node r)) diskN_E /setU Er Eedge.
  By Rewrite Hxy.
Case/andP; Move=> Hy; Case/hasP=> [z Hz Hzy]; Case/connectP: Hzy Hy.
Pose z' := (finv node z); Rewrite: Er in Hz.
Step Hz': (r (face z')).
  By Rewrite: -(De2 z') Er Eedge -(Dn3 z') /z' (f_finv (Inode g)) cface1r Enode.
Move=> [|z'' q] Hq [].
  By Case/hasP=> /=; Exists (face z'); RightBy Apply fconnect1.
Move: Hq; Rewrite: /= {1}/dlink; Case (r z'); LeftDone.
Case/andP; Case/clinkP=> [Dz' | Dz''] Hq.
  Rewrite: -(f_finv (Inode g) z) (Inode g (etrans (Dn3 ?) Dz')) in Hz.
  Elim: q z'' {y z z' Hz' Dz'}Hz Hq  => [|z q Hrec] y Hy //=.
  Rewrite: {1}/dlink; Case: (r y) => //; Case/andP; Case/clinkP=> [Dy | Dz].
    Step Hz: (r z) By Rewrite: Er -Dy.
    Case: q {Hrec} => [|z' q]; RightBy Rewrite: /= /dlink Hz.
    By Rewrite: /= (subsetP (ring_fband r) ? Hz).
  By Apply: Hrec; Rewrite: -Dz -cface1r.
Rewrite Dz'' in Hz'; Case: q Hq => [|z''' q]; RightBy Rewrite: /= /dlink Hz'.
By Rewrite: /= (subsetP (ring_fband r) ? Hz').
Qed.

Lemma chordless_spoke_ring : (chordless spoke_ring).
Proof.
Apply/subsetP=> [y1 Hy1]; Apply/set0Pn=> [[y2]]; Case/andP.
Move/adjP=> [z Hz1 Hz2]; Rewrite: /rlink in Hz2; Move/and3P=> [Hry12 Hry21 Hy2].
Pose q := (seq3 (node y2) (edge z) (edge (node y1))).
Step HUq: (scycle rlink q).
  Rewrite: srcycleI //= !De2 cface1 Enode Sface Hz2 /= andbC.
  Rewrite: cface1r Enode Sface Hz1 /= Sface; Rewrite: !Er in Hy1 Hy2.
  By Rewrite: -!(same_cface Hy2) !(same_cface Hy1) connect0 (set0P Hbg).
Apply: (elimF idP (birkhoff ? HUq) ?); LeftDone.
Apply/(nontrivial0P ?); Split.
  Pose t := (node (edge (node y1))); Exists t; Rewrite: /diskF /setD /=.
  Step Dt: t = (prev r y1).
    Case: (andP HUr) =>[_ Ur]; Rewrite: /t -{1 y1}(next_prev (simple_uniq Ur)).
    By Rewrite: next_spoke_ring ?mem_prev // Eface /spoke Eedge.
  Rewrite Er in Hy2; Rewrite: Sface -(same_cface Hy2).
  Step Ht: (cface x (node t)) By Rewrite: -Er Dt mem_prev.
  Rewrite: (same_cface Ht) -{2 t}Enode -cface1r (set0P Hbg).
  Rewrite: Sface (same_cface Hz2) Sface /= orbC.
  Rewrite: -{(edge (node y1))}Enode -cface1r (set0P Hbg).
  Rewrite: {2}/t -(fclosed1 (diskN_node q)) diskN_E /setU /= /setU1 set11.
  Rewrite: /= !orbT andbT; Apply/idP=> [Hy2t]; Case/eqP: Hry21.
  By Rewrite: -Dt; Apply (scycle_cface HUr); Rewrite: ?Er.
Exists (node (node y1)); Rewrite: /diskFC /setD /= /setC.
Rewrite: andbC -(fclosed1 (diskN_node q)) -{1 (node y1)}De2.
Rewrite: (diskN_edge_ring Hg) /= /setU1 ?set11 /= ?orbT //.
Rewrite: !Er in Hy1 Hy2.
Rewrite: Sface -(same_cface Hy2) (same_cface Hy1) -{1 (node y1)}Enode -cface1.
Rewrite: Sface (set0P Hbg) /= orbF orbC -{(node (node y1))}Enode Dn3.
Rewrite: -cface1 Sface cface1 Enode (set0P Hbg) /= cface1 -/(spoke y1).
Rewrite: -next_spoke_ring; RightBy Rewrite: Er.
Apply/idP=> [Hy2t]; Case/eqP: Hry12.
By Apply (scycle_cface HUr); Rewrite: ?mem_next ?Er // (same_cface Hy2t).
Qed.

Lemma size_spoke_ring : (size spoke_ring) = (arity x).
Proof. By Rewrite: /spoke_ring size_maps size_rev /p /orbit size_traject. Qed.

Lemma min_arity : (ltn (4) (arity x)).
Proof.
Rewrite: /= -size_spoke_ring ltnNge; Apply/idP=> [HrF].
Case HrFC: (negb (set0b (diskFC r))).
  Apply: (elimF idP (birkhoff ? HUr) ?); LeftBy Apply ltnW.
  Case: ((size r) =P (5)) => [Hr5 | _]; LeftBy Rewrite Hr5 in HrF.
  Apply/(nontrivial0P ?); Split; RightBy Exact (set0Pn HrFC).
  By Exists x; Rewrite: diskF_spoke_ring connect0.
Move: {HrFC}(set0P (negbEf HrFC)) => HrFC.
Case Hkg.
Exists [y](if (cface x y) then Color0 else
           let i = (find (cface y) r) in
           if (andb i =d (2) (size r) =d (3)) then Color3 else
           if (set2 (0) (2) i) then Color1 else Color2).
Split; Move=> y; Rewrite: /invariant;
  RightBy Rewrite: -cface1r -(eq_find (cface1 y)) set11.
Pose i1 := (find (cface y) r); Pose i2 := (find (cface (edge y)) r).
Case Hxy: (cface x y).
  Rewrite: (same_cface Hxy) (set0P Hbg).
  By Case (andb i2 =d (2) (size r) =d (3)); RightBy Case (set2 (0) (2) i2).
Case Hxey: (cface x (edge y)).
  By Case (andb i1 =d (2) (size r) =d (3)); RightBy Case (set2 (0) (2) i1).
Case Hy: (fband r y);
  RightBy Rewrite: -diskF_spoke_ring /diskF /setD Hy /= in Hxy;
  Move: (HrFC y); Rewrite: /diskFC /setD Hy /setC Hxy.
Case Hey: (fband r (edge y));
  RightBy Rewrite: -diskF_spoke_ring /diskF /setD Hey /= in Hxey;
  Move: (HrFC (edge y)); Rewrite: /diskFC /setD Hey /setC Hxey.
Pose z1 := (sub x r i1); Pose z2 := (sub x r i2).
Step Hz12: (adj z1 z2).
  Apply/adjP; Exists y; LeftBy Rewrite: Sface; Exact (sub_find x Hy).
  Exact (sub_find x Hey).
Rewrite: /fband has_find -/i1 in Hy; Rewrite: /fband has_find -/i2 in Hey.
Step Hz1: (r z1) By Rewrite: /z1 (mem_sub x Hy).
Step Hz2: (r z2) By Rewrite: /z2 (mem_sub x Hey).
Move: (set0P (subsetP chordless_spoke_ring ? Hz1) z2) {Hz1}.
Case: (andP HUr); Move=> Hr; Move/simple_uniq=> Ur.
Rewrite: /setI /setD1 ~Hz12 ~Hz2 (monic2F_eqd (prev_next Ur)) -(eqd_sym z2).
Step Hpri: (i, i' : nat) (ltn i (size r)) -> (ltn i' (size r)) ->
           ((sub x r i') =d (prev r (sub x r i)))
              = (i' =d (pred if i =d (0) then (size r) else i)).
  Move=> i i' Hi Hi'; Pose z := (sub x r i).
  Cut (index (prev r z) r) = (pred if i =d (0) then (size r) else i).
    Case; Apply/eqP/eqP; LeftBy Case; Rewrite (index_uniq x Hi' Ur).
    By Move=> Di'; Rewrite: Di' sub_index // mem_prev /z mem_sub.
  Rewrite: prev_sub ~/z mem_sub // ~{i' Hi'}.
  Case Dr: r Ur Hi => [|x0 r'] Ur //.
  Rewrite: index_uniq //; RightBy Rewrite: /= ltnS index_size.
  Simpl in Ur; Case/andP: Ur => [Hx0 Ur'].
  Case: i => [|i] Hi; Rewrite: /= ?index_uniq //.
  By Rewrite: -{1 r'}cats0 index_cat (negbE Hx0) /= addn0.
Rewrite: ~/z1 ~/z2 !~Hpri //.
Case Dn: (size r) HrF Hy Hey => [|[|n]] //.
  Case: {}r {}HUr Dn => [|x0 [|x1 r']] //. 
  By Rewrite: /scycle /= andbT /rlink Sface (set0P Hbg).
By Case: i1 i2 n {Dn} => [|[|[|[|i1]]]] [|[|[|[|i2]]]] [|[|[|n]]].
Qed.

Lemma fband_spoke_ring : (fband r) =1 (adj x).
Proof.
Move=> y; Apply/hasP/adjP=> [[z Hxz Hzy]].
  Exists (node z); LeftBy Rewrite: -mem_spoke_ring.
  By Rewrite: /rlink cface1 Enode Sface.
Exists (face (edge z)); RightBy Rewrite: -cface1r Sface.
By Rewrite: mem_spoke_ring Eedge.
Qed.

Lemma adj11_edge : (y : g) (adj x y) -> (adj x (edge y)) ->
  (orb (r y) (r (edge y))).
Proof.
Move=> y; Rewrite: -!fband_spoke_ring.
Move/hasP=> [z Hrz Hyz]; Move/hasP=> [z' Hrz' Heyz']; Apply/norP=> [[Hry Hrey]].
Case/andP: (set0P (subsetP chordless_spoke_ring ? Hrz) z'); Split.
  By Apply/adjP; Exists y; LeftBy Rewrite Sface.
Case: (andP HUr); Clear; Move/simple_uniq=> Ur.
Rewrite: /setD1 Hrz' andbT (monic2F_eqd (next_prev Ur)) !next_spoke_ring //.
Apply/andP; Split; Apply/eqP=> [Dz].
  Rewrite: -Dz /spoke -!cface1r in Heyz'.
  By Rewrite: (double_dart Hyz Heyz') Hrz in Hry.
Rewrite: Dz /spoke -!cface1r -{1 y}De2 in Hyz.
By Rewrite: (double_dart Heyz' Hyz) Hrz' in Hrey.
Qed.

Lemma fcard_adj_adj : (y : g) (adj x y) ->
  (fcard face (setI (adj y) (adj x))) = (2).
Proof.
Move=> y Hy; Def: Hry := Hy; Rewrite: -fband_spoke_ring in Hry.
Case/hasP: Hry => [y' Hy' Hyy'].
Rewrite: /n_comp (cardD1 (froot face (next r y'))).
Rewrite: (cardD1 (froot face (prev r y'))).
Rewrite: {1}/setD1 {1 2 3 4}/setI !(roots_root (Sface g)).
Step Hra: (z : g) (r z) -> (adj x z).
  By Move=> z; Rewrite: Er; Move=> Hnxz; Rewrite: (adjF Hnxz) adjN.
Pose z := (prev r y'); Step Hz: (r z) By Rewrite: /z mem_prev.
Pose z' := (next r y'); Step Hz': (r z') By Rewrite: /z' mem_next.
Rewrite: -![z : g](adjFr (connect_root ? z)) !Hra //.
Case: (andP HUr); Move=> Hr; Move/simple_uniq=> Ur.
Rewrite: !(adjF Hyy') (rlink_adj (next_cycle Hr Hy')).
Rewrite: Sadj // (rlink_adj (prev_cycle Hr Hy')) /=.
Rewrite: (sameP eqP (rootPx (Sface g) z' z)).
Case Hz'z: (cface z' z).
  Case: (rot_to Hz) {}min_arity (cycle_next Ur) {}Ur => [i r' Dr].
  Rewrite: -size_spoke_ring -(size_rot i) -(cycle_rot i) -(uniq_rot i) Dr.
  Case: r' {Dr} => [|y'' [|z'' r']] // _; Move/and3P=> [Dy'' Dz'' _].
  Case/andP; Case/orP; Right; Apply/setU1P; Left.
  Rewrite: -(eqP Dz'') -(eqP Dy'') {1}/z (next_prev Ur) -/z'.
  By Apply: (scycle_cface HUr).
Apply: eqP; Apply/set0Pn=> [[t]]; Move/and5P=> [Hzt Hz't Ht Hyt Hxt].
Rewrite: -(eqP Ht) (sameP eqP (rootPx (Sface?) z t)) in Hzt.
Rewrite: -~{Ht}(eqP Ht) (sameP eqP (rootPx (Sface?) z' t)) in Hz't.
Rewrite: -fband_spoke_ring in Hxt; Case/hasP: Hxt => [t' Ht' Htt'].
Case/andP: (set0P (subsetP chordless_spoke_ring ? Hy') t'); Split.
  By Rewrite: -(adjF Hyy') -(adjFr Htt').
Rewrite: /setD1 Ht' andbT; Apply/andP; Split; Apply/eqP=> [Dt'].
  By Rewrite: Sface (same_cface Htt') -Dt' -/z' connect0 in Hz't.
By Rewrite: Sface (same_cface Htt') -Dt' -/z connect0 in Hzt.
Qed.

Definition adj01 [y, z : g] : bool := (orb (cface y z) (adj y z)).

Lemma adj12_edge : (y, z : g) (adj x y) -> (adj x z) -> (adj z (edge y)) ->
  (orb (adj01 z y) (adj01 x (edge y))).
Proof.
Move=> y z0; Rewrite: -2!fband_spoke_ring.
Move/hasP=> [y' Hry' Hyy']; Move/hasP=> [z Hrz Hz0z].
Move/adjP=> [z' Hzz' Heyz']; Rewrite: /rlink Sface in Heyz'.
Apply/norP; Case; Move/norP=> [Hzy Hazy]; Move/norP=> [Hxey Haxey].
Rewrite: !(same_cface Hz0z) in Hzy Hzz'; Rewrite: ~{z0 Hz0z}(adjF Hz0z) in Hazy.
Pose q := (Adds y (seq3 (edge z') (edge (node z)) (node y'))).
Step HUq: (scycle rlink q).
  Rewrite: srcycleI //= Heyz' cface1r Enode Sface Hzy !De2 /=.
  Rewrite: (same_cface Hyy') Sface (adj_no_cface Hbg (adjN y')) /=.
  Rewrite: !Er in Hry' Hrz.
  Rewrite: cface1r Enode Sface Hzz' -(same_cface Heyz') Sface -(same_cface Hry').
  By Rewrite: Hxey -(same_cface Hrz) Hry' cface1 Enode Sface Hyy'.
Apply: (elimF (nontrivial0P ?) (birkhoff ? HUq) ?); [Done | Split].
  Exists (node (node y')); Rewrite: /diskF /setD -(fclosed1 (diskN_node q)).
  Rewrite: diskN_E /setU /= /setU1 set11 /= !orbT andbT.
  Rewrite: Sface (same_cface Hyy') -{2 4 y'}Eedge Dn3.
  Rewrite: -cface1r (set0P Hbg) Sface -(same_cface Heyz') (no_adj_adj Haxey).
    Rewrite: -cface1 Sface cface1 Enode.
    Rewrite: Sadj // in Hazy; Rewrite: (no_adj_adj Hazy).
      By Rewrite: adj_no_cface ?adjN. 
    By Rewrite: (adjF Hyy') adjE.
  By Rewrite: Er in Hry'; Rewrite: (adjF Hry') Sadj ?adjN.
Exists (node (node z)).
Rewrite: /diskFC /setD /setC -(fclosed1 (diskN_node q)).
Rewrite: -{2 (node z)}De2 (diskN_edge_ring Hg) //= /setU1 ?set11 ?orbT //.
Rewrite: andbT orbF -{1 3 z}Eedge Dn3 -cface1.
Rewrite: Sface (no_adj_adj Hazy (adjE z)).
Rewrite: !Er in Hry' Hrz.
Rewrite: Sface -(same_cface Heyz') (no_adj_adj Haxey).
  Rewrite: -cface1 Sface cface1 Enode (set0P Hbg) Sface -(same_cface Hry').
  By Rewrite: (same_cface Hrz) -{1 (node z)}Enode -cface1 Sface (set0P Hbg).
By Rewrite: (adjF Hrz) Sadj ?adjN.
Qed.

Lemma fcard_adj_max : (y : g)
  (negb (cface x y)) -> (leq (fcard face (setI (adj y) (adj x))) (2)).
Proof.
Move=> y Hxy0; Case Hxy: (adj01 x y).
  By Rewrite: /adj01 (negbE Hxy0) in Hxy; Rewrite (fcard_adj_adj Hxy).
Rewrite: ~{Hxy0}leqNgt /n_comp; Apply/idP=> [Hy3].
Def: Hy1 := (ltnW (ltnW Hy3)); Rewrite: ltnNge leqn0 in Hy1.
Case/set0Pn: Hy1 => [z1 Hz1]; Rewrite: (cardD1 z1) Hz1 /= in Hy3.
Def: Hy2 := (ltnW Hy3); Rewrite: add1n ltnS ltnNge leqn0 in Hy2.
Case/set0Pn: Hy2 => [z2 Hz2]; Rewrite: (cardD1 z2) Hz2 /= in Hy3.
Rewrite: !add1n !ltnS ltnNge leqn0 in Hy3; Case/set0Pn: Hy3 => [z3 Hz3].
Case/and3P: Hz1 => [Hz1 Hyz1 Hxz1]. 
Case/and4P: Hz2 => [Hz12 Hz2 Hyz2 Hxz2]. 
Case/and5P: Hz3 => [Hz23 Hz13 Hz3 Hyz3 Hxz3]. 
Step Hyz: (z, z' : g) (negb z =d z') ->
          (froots face z) -> (froots face z') ->
          (adj x z) -> (adj x z') -> (adj y z) -> (adj y z') -> (adj z z').
  Move=> z z' Hzz' Hz Hz' Hxz Hxz' Hyz; Move/adjP=> [z'' Hyz'' Hz''z'].
  Rewrite: -(adjFr Hz''z') in Hxz'.
  Rewrite: (adjF Hyz'') Sadj // -{z''}De2 in Hyz.
  Move: (adj12_edge Hxz' Hxz Hyz).
  Rewrite: De2 orbC /adj01 -(adjFr Hyz'') (Sface ? x).
  Rewrite: -(same_cface Hyz'') Sface -/(adj01 x y) Hxy.
  Rewrite: Sface (same_cface Hz''z') Sface.
  Rewrite: (sameP (rootPx (Sface ?) z z') eqP) (eqP Hz) (eqP Hz') (negbE Hzz').
  By Rewrite: (adjFr Hz''z').
Step Hz123: (and3 (adj z1 z2) (adj z1 z3) (adj z2 z3)) By Split; Auto.
Move: {y Hxy Hz1 Hyz1 Hz12 Hz2 Hyz2 Hz13 Hz23 Hz3 Hyz3 Hyz} Hxz1 Hxz2 Hxz3.
Rewrite: -!fband_spoke_ring; Move/hasP=> [t1 Ht1 Hzt1].
Move/hasP=> [t2 Ht2 Hzt2]; Move/hasP=> [t3 Ht3 Hzt3].
Move: Hz123; Rewrite: !(adjF Hzt1) (adjF Hzt2) (adjFr Hzt2) !(adjFr Hzt3).
Move{z1 z2 z3 Hzt1 Hzt2 Hzt3}=> [Ht12 Ht13 Ht23].
Case: (andP HUr); Clear; Move/simple_uniq=> Ur.
Step Hrt: (t, t' : g) (adj t t') -> (r t) -> (r t') ->
           ~ (next r t) = (next r t') /\ ((next r t) = t' \/ (next r t') = t).
  Move=> t t' Htt' Ht Ht'; Split.
    Move=> Dt'; Move: (adj_no_cface Hbg Htt').
    By Rewrite: (monic_inj (prev_next Ur) Dt') connect0.
  Move: (set0P (subsetP chordless_spoke_ring ? Ht) t').
  Rewrite: /setI /setD1 Htt' Ht' andbT -negb_orb.
  By Case/orP; Case/eqP; Auto; Right; Apply next_prev.
Case: {Ht12}(Hrt ? ? Ht12 Ht1 Ht2) => [Ht12 Dt12].
Case: {Ht13}(Hrt ? ? Ht13 Ht1 Ht3) => [Ht13 Dt13].
Case: {Hrt Ht23}(Hrt ? ? Ht23 Ht2 Ht3) => [Ht23 Dt23].
Case: (rot_to Ht1) (min_arity) (cycle_next Ur) (Ur) => [i r' Dr].
Rewrite: -size_spoke_ring -(size_rot i) -(cycle_rot i) -(uniq_rot i) Dr.
Case: r' {Dr} => [|u2 [|u3 [|u4 r']]] //= _; Move/and4P=> [Du2 Du3 Du4 _].
Case/andP; Do 2 (Case/norP; Clear); Case/norP; Case/eqP.
Rewrite: -(eqP Du4) -(eqP Du3) -(eqP Du2) ~{u2 u3 u4 Du2 Du3 Du4}.
Case: Dt12 => [Dt2 | Dt1].
  Case: Dt23 => [Dt3 | Dt2']; RightBy Case Ht13; Rewrite: Dt2 Dt2'.
  Case: Dt13 => [Dt3' | Dt1]; LeftBy Case Ht12; Rewrite: Dt3 Dt3'.
  By Rewrite: Dt2 Dt3 Dt1.
Case: Dt13 => [Dt3 | Dt1']; RightBy Case Ht23; Rewrite: Dt1 Dt1'.
Case: Dt23 => [Dt3' | Dt2]; LeftBy Case Ht12; Rewrite: Dt3 Dt3'.
By Rewrite: Dt3 Dt2 Dt1.
Qed.

End SpokeRing.

Definition minimal_counter_example_is_plain_cubic_pentagonal :
  (plain_cubic_pentagonal g).
Split; [Exact Hg | Exact min_arity]. Defined.

End Birkhoff.

Syntax constr level 0:
  map_spoke_pp [(spoke 1!$_)] -> [ "spoke" ].

Grammar constr constr0 : constr :=
  map_spoke ["spoke"] -> [(!spoke ?)].

Coercion minimal_counter_example_is_plain_cubic_pentagonal :
  minimal_counter_example >-> plain_cubic_pentagonal.
 
Unset Implicit Arguments.
