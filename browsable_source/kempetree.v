(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require tacticext.
Require funs.
Require boolprop.
Require dataset.
Require natprop.
Require dyck.
Require seq.
Require paths.
Require connect.
Require hypermap.
Require geometry.
Require color.
Require chromogram.
Require coloring.
Require cfmap.
Require cfcolor.
Require ctree.
Require initctree.
Require gtree.
Require initgtree.
Require gtreerestrict.
Require ctreerestrict.

Set Implicit Arguments.

(* Here we put all the reducibility steps together, to compute the   *)
(* Kempe closure tree of a configuration, which we can use to test   *)
(* directly for D-reducibility. A bit more work will be required for *)
(* C-reducibility.                                                   *)

Fixpoint ctree_size [t : ctree] : nat :=
  Cases t of
    (Ctree_node t1 t2 t3) =>
       (addn (ctree_size t1) (addn (ctree_size t2) (ctree_size t3)))
  | (Ctree_leaf _) => (1)
  | Ctree_empty => (0)
  end.

Lemma ctree_size_partition : (t, t', t'' : ctree)
  (Hpt : (ctree_partition t (Ctree_pair t' t'')))
  (ctree_size t) = (addn (ctree_size t') (ctree_size t'')).
Proof.
Def: Epp := [st](addnCA (ctree_size st)).
Step Esz0: (t : ?; Ht : (et : ?)(ctree_mem t et) = false) (ctree_size t) = (0).
  Elim=> [t1 Hrec1 t2 Hrec2 t3 Hrec3|lf Hr|] Ht //=.
    Def: Hte := [e; et](Ht (Adds e et)); Rewrite: (Hrec1 (Hte Color1)).
    By Rewrite: (Hrec2 (Hte Color2)) (Hrec3 (Hte Color3)).
  By Case/idP: (Ht seq0).
Simpl; Elim.
  Move=> t1 Hrec1 t2 Hrec2 t3 Hrec3 t' t'' Ht.
    Move: {Ht}(Ht seq0) [e;et](Ht (Adds e et)).
    Case: t' => [t1' t2' t3'|lf|] //.
      Case: t'' => [t1'' t2'' t3''|lf|] // _ Hte.
        Rewrite: /= (Hrec1 ? ? (Hte Color1)).
        Rewrite: (Hrec2 ? ? (Hte Color2)) (Hrec3 ? ? (Hte Color3)).
        By Rewrite: -!addnA (Epp t1'') (Epp t2'') (Epp t1'').
      Rewrite: /= (Hrec1 ? Ctree_empty (Hte Color1)).
      Rewrite: (Hrec2 ? Ctree_empty (Hte Color2)).
      By Rewrite: (Hrec3 ? Ctree_empty (Hte Color3)) /= !addn0.
    Case: t'' => [t1'' t2'' t3''|lf|] // _ Hte.
      Rewrite: /= (Hrec1 Ctree_empty ? (Hte Color1)).
      Rewrite: (Hrec2 Ctree_empty ? (Hte Color2)).
      By Rewrite: (Hrec3 Ctree_empty ? (Hte Color3)).
    Rewrite: /= (Hrec1 Ctree_empty Ctree_empty (Hte Color1)).
    Rewrite: (Hrec2 Ctree_empty Ctree_empty (Hte Color2)).
    By Rewrite: (Hrec3 Ctree_empty Ctree_empty (Hte Color3)).
  Move=> lf _ t' t'' Ht.
    Case Dt': t' Ht => [t1' t2' t3'|lf'|] Ht.
      Move: {Ht} (Ht seq0) [e;et](Ht (Adds e et)).
        Case: t'' => [t1'' t2'' t3''|lf''|] Htn //.
        Rewrite: -Dt'; Move=> Hte; Rewrite: (Esz0 t') //.
        By Move=> [|e et]; [Rewrite Dt' | Rewrite: -(Hte e et) /= orbC].
      Rewrite: addnC (Esz0 t'') //; Move=> et; Rewrite: -(Ht et).
      By Case (ctree_mem t'' et); Case et.
    By Case: t'' {Ht}(Ht seq0).
Move=> /= t' t'' Ht; Rewrite: (Esz0 t') ?(Esz0 t'') //;
  By Move=> et; Case (orb_false_elim ? ? (Ht et)).
Qed.

Lemma ctree_size_proper : (h : nat; t : ctree)
  (Ht : (ctree_proper h t)) (ctree_size t) = (0) -> t = Ctree_empty.
Proof.
Elim=> [|h Hrec] [t1 t2 t3|lf|] //= [Hne Ht1 Ht2 Ht3] Hzt; Move: Hzt Hne.
Case Hzt1: (ctree_size t1); [Rewrite (Hrec ? Ht1 Hzt1) | Done].
Case Hzt2: (ctree_size t2); [Rewrite (Hrec ? Ht2 Hzt2) | Done].
By Case Hzt3: (ctree_size t3); LeftBy Rewrite (Hrec ? Ht3 Hzt3).
Qed.

Fixpoint exp3 [n : nat] : nat :=
  Cases n of (0) => (1) | (S n') => (mult (3) (exp3 n')) end.

Lemma ctree_max_size_proper : (h : nat; t : ctree)
  (Ht : (ctree_proper h t)) (leq (ctree_size t) (exp3 h)).
Proof.
Elim=> [|h Hrec] [t1 t2 t3|lf|] //= [_ Ht1 Ht2 Ht3]; Rewrite: !addnI addn0.
Move: (leq_add2); Auto.
Qed.

Section KempeTreeClosure.

Variable h : nat.
Local ktc_result : Set := ctree * gtree_pair.
Local ktc_fun : Set := (ctu, ctr : ctree) gtree -> ktc_result.
Definition ktc_step [closure : ktc_fun; kr : ktc_result] : ktc_result :=
  let (ctu, gtp) = kr in if (ctree_empty ctu) then kr else
  let (gtr, gtu) = gtp in if (gtree_empty gtr) then kr else
  if (gtree_empty gtu) then (Ctree_empty, empty_gtree_pair) else
  let (ctu', ctr) = (ctree_restrict h ctu (Ctr_some Bstack0 gtr Ctr_none)) in
  (closure ctu' (ctree_rotlr ctr) gtu).
Definition ktc_step2c [step : ktc_result -> ktc_result] : ktc_fun -> ktc_fun :=
  [closure; ctu, ctr; gtu](step (step (closure ctu ctr gtu))).
Definition ktc_dostep2c [closure : ktc_fun] : ktc_fun :=
  (ktc_step2c (ktc_step closure) closure).
Fixpoint kempe_tree_closure [d : nat] : ktc_fun :=
  Cases d of
    (S d') =>
      (ktc_dostep2c (kempe_tree_closure d'))
  | (0) =>
      [ctu, ctr; gtu]
      (ctu, (gtree_restrict gtu (Gtr_some Bstack0 ctr Gtr_none)))
  end.

Variable P : colseq -> Prop.

Definition kempe_valid [ctu, ctr : ctree; gtr, gtu : gtree] : Prop :=
     (ctree_proper (S h) ctu)
  /\ ((et : colseq)
      (ctree_sub ctu et) =
        (if (negb (even_trace et)) then (0) else
         (addn (gtree_sub gtr Bstack0 et) (gtree_sub gtu Bstack0 et))))
  /\ ((et : colseq; Het : (ctree_mem ctr et))
      (kempe_coclosure P (ctrace et)) /\ (size et) = (S h))
  /\ ((w : chromogram; Hw : (gtree_mem gtr w))
      ~(gtree_mem gtu w) /\ (init_gtree_spec (S h) w))
  /\ ((w : chromogram; Hw : ~(gtree_mem gtu w); Hcw: (init_gtree_spec (S h) w))
      (EX et | (kempe_coclosure P (ctrace et)) & (matchpg Bstack0 et w)))
  /\ ((w : chromogram; Hw : (gtree_mem gtu w)) (init_gtree_spec (S h) w)).

Definition kempe_complete
   [sz : nat; ctu, ctr : ctree; gtr, gtu : gtree] : Prop :=
    ( (ltn (ctree_size ctu) sz)
     \/ ctr = Ctree_empty /\ (w : chromogram) ~(gtree_mem gtr w) )
  /\ ((et : colseq)
      (Het : (P (ctrace et))
           \/ (EX e | ~(ctree_mem ctu (permt (edge_rot e) (etrace et)))))
      (ctree_mem ctr (etrace et)) \/ (gtree_sub gtu Bstack0 et) = (0)).

Local ktr_prop [ktr : ktc_result; P] : Prop :=
  let (ctu, gtp) = ktr in let (gtr, gtu) = gtp in (P ctu Ctree_empty gtr gtu).

Theorem kempe_tree_closure_correct : (d : nat; ctu, ctr : ctree; gtu : gtree)
  let ktrp = (ktr_prop (kempe_tree_closure d ctu ctr gtu)) in
     (kempe_valid ctu ctr Gtree_empty gtu) -> (ktrp kempe_valid)
  /\ (sz : nat) (kempe_complete (addn (exp3 d) sz) ctu ctr Gtree_empty gtu)
        -> (ktrp (kempe_complete (S sz))).
Proof.
Elim=> [|d Hrec].
  Move=> ctu ctr gtu; Hnf; Move=> [Hctu [Ectu [Hctr [Hgte [Hgtu Hclg]]]]] /=.
  Def Dctrr: ctrr := (Gtr_some Bstack0 ctr Gtr_none).
  Move: (gtree_restrict_partition gtu ctrr) (gtree_mem0_restrict gtu ctrr).
  Case: (gtree_restrict gtu ctrr) => [gtr gtu'] /=.
  Move=> Hgtp Hgtr; Split.
    Split; [Done | Split].
      Move=> et; Rewrite (Ectu et); Case: (even_trace et) => //=.
      Rewrite: gtree_sub_empty; Exact (match_count_partition Hgtp ? ?).
    Split; [Done | Split].
      Move=> w Hwr; Case: (esym Hwr) (esym (Hgtr w)) {Hgtp}(elimF idP (Hgtp w)).
      Case/andP=> [Hwu _]; Rewrite: Hwu /=.
      By Case: (gtree_mem gtu' w); [Case | Split; RightBy Apply: Hclg].
    Split; [Move=> w Hwu' Hcw | Idtac].
      Case Hwu: (gtree_mem gtu w) (Hgtp w); RightBy Move/idP: Hwu; Auto.
      Case Hwr: (gtree_mem gtr w); RightBy Rewrite (introF idP Hwu').
      Clear; Rewrite: ~Hgtr ~Hwu ~Dctrr /= orbF in Hwr.
      Case: (xmatchP Hwr) {Hcw}(andP Hcw) => [et Het Hm] [Hsw Hbw].
      By Case: (Hctr ? Het); Exists et.
    Move=> w Hw; Apply Hclg; Apply/negPf=> [Hwu].
    By Case/idP: (Hgtp w); Rewrite: Hw Hwu orbC.
  Move=> sz [Hsz Hcl]; Split.
    Case: Hsz => [Hsz | [Dctr Egte]]; [Left | Right; Split]; Trivial.
    Move=> w; Rewrite: Hgtr andb_sym Dctrr Dctr /=.
    By Rewrite: [bs;st](introF (has_matchP bs st w)) //; Case.
  Move=> et Het; Right; Symmetry; Apply: (eqP (negbEf ?)).
  Apply/nmatchP=> [[w Hw Hm]]; Case/idP: (Hgtp w); Rewrite: Hw Hgtr Dctrr /=.
  Case Hwu: (gtree_mem gtu w); Rewrite: //= orbF eqbE.
  Case: {Hcl Het} (Hcl ? Het) => [Het | Het].
    Rewrite: -matchpg_etrace in Hm.
    By Apply/eqP; Apply/(has_matchP ? ? ?); Exists (etrace et).
  Case (elimF (match_countP (gtree_mem gtu) Bstack0 et)); RightBy Exists w.
  By Rewrite: /gtree_sub in Het; Rewrite Het.
Simpl; Move: (kempe_tree_closure d) Hrec => ktc' Hktc'.
Cut (ktr : ktc_result)
    let ktrp = (ktr_prop ktr) in let ktrp' = (ktr_prop (ktc_step ktc' ktr)) in
       (ktrp kempe_valid) -> (ktrp' kempe_valid)
    /\ (sz : nat) (ktrp (kempe_complete (addn (exp3 d) (S sz))))
           -> (ktrp' (kempe_complete (S sz))).
  Move=> Hstep ctu ctr gtu Hv; Case: (Hktc' ? ? ? Hv) => [Hv1 Hcl1].
  Case: (Hstep ? Hv1) => [Hv2 Hcl2]; Case: (Hstep ? Hv2) => [Hv3 Hcl3].
  Split; [Done | Apply: [sz; Hc0](Hcl3 ? ?); Rewrite addnS].
  By Apply Hcl2; Rewrite: addnS; Rewrite: addnI -!addnA in Hc0; Auto.
Hnf; Move=> ktr; Def Dktr': ktr' := (ktc_step ktc' ktr).
Case: ktr Dktr' => [ctu [gtr gtu]] /=.
Move=> Dktr' [Hctu [Ectu [Hcte [Hgtr [Hgtu Hclg]]]]].
Case Hctue: (ctree_empty ctu) Dktr'.
  Move=> Dktr'; Rewrite Dktr'; Split; LeftBy Repeat (Split; Trivial).
  Move=> sz [Hsz Hcl]; Split; Rewrite: // (ctree_empty_eq Hctue); By Left.
Case Hgtre: (gtree_empty gtr).
  Move=> Dktr'; Rewrite Dktr';  Split; LeftBy Repeat (Split; Trivial).
  Move=> sz [Hsz Hcl]; Split; [Right; Split; Trivial | Done].
  By Move=> w; Rewrite: (gtree_empty_empty Hgtre) gtree_mem_empty.
Case Hgtue: (gtree_empty gtu); Move=> Dktr'; Rewrite Dktr'.
  Split; RightBy Move=> sz _; Split; [Left | Right; Rewrite gtree_sub_empty].
  Do 2 Split; LeftBy Move=> et; Rewrite: gtree_sub_empty /= addn0 if_same.
  Split; [Done | Split; LeftBy Move=> w; Rewrite gtree_mem_empty].
  Split; RightBy Move=> w; Rewrite gtree_mem_empty.
  By Rewrite: (gtree_empty_empty Hgtue) in Hgtu *.
Clear: ktr' Dktr' Hctue Hgtre Hgtue.
Move: (ctree_restrict_correct (Ctr_some Bstack0 gtr Ctr_none) Hctu).
Case: (ctree_restrict h ctu (Ctr_some Bstack0 gtr Ctr_none)) => [ctu' ctr].
Simpl; Move=> [Hctru' [Hctp Ectu'r]].
Cut (kempe_valid ctu' (ctree_rotlr ctr) Gtree_empty gtu)
  /\ (sz : nat) (kempe_complete (S sz) ctu Ctree_empty gtr gtu)
              -> (kempe_complete sz ctu' (ctree_rotlr ctr) Gtree_empty gtu).
   Move=> [Hv Hc]; Case: (Hktc' ? ? ? Hv).
   By Split; Auto; Move=> sz; Rewrite addnS; Auto.
Step Ectu': (et : colseq) (ctree_sub ctu' et) =
      (if (negb (even_trace et)) then (0) else (gtree_sub gtu Bstack0 et)).
  Move=> et; Rewrite: Ectu'r Ectu addn0.
  Case (even_trace et); [Exact (subn_addr ? ?) | Done].
Clear Ectu'r Hktc' Hcte; Split.
  Split; [Exact (Hctru' false) | Split].
    Move=> et; Rewrite gtree_sub_empty; Exact (Ectu' et).
  Split; [Move=> et Het | By Split; [Move=> [|s w] | Split]].
  Step [g Het']: (EX g | (ctree_mem ctr (permt g et))).
    Rewrite (ctree_mem_rotlr et (Hctru' true)) in Het.
    By Case (orP Het); [Exists Eperm312 | Exists Eperm231].
  Pose et' := (permt g et); Rewrite: -/et' in Het'.
  Step [g' Eg']: (EX g' | (ctrace et) = (permt g' (ctrace et'))).
    Exists (inv_eperm g); Rewrite: /et' ctrace_permt.
    Exact (monic_move (monic_maps (inv_permc g)) (erefl ?)).
  Step Elg: (size et') = (size et) By Exact (size_maps ? ?).
  Case Het'u: (ctree_mem ctu et') (Hctp et');
    Case Hetu': (ctree_mem ctu' et');
    Rewrite Het'; Move=> Hep; Try Done; Clear Hep Het'.
  Move: Hetu' Het'u; Rewrite: /ctree_mem Ectu Ectu'.
  Case (even_trace et'); [Simpl | Done].
  Move=> Het'; Rewrite: -(eqP (negbEf Het')) addn0; Move=> Het'g.
  Case: {Het'g}(nmatchP Het'g) => [w Hw Hm].
  Case: {Hgtr}(Hgtr w Hw) => [Hwu H]; Case: {H}(andP H) (Hgtu ? Hwu H).
  Move=> Hlw Hcw [et1 _ Het1w].
  Move: (esym (matchpg_size Hm)); Rewrite: (eqP Hlw) Elg.
  Move=> Hetl; Split; [Move=> P' HP' HP'et | Done].
  Step HP'et': (P' (ctrace et')).
    By Rewrite: /et' ctrace_permt; Case: (HP' ? HP'et).
  Case: (HP' ? HP'et') => [_ [w1 Hetw1 HP'w1]].
  Move: (take (pred (size w1)) w1) (matchg_cgram Hetw1) => w2 Dw1.
  Case: (matchg_balanced Hetw1) => [_ Hw2]; Rewrite: Dw1 sumt_ctrace /= in Hw2.
  Move: (Hetw1); Rewrite: Dw1 !matchg_pg //; Move=> Hetw2.
  Case: (Hgtu w2).
      By Move=> Hgtuw2; Case/idPn: Het'; Apply/nmatchP; Exists w2.
    By Rewrite: /init_gtree_spec Hw2 (matchpg_size Hetw2) Elg Hetl set11.
  By Apply: [et2; Het2; H](Het2 ? HP' (HP'w1 ? ?)); Rewrite: Dw1 matchg_pg.
Move=> sz [Hsz Hcl]; Split.
  Case: Hsz => [Hsz | [_ Egtr]].
    Move: Hsz; Rewrite: (ctree_size_partition Hctp) addnC.
    Case Dctr: (ctree_size ctr) => [|m] Hsz.
      Right; Rewrite (ctree_size_proper (Hctru' true) Dctr).
      By Repeat Split; Move=> *; Rewrite gtree_mem_empty.
    Left; Apply: (leq_trans 2!(S (S ?)) ? Hsz); Exact (leq_addl m ?).
  Right; Split; RightBy Move=> *; Rewrite gtree_mem_empty.
  Replace ctr with Ctree_empty; [Done | Symmetry].
  Apply (ctree_size_proper (Hctru' true)).
  Apply (!addn_injl (ctree_size ctu')); Rewrite: -(ctree_size_partition Hctp).
  Rewrite: (!ctree_size_partition ctu ctu' Ctree_empty) //.
  Move=> et; Move: (Hctp et).
  Case Hetu': (ctree_mem ctu' et); Case Hetu: (ctree_mem ctu et); Trivial.
  Case/idPn: Hetu'; Move: Hetu.
  By Rewrite: /ctree_mem Ectu Ectu' {1}/gtree_sub match_count_0.
Move=> et [Het | [e Hrot]]; Try (Case: (Hcl et); [Tauto | Done | Tauto]).
Case Hetu': (ctree_mem ctu' (etrace et)).
  Case Hrotu: (ctree_mem ctu (permt (edge_rot e) (etrace et))).
    Left; Move: {Hctp}(Hctp (permt (edge_rot e) (etrace et))).
    Rewrite: ~Hrotu (introF idP Hrot) /=.
    Case Hrotr: (ctree_mem ctr (permt (edge_rot e) (etrace et))) => // [] _.
    Rewrite (ctree_mem_rotlr (etrace et) (Hctru' true)).
    Case: e {Hrot}(introF idP Hrot) Hrotr; Simpl;
      By First [Rewrite: permt_id Hetu' | Move=> _ H; Rewrite: H ?orb_b_true].
  By Case: (Hcl et); Auto; LeftBy Right; Exists e; Rewrite Hrotu.
Right; Symmetry; Apply: (eqP (introTn nmatchP ?)); Move=> [w Hw Hetw].
Rewrite: /ctree_mem Ectu' even_etrace /= in Hetu'.
By Case (elimF nmatchP Hetu'); Exists w; Rewrite: ?matchpg_etrace.
Qed.

Lemma kempe_validP : (ctu, ctr : ctree; gtr, gtu : gtree)
 (Hv : (kempe_valid ctu ctr gtr gtu))
 (et : colseq; Het : (size et) = (S h))
 (negb (ctree_mem ctu (etrace et))) -> (kempe_coclosure P (ctrace et)).
Proof.
Move=> ctu ctr gtr gtu [Hctu [Ectu [Hctr [Hgtr [Hgtu Hclg]]]]] et0 Het0l.
Move=> Het0 P' HP' HP'et0; Step HP'eet0: (P' (ctrace (etrace et0))).
  By Rewrite: /etrace ctrace_permt; Case: (HP' ? HP'et0).
Case: (HP' ? HP'eet0) => [_ [cw Hwet0 HP'cw]].
Move: (take (pred (size cw)) cw) (matchg_cgram Hwet0) => w Dcw.
Case: (matchg_balanced Hwet0) => [_ Hbw]; Rewrite: sumt_ctrace /= Dcw in Hbw.
Rewrite: Dcw matchg_pg // in Hwet0.
Case: (Hgtu w).
    Move=> Hgtuw; Case: (negP Het0).
    Rewrite: /ctree_mem Ectu even_etrace /= eqd_sym -leqn0 -ltnNge.
    Apply: (leq_trans ? (leq_addl ? ?)); Rewrite: ltnNge leqn0 eqd_sym.
    By Apply: (introT nmatchP ?); Exists w.
  Rewrite: /init_gtree_spec Hbw (matchpg_size Hwet0) /etrace /permt size_maps.
  By Rewrite: Het0l set11.
By Apply: [et'; Het'; H](Het' ? HP' (HP'cw ? ?)); Rewrite: Dcw matchg_pg.
Qed.

Lemma kempe_completeP : (ctu, ctr : ctree; gtr, gtu : gtree)
 (Hv : (kempe_valid ctu ctr gtr gtu))
 (Hc : (kempe_complete (1) ctu ctr gtr gtu))
 (et : colseq; Het : (size et) = (S h))
 (reflect (kempe_coclosure P (ctrace et)) (negb (ctree_mem ctu (etrace et)))).
Proof.
Move=> ctu ctr gtr gtu Hv [Hsz Hcl] et0 Het0l.
Case Het0: (ctree_mem ctu (etrace et0)); Constructor;
  RightBy Apply (kempe_validP Hv Het0l); Rewrite Het0.
Case: Hv => [Hctu [Ectu [Hctr [Hgtr [Hgtu Hclg]]]]] Hk.
Apply: (elimF idP ? Het0); Clear Het0.
Case: Hsz => [Hsz0 | [Dctr Egtr]].
  Rewrite: ltnS leqn0 in Hsz0.
  By Rewrite (ctree_size_proper Hctu (eqP Hsz0)).
Step Hctug: (et : colseq)
    (gtree_sub gtu Bstack0 et) = (0) -> ~(ctree_mem ctu et).
  Move=> et Het; Unfold ctree_mem; Rewrite: Ectu Het; Unfold gtree_sub.
  By Rewrite: match_count_0 /= ?if_same.
Step Hgtu23: (et : colseq; Het: (gtree_sub gtu Bstack0 et) = (0))
    (gtree_sub gtu Bstack0 (permt Eperm132 et)) = (0).
  Move=> et Het; Apply: esym; Apply: eqP; Apply/nmatchP=> [[w Hw Hm]].
  Rewrite matchpg_flip in Hm.
  By Case/idPn: (introT eqP (esym Het)); Apply/nmatchP; Exists w.
Step Hctu23: (et : colseq)
    (ctree_mem ctu (permt Eperm132 (etrace et)))
      -> (ctree_mem ctu (etrace et)).
  Move=> et; Rewrite: {2}/ctree_mem Ectu even_etrace {1}/gtree_sub.
  Rewrite: match_count_0 //=; Move=> Het.
  Apply/eqP=> [Hwet]; Apply: Hctug Het; Auto.
Step Hctue : (et : colseq)
   (ctree_mem ctu (etrace et))
     = (orb (ctree_mem ctu et) (ctree_mem ctu (permt Eperm132 et))).
  Step Hio: (b,b': bool) (b -> b') -> b' = (orb b b').
    Rewrite: /is_true; Case; Auto.
  Move=> et; Move: (Hctu23 et); Rewrite: /etrace /etrace_perm.
  Case (even_trace et); Rewrite: ?permt_id ?etrace_id; Auto.
  Rewrite orbC; Auto.
Move Dcet0: (ctrace et0) Hk => cet0 Hk; Apply/negPf=> [Het0].
Case (Hk [cet](EX et | cet = (ctrace et) & (ctree_mem ctu (etrace et)))).
  Move=> cet [et Dcet Het]; Split.
    Move=> g; Exists (permt g et); LeftBy Rewrite: Dcet ctrace_permt.
    Pose et' := (etrace et).
    Step [g' [ ]]: (EX g' | (permt g' et') = (permt g et)).
      Case: (compose_permt g (etrace_perm et) (etrace et)) => [g' Eg'].
      Exists g'; Rewrite: Eg' /et' /etrace /etrace_perm.
      By Case (even_trace et); Rewrite: ?permt_id ?etrace_id.
    Rewrite: Hctue; Apply/norP=> [[Hg'et Hpg'et]].
    Step Hrot: (EX e | ~(ctree_mem ctu (permt (edge_rot e) et'))).
      Case: g' {Hg'et Hpg'et} (negP Hg'et) (negP Hpg'et);
      Try First [By Exists Color1 | By Exists Color2 | By Exists Color3];
      Try (By Rewrite etrace_id; Exists Color1; Rewrite permt_id);
      Move=> _ Het'; Rewrite: /permt -maps_comp in Het';
      [Exists Color2 | Exists Color3]; Move=> He;
      By Apply: (Het' (etrans (congr ? (eq_maps ? ?)) He)); Case.
    Case (Hcl et); [By Right | By Rewrite Dctr | Idtac].
    Rewrite: Hctue in Het; Case: {Het}(orP Het) => [Het | Het];
      By Apply: [Het'](elimF idP (negbIf Het) (introT negP ?)); Auto.
    Case Hgtuet: ((0) =d (gtree_sub gtu Bstack0 (etrace et))).
      Case (Hctug ? (esym (eqP Hgtuet)) Het).
    Case/nmatchP: Hgtuet => [w Hw Hwet].
    Case/andP: (Hclg ? Hw) => [Hsw Hbw].
    Exists (cgram (0) false w).
      By Rewrite: matchpg_etrace -matchg_pg // -Dcet in Hwet *.
    Move=> cet' Hcet'w; Step [et' Dcet']: (EX et' | cet' = (ctrace et')).
      Move: (balanced_sumt0 Hbw Hcet'w).
      Elim/last_ind: cet' Hcet'w => [|et' e _]; LeftBy Case w.
      Move=> _ He; Rewrite: -cats1 /sumt foldr_cat /= addc0 in He.
      Exists et'; Apply: (congr (add_last ?) (inj_addc 1!e ?)).
      Rewrite: addcc -~He; Elim: et' e => [|e' et' Erec] e /=.
        By Rewrite addc0.
      By Rewrite: Erec !addcA (addcC e').
    Exists et'; Auto.
    Rewrite: Dcet' matchg_pg // in Hcet'w.
    Rewrite: /ctree_mem Ectu even_etrace /= eqd_sym -leqn0 -ltnNge.
    Apply: (leq_trans ? (leq_addl ? ?)); Rewrite: ltnNge leqn0 eqd_sym.
    By Apply: (introT nmatchP ?); Exists w; Rewrite: ?matchpg_etrace.
  By Exists et0; Rewrite: // /ctree_mem Het0.
Move=> cet Hpet [et Dcet Het]; Case (Hcl et); Rewrite: ?Dctr // -?Dcet; Auto.
Move=> Hgtuet; Case (negP Het); Rewrite: Ectu even_etrace /=.
Step Hgtueet: (gtree_sub gtu Bstack0 (etrace et)) = (0).
  Unfold etrace etrace_perm; Case (even_trace et); Rewrite: ?permt_id; Auto.
Rewrite: Hgtueet addn0; Apply/nmatchP=> [[w' Hw' _]]; Case (Egtr ? Hw').
Qed.

Lemma kempe_valid_restrict : (ctr, ctu : ctree; gtu, gtr : gtree)
  ((et : colseq) (ctree_mem ctr et) -> (P (ctrace et)) /\ (size et) = (S h))
  -> (kempe_valid ctu Ctree_empty gtr gtu) -> (kempe_valid ctu ctr gtr gtu).
Proof.
Move=> ctr ctu gtu gtr Hctr [Hctu [Ectu [_ Hgtur]]]; Do 3 (Split; Trivial).
By Move=> et Het; Case: (Hctr ? Het); Split; LeftBy Exists (ctrace et).
Qed.

Lemma kempe_valid_init :
  let ctu = (ctree_init_tree (S h)) in
  let gtu = (gtree_init_tree (S h)) in
  (kempe_valid ctu Ctree_empty Gtree_empty gtu).
Proof.
Move: (ctree_init_tree_proper (S h)) (ctree_sub_init_tree (S h)).
Move Dctu: (ctree_init_tree (S h)) => ctu Hctu Ectu.
Move Dgtu: (gtree_init_tree (S h)) (gtree_mem_init_tree (S h)) => gtu Egtu.
Split; [Done | Split].
  Move=> et; Rewrite: Ectu gtree_sub_empty andbC.
  Case Hete: (even_trace et); RightBy Done.
  By Rewrite: /= /gtree_sub (match_count_eq Egtu) match_count_balanced.
Split; [Done | Split; LeftBy Move=> w; Rewrite: gtree_mem_empty].
By Split; Move=> w; Rewrite Egtu; LeftBy Move=> H H'; Case (H H').
Qed.

Lemma kempe_complete_init : (ctr : ctree)
  (Hctr : (et : colseq) (P (ctrace et)) -> (ctree_mem ctr (etrace et)))
  let ctu = (ctree_init_tree (S h)) in
  let gtu = (gtree_init_tree (S h)) in
  (gtr : gtree)(kempe_complete (exp3 (S (S h))) ctu ctr gtr gtu).
Proof.
Move=> ctr Hctr; Split.
  Left; Step Hexp: (ltn (exp3 (S h)) (exp3 (S (S h)))).
    Move: (S h) => n; Rewrite: -addn1 /= addnI leq_add2l addn0.
    Elim: n => [|n Hrec]; [Done | Rewrite: /= addnI -!addnA addnA].
    Exact (leq_trans Hrec (leq_addr ? ?)).
  Apply: (leq_trans ? Hexp); Rewrite ltnS; Apply ctree_max_size_proper.
  Apply ctree_init_tree_proper.
Move=> et [Het | [e Hrot]]; Auto.
Right; Apply: (esym (eqP (negbEf (introF nmatchP ?)))).
Move=> [w Hw Hetw]; Case: Hrot; Rewrite: /ctree_mem ctree_sub_init_tree.
Rewrite: gtree_mem_init_tree in Hw; Case: {Hw}(andP Hw) => [Hsw Hbw].
Rewrite: {1 2}/etrace {1 2}/permt !size_maps -(matchpg_size Hetw) Hsw.
Rewrite: -matchg_pg // in Hetw.
Rewrite: !ctrace_permt !memc0_permt (matchg_memc0 Hetw).
Pose pre := (permt (edge_rot e)); Step Hreet: (even_trace (pre (etrace et))).
  Rewrite: /is_true -(even_etrace et) /even_trace /ttail /pre proper_permt.
  Case: (etrace et) => [|[|||] ett]; Rewrite: // /permt /= -maps_comp;
    By Apply: (congr even_tail (eq_maps ? ?)); Move=> [|||]; Case e.
Step Hbit: (et' : colseq) (odd (count_cbit1 et')) = (cbit1 (sumt et')).
  Move=> et'; Elim: et' => [|c et' Hrec]; Trivial; Simpl.
  By Rewrite: odd_addn Hrec cbit1_addc; Case c.
Rewrite: Hreet /= -[et'](odd_double_half (count_cbit1 et')) Hbit /pre.
Rewrite: sumt_permt sumt_ctrace permc0 /= add0n eqd_sym -leqn0 -ltnNge.
Apply even_dyck_pos.
Qed.

End KempeTreeClosure.

Definition kempe_tree [cp : cprog] : ctree :=
  if (cprsize cp) is (S (S h)) then
    let ctu = (ctree_init_tree (S h)) in
    let gtu = (gtree_init_tree (S h)) in
    let ctr = (cpcolor cp) in
    (Fst (kempe_tree_closure h (S (S h)) ctu ctr gtu))
  else Ctree_empty.

Theorem kempe_treeP : (cp : cprog; et : colseq)
  (size et) = (pred (cprsize cp)) ->
  let Pcol = (ring_trace (rot (1) (cpring (cpmap cp)))) in
  (reflect (kempe_coclosure Pcol (ctrace et))
    (negb (ctree_mem (kempe_tree cp) (etrace et)))).
Proof.
Move=> cp; Rewrite: /kempe_tree.
Move: (cpcolor cp) (ctree_mem_cpcolor cp) => ctr Dctr.
Pose Pcol := (ring_trace (rot (1) (cpring (cpmap cp)))).
Case Dh: (cprsize cp) => [|[|h]].
    By Rewrite: -size_ring_cpmap head_cpring in Dh.
  By Case=> // [] _; Left; By Move=> P H H0; Case: (H ? H0) => [_ [[|s w] Hw _]].
Pose ctu := (ctree_init_tree (S h)); Pose gtu := (gtree_init_tree (S h)).
Case: (!kempe_tree_closure_correct h Pcol (S (S h)) ctu ctr gtu).
  Apply: (kempe_valid_restrict ? (kempe_valid_init ? ?)).
  Move=> et'; Move/(Dctr ?) => [Heet' [k Hk Det']]; Split.
    By Rewrite: /Pcol /ctrace -rot1_adds Det' -trace_rot -maps_rot; Exists k.
  Move: (congr size Det'); Rewrite: size_trace size_maps size_ring_cpmap Dh.
  By Injection=> [].
Case: (kempe_tree_closure h (S (S h)) ctu ctr gtu) => [ctu' [gtr gtu']].
Move=> Hv Hcl; Apply: (kempe_completeP Hv (Hcl ? ?)) {Hcl}.
Rewrite addn0; Apply: kempe_complete_init{et Het}=> [et Het]; Apply/(Dctr ?).
Split; LeftBy Apply even_etrace.
Case: Het => [k Hk Det]; Rewrite: /Pcol maps_rot trace_rot in Det.
Rewrite: /etrace; Pose g := (etrace_perm et); Exists (comp g k).
  By Apply: (coloring_inj 2!g) Hk => //; Apply permc_inj.
Rewrite: (maps_comp g k) -/(permt g) trace_permt sumt_permt.
By Rewrite: (monic_move (rotr_rot (1) 2!?) (esym Det)) /ctrace rotr1_add_last.
Qed.

Unset Implicit Arguments.

