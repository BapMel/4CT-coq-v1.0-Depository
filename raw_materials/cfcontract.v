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
Require geometry.
Require color.
Require coloring.
Require cfmap.
Require ctree.
Require cfcolor.

Set Implicit Arguments.

(* Compute the contract of a configuration construction: a cprog whose ring  *)
(* colorings coincides with the contract colorings of the initial cprog.     *)
(* Also, check the validity of the contract (sparseness, and possibly the    *)
(* existence of a triad.                                                     *)
(* The darts in the contract sequence are represented by the index at which  *)
(* they are removed from the internal ring; each Y step (except the final    *)
(* one) has a single index, while each H step has three. The first index of  *)
(* the H step corresponds to the middle edge, which is actually never part   *)
(* of a ring; the next two are for the left and right feet of the H.         *)
(* The last Y does not have an index because it removes only one dart of the *)
(* central edge pair.                                                        *)

Section ConfigContract.

Fixpoint ctrmsize [cp : cprog] : nat :=
  Cases cp of
    (Adds (CpR _) cp') => (ctrmsize cp')
  | (Adds CpY Seq0) => (0)
  | (Adds CpY cp') => (S (ctrmsize cp'))
  | (Adds CpH cp') => (S (S (S (ctrmsize cp'))))
  | _ => (0)
  end.

Fixpoint ctrmask_rec [cci : natseq; i, n : nat] : bitseq :=
  if n is (S n') then (Adds (cci i) (ctrmask_rec cci (S i) n')) else seq0.

Definition ctrmask [cp : cprog; cci : natseq] : bitseq :=
  (ctrmask_rec cci (0) (ctrmsize cp)).

Lemma size_ctrmask : (cp : cprog; ms : natseq)
  (size (ctrmask cp ms)) = (ctrmsize cp).
Proof.
By Move=> cp ms; Rewrite: /ctrmask; Elim: (ctrmsize cp) (0) => //= *; Congr S.
Qed.

Fixpoint ctrenum [cp : cprog] : (seq (cpmap cp)) :=
  <[cp'](seq (cpmap cp'))>Cases cp of
    (Adds (CpR _) cp') =>
    (ctrenum cp')
  | (Adds CpY cp') =>
    let g = (cpmap cp') in
    if cp' is Seq0 then seq0 else (maps (icpY g) (Adds (node g) (ctrenum cp')))
  | (Adds CpH cp') =>
    let g = (cpmap cp') in
    (Adds (face (ecpH g)) (maps (icpH g) (Adds (node g) (Adds g (ctrenum cp')))))
  | _ => seq0
  end.

Lemma size_ctrenum : (cp : cprog) (size (ctrenum cp)) = (ctrmsize cp).
Proof.
Elim=> [|[n||||||] cp Hrec] //=; Rewrite: -~Hrec ?size_maps //.
By Case: cp => //= *; Rewrite size_maps.
Qed.

Lemma insertE_icpY : (g : hypermap; x : g; p : (seq g))
  (insertE (maps (icpY x) p)) = (maps (icpY x) (insertE p)).
Proof. By Move=> g x; Elim=> // *; Repeat Congr Adds. Qed.

Lemma insertE_icpH : (g : hypermap; x : g; p : (seq g))
  (insertE (maps (icpH x) p)) = (maps (icpH x) (insertE p)).
Proof. By Move=> g x; Elim=> // *; Repeat Congr Adds. Qed.

Lemma uniq_ctrenum : (cp : cprog)
  (config_prog cp) -> (uniq (insertE (cat (cpring (cpmap cp)) (ctrenum cp)))).
Proof.
Elim=> //=; Case=> // [n||] cp Hrec.
    Move/Hrec {Hrec}; Apply: etrans; Pose g := (cpmap cp).
    Rewrite: cpring_ecpR /rot !insertE_cat -catA uniq_catCA catA.
    By Rewrite: -insertE_cat cat_take_drop.
  Case Dcp: cp => // [s cp']; Case: {c cp'}Dcp => [] Hcp; Move: {Hrec}(Hrec Hcp).
  Pose g := (cpmap cp); Move=> Hrec; Rewrite: cpring_ecpY.
  Rewrite: -!cat1s !(!insertE_cat (ecpY g)) uniq_catCA.
  Rewrite: {1 cat}lock -!catA catA -lock uniq_catCA -!insertE_cat -maps_cat.
  Rewrite: !cat1s -maps_adds -cat_adds -head_cpring insertE_cat.
  Rewrite: (insertE_icpY g) uniq_cat (uniq_maps (icpY_inj 2!g)) Hrec.
  By Rewrite: has_maps /comp /= /setU1 /= has_set0.
Move=> Hcp; Move: (cpmap_proper (config_prog_cubic Hcp)) {Hrec}(Hrec Hcp).
Pose g := (cpmap cp); Move=> Hgp Hrec.
Rewrite: (cpring_ecpH Hgp) -!cat1s !(!insertE_cat (ecpH g)).
Rewrite: {1 cat}lock !catA -lock uniq_catCA {2 6 cat}lock -!catA uniq_catCA.
Rewrite: -!lock -!catA -3!insertE_cat !cat1s -maps_cat -!maps_adds.
Rewrite: -!cat_adds -(head_proper_cpring Hgp) (insertE_icpH g) !catA.
Rewrite: {insertE}lock /= /long_cpring /= Enode (negbE Hgp) /= -!lock.
Rewrite: uniq_cat (uniq_maps (icpH_inj 2!g)) Hrec has_maps /comp /= /setU1 /=.
By Rewrite has_set0.
Qed.

Local nsp : (b1, b2, b3 : bool) bool := [b]if b then orb else andb.

Fixpoint cfctr [mr, mc : bitseq; cp : cprog] : (option cprog) :=
  Cases cp mr mc of
    (Adds (CpR i) cp') _ _ =>
    let mr' = (rotr i mr) in
    if (cfctr mr' mc cp') is (Some cpc) then
      (Some ? (Adds (CpR (count negb (take i mr'))) cpc))
    else (None ?)
  | (Adds CpY Seq0) (Adds b1 (Adds b2 (Adds b3 _))) _ =>
    if (nsp b1 b2 b3) then (None ?) else
    (Some ? if (or3b b1 b2 b3) then seq0 else (seq1 CpY))
  | (Adds CpY cp') (Adds b1 (Adds b2 mr')) (Adds b3 mc') =>
    if (nsp b1 b2 b3) then (None ?) else
    if (cfctr (Adds b3 mr') mc' cp') is (Some cpc) then
      (Some ? if (orb b1 b2) then cpc else (Adds (if b3 then CpU else CpY) cpc))
    else (None ?)
  | (Adds CpH cp') (Adds b1 (Adds b2 mr')) (Adds b3 (Adds b4 (Adds b5 mc'))) =>
    if (orb (nsp b3 b1 b4) (nsp b3 b2 b5)) then (None ?) else
    if (and3b b1 b2 (all [b]b mr')) then (None ?) else
    if (cfctr (Adds b4 (Adds b5 mr')) mc' cp') is (Some cpc) then
      (Some ? if b3 then cpc else
              if b1 then
                if b2 then (Adds CpA cpc) else
                if b5 then cpc else (Adds CpK cpc) else
              if b2 then
                if b4 then cpc else (Adds CpK cpc) else
              if b4 then
                if b5 then (Adds CpU cpc) else (Adds CpY cpc) else
             if b5 then (Adds CpY cpc) else (Adds CpH cpc))
    else (None ?)
  | _ _ _ =>
    (None ?)
  end.

Lemma cfctr_config_prog : (mr, mc : bitseq; cp : cprog)
  if (cfctr mr mc cp) is (Some _) then (config_prog cp) else true.
Proof.
Move=> mr mc cp; Elim: cp mr mc => //=; Case=> // [n||] cp Hrec mr mc.
    By Case: (cfctr (rotr n mr) mc cp) (Hrec (rotr n mr) mc).
  Case Dcp: cp mr => [|s cp'] [|b1 [|b2 mr]] //.
    Case: mr => [|b3 mr]; RightBy Case (nsp b1 b2 b3).
    By Case: mc => [|b3 mc] //; Case: (nsp b1 b2 b3).
  Case Dcp; Case: mc => [|b3 mc] //; Case: (nsp b1 b2 b3) => //.
  By Case: (cfctr (Adds b3 mr) mc cp) (Hrec (Adds b3 mr) mc).
Case: mr mc => [|b1 [|b2 mr]] [|b3 [|b4 [|b5 mc]]] //=.
Case: (orb (nsp b3 b1 b4) (nsp b3 b2 b5)) => //.
Case: (and3b b1 b2 (all [b : bool]b mr)) => //.
By Pose mr' := (Adds b4 (Adds b5 mr)); Case: (cfctr mr' mc cp) (Hrec mr' mc).
Qed.

Lemma cfctr_correct : (mr, mc : bitseq; cp : cprog)
  (size mr) = (cprsize cp) -> (size mc) = (ctrmsize cp) ->
  let g = (cpmap cp) in let r = (cpring g) in
  let cc = (cat (sieve mr r) (sieve mc (ctrenum cp))) in
  (k : g -> color) (cc_coloring cc k) ->
  if (cfctr mr mc cp) is (Some cpc) then
    let r' = (cpring (cpmap cpc)) in
    (EX k' | (coloring k') & (maps k' r') = (maps k (sieve (maps negb mr) r)))
  else True.
Proof.
Move=> /= mr mc cp; Elim: cp mr mc => [|s cp Hrec] mr mc //.
Move: (cfctr_config_prog mr mc (Adds s cp)).
Case Dcpc: (cfctr mr mc (Adds s cp)) => // [cpc].
Case: s Dcpc => // [n||] Dcpc Hcp' Emr Emc;
  Def: Hcp := (config_prog_cubic Hcp'); Simpl in Dcpc Hcp Emr Emc;
  Move: Hrec (cpmap_plain Hcp) (cpmap_proper Hcp);
  Rewrite: /cpmap -/cpmap; Pose g := (cpmap cp); Move => Hrec HgE Hgp.
    Rewrite: cpring_ecpR; Rewrite: -(size_rotr n) in Emr.
    Move=> k [HkE HkF]; Move: {Hrec}(Hrec ? ? Emr Emc k).
    Case: (cfctr (rotr n mr) mc cp) cpc Dcpc => // [cpc] p'; Injection=> []{p'}.
    Rewrite: /cpmap -/cpmap; Pose gc := (cpmap cpc).
    Case.
      Split; RightDone.
      Move=> x; Rewrite: HkE !(mem_insertE HgE); Apply: eq_has_r {x} => [x].
      Rewrite: !mem_cat; Congr orb; Rewrite: -{1 mr}(rot_rotr n mr).
      By Apply: mem_sieve_rot; Rewrite: Emr -size_ring_cpmap.
    Move=> k' Hk' Ek'; Exists k'; LeftDone.
    Rewrite: cpring_ecpR -{3 mr}(rot_rotr n mr) !maps_rot ~Ek' sieve_rot.
      By Rewrite: maps_rot -maps_take count_maps. 
    By Rewrite: size_maps /g size_ring_cpmap.
  Rewrite: /g.
  Case Dcp: cp mc mr Emc Emr Dcpc => [|s cp'] [|b3 mc] [|b1 [|b2 mr]] //.
    Case: mr {cp Dcp Hcp' Hcp g Hrec HgE Hgp} => [|b3 [|b4 mr]] // _ _.
    Case Hb123: (nsp b1 b2 b3) => //; Injection=> [] {cpc}; Rewrite: cpring_ecpY.
    Pose x0 := ((cpmap seq0) :: (dart ?)).
    Case: b1 Hb123; Case: b2=> //; Case: b3=> // [] _ k [HkE HkF].    
     Exists [y](k (icpY x0 y)).
        By Split; [Move=> y; Case: y (HkE (icpY x0 y)) | Case; Apply/eqP].
      Congr Adds; Move: (HkE (node (ecpY ?))); Rewrite: /= /setU1 /=.
      Move/eqcP; Rewrite: /= -[u](eqcP (HkF u)) /=.
      By Move/esym; Rewrite: -[u](eqcP (HkF u)) /=.
     Exists [y](k (icpY x0 y)).
        By Split; [Move=> y; Case: y (HkE (icpY x0 y)) | Case; Apply/eqP].
      By Congr Adds; Rewrite: /= -[u](eqcP (HkF u)).
     Exists [y](k if y is true then (ecpY x0) else (node (ecpY x0))); RightDone.
      Split; RightBy Case; Apply/eqP.
      Def: HkEx0 := (HkE (node (ecpY x0))).
      Rewrite: /invariant -[u](eqcP (HkF u)) Enode in HkEx0.
      By Case=> //; Rewrite: /invariant eqd_sym.
    By Exists k; Split.
  Rewrite: -Dcp cpring_ecpY; Move=> Emc Emr; Simpl in Emc Emr.
  Injection: Emc => Emc; Injection: Emr => Emr.
  Step Ecp: (ctrenum (Adds CpY cp)) = (maps (icpY g) (Adds (node g) (ctrenum cp))).
    By Rewrite: /= /g Dcp.
  Step Hg'E: (plain (ecpY g)) By Apply: plain_ecpY.
  Case Hb123: (nsp b1 b2 b3) {s cp' Dcp} => //.
  Case: (cfctr (Adds b3 mr) mc cp) {Hrec Emr}(Hrec (Adds b3 mr) mc Emr Emc) => //.
  Move: cpc => p' cpc Hrec; Injection=> [] {p'} k [HkE HkF].
  Pose h := [x](k (icpY g x)).
  Step HhF: (invariant face h) =1 g.
    Move=> x; Apply/eqP; Apply: (fconnect_invariant HkF).
    By Rewrite: cface_icpY Sface fconnect1.
  Step HhE: (invariant edge h) =1
      (insertE (cat (sieve (Adds b3 mr) (cpring g)) (sieve mc (ctrenum cp)))).
    Move=> x; Rewrite: /invariant /h -icpY_edge; Apply: (etrans (HkE ?)).
    Rewrite: !mem_insertE // /behead head_cpring Ecp.
    Rewrite: (eq_has (plain_orbit HgE x)) (eq_has (plain_orbit Hg'E (icpY g x))).
    Rewrite: !has_cat icpY_edge maps_adds !has_sieve_adds !andbF !orFb.
    By Rewrite: orbCA -!orbA; Congr orb; Rewrite: -!maps_sieve !has_maps.
  Case: {Hrec}(Hrec h) {Emc}; LeftBy Split.
  Pose gc := (cpmap cpc); Move=> h' Hh' Eh.
  Move: Hh' (coloring_proper_cpring gc Hh') => [Hh'E Hh'F] Hgcp.
  Case Hb12: (orb b1 b2).
    Exists h'; LeftBy Split.
    Rewrite: ~{h' HhE Hh'E Hh'F Eh'nX}Eh /behead head_cpring /h.
    Rewrite: !maps_sieve (maps_comp k (icpY ?)) !maps_adds.
    Rewrite: -(fconnect_invariant HkF (cface_node_ecpY g)).
    Case: b1 b2 b3 Hb12 Hb123 HkE => [|] [|] [|] // _ _ HkE; Congr Adds.
    Move: (etrans (HkE ?) (setU11 ? ?)).
    By Rewrite: /invariant -[u](eqcP (HkF u)) Enode; Move/eqP.
  Step HrgE: (all (invariant edge h) (sieve (Adds b3 mr) (cpring g))).
    Apply/allP=> [x Hx]; Rewrite: HhE mem_insertE //.
    Apply/hasP; Exists x; RightBy Apply connect0.
    By Rewrite: mem_cat /setU Hx.
  Step HrgN: (fpath (finv node) (node g) (behead (cpring g))).
    Move: (cycle_rev_cpring g); Rewrite: head_cpring lastI rev_add_last -lastI.
    By Rewrite: (cycle_path g) /= -(fpath_finv (Inode g)); Case/andP.
  Step Eh'nX: (h' (node gc)) = (h (node g)).
    Rewrite: head_cpring in Eh; Move: HrgE Eh {HhE HkE}; Rewrite: head_cpring.
    Elim: {mr}(Adds b3 mr) (node g) (behead (cpring g)) HrgN => // [b mr Hrec].
    Case: b; RightBy Move => x p _ _; Injection=> _.
    Move=> x [|y p] //=; LeftBy Case mr.
    Case/andP; Move/eqP=> Dy Hp; Case/andP; Case/eqcP.
    Rewrite: -(eqcP (HhF (edge x))) -{x}(f_finv (Inode g)) Enode Dy; EAuto.
  Case: b1 b2 b3 Hb12 Eh HkE HhE HrgE {Hb123} => [|] [|] [|] // _ Eh HkE HhE HrgE.
    Pose k' := [u]if pick x in [x](cface u (icpU (cpmap cpc) x)) then (h' x)
                  else (k (ecpY ?)).
    Step Hk'F : (invariant face k') =1 (ecpU (cpmap cpc)).
      Move=> u; Apply/eqP; Rewrite: /k' -(eq_pick 2![x](cface u (icpU ? x))) //.
      Move=> x; Apply: cface1.
    Step Ek': (x : (cpmap cpc)) (k' (icpU ? x)) = (h' x).
      Move=> x; Rewrite: /k'.
      Case: (pickP [y](cface (icpU (cpmap cpc) x) (icpU ? y))) => [y Hy | Hx].
        By Rewrite: cface_icpU Sface in Hy; Apply: (fconnect_invariant Hh'F).
      Case/idP: (Hx x); Apply connect0.
    Step Ek'X: (k' (ecpU ?)) = (k (ecpY ?)).
      Rewrite: /k'.
      Case: (pickP [y](cface (ecpU (cpmap cpc)) (icpU ? y))) => // [y Hy].
      By Rewrite: cface_ecpU in Hy.
    Step Ek'nX: (k' (node (ecpU ?))) = (k (node (ecpY ?))).
      Rewrite: (fconnect_invariant HkF (cface_node_ecpY ?)).
      By Rewrite: -[u](eqcP (Hk'F u)) /= -/(icpU (cpmap cpc)) Ek' Eh'nX.
    Exists k'.
      Split; RightDone.
      Step Hk'EX: (invariant edge k' (ecpU ?)) = false.
        Apply/eqP=> [Hk'X]; Move: (esym (HkE (node (ecpY g)))).
        Rewrite: /invariant -Ek'nX -[u](eqcP (HkF u)) Enode -Ek'X -Hk'X set11.
        Move: (uniq_ctrenum Hcp'); Rewrite: /cpmap -/cpmap -/g cpring_ecpY.
        Move: {mc HkE HhE}(Adds true mc) (ctrenum (Adds CpY cp)) => mc p.
        Move: (node (ecpY g)) => x /=; Case/andP=> [H _]; Move: H.
        Do 3 (Case/norP; Clear); Rewrite: !(mem_insertE Hg'E).
        Move=> H; Move/hasP=> [y Hy Hxy]; Case/hasP: H; Exists y; Auto.
        Rewrite: !mem_cat in Hy *; Apply/orP; Case/orP: Hy; Move/mem_sieve; Auto.
      Move=> [||x] //; LeftBy Rewrite: /invariant eqd_sym.
      Rewrite: -/cpmap -/gc in x *; Rewrite: -/(icpU gc x).
      Rewrite: /invariant -(icpU_edge gc) !Ek'; Apply: Hh'E.
    Rewrite: /cpmap -/cpmap cpring_ecpU !maps_adds {1 2}/negb.
    Rewrite: Ek'nX !sieve_adds !maps_cat !maps_seqn Ek'X; Do 2 Congr Adds.
    Rewrite: -maps_sieve -!maps_comp /comp -/h.
    By Rewrite: (eq_maps 3!(comp k' (icpU ?)) Ek') Eh head_cpring.
  Pose k' := [u]if pick x in [x](cface u (icpY gc x)) then (h' x)
                else (k (ecpY g)).
  Step Hk'F : (invariant face k') =1 (ecpY (cpmap cpc)).
    Move=> u; Apply/eqP; Rewrite: /k' -(eq_pick 2![x](cface u (icpY ? x))) //.
    Move=> x; Apply: cface1.
  Step Ek': (x : (cpmap cpc)) (k' (icpY ? x)) = (h' x).
    Move=> x; Rewrite: /k'.
    Case: (pickP [y](cface (icpY (cpmap cpc) x) (icpY ? y))) => [y Hy | Hx].
      By Rewrite: cface_icpY Sface in Hy; Apply: (fconnect_invariant Hh'F).
    Case/idP: (Hx x); Apply connect0.
  Step Ek'X: (k' (ecpY gc)) = (k (ecpY g)).
    Rewrite: /k'.
    Case: (pickP [y](cface (ecpY (cpmap cpc)) (icpY ? y))) => // [y Hy].
    By Rewrite: cface_ecpY in Hy.
  Step Ek'nX: (k' (node (ecpY ?))) = (k (node (ecpY ?))).
    Rewrite: (fconnect_invariant Hk'F (cface_node_ecpY ?)) Ek' Eh'nX.
    By Rewrite: (fconnect_invariant HkF (cface_node_ecpY ?)).
  Step Eh'X: (h' gc) = (h g).
    Rewrite: head_proper_cpring // in Eh; Move: HrgN Eh HrgE {HhE HkE}.
    Rewrite: head_proper_cpring //=; Case/andP=> [_ H]; Injection=> E _; Move: H E.
    Elim: mr (g::g) (drop (2) (cpring g)) => // [b mr Hrec].
    Case: b; RightBy Move => x p _; Injection=> _.
    Move=> x [|y p] //=; LeftBy Case mr.
    Case/andP; Move/eqP=> Dy Hp Eh; Case/andP; Case/eqcP; Move: Eh.
    Rewrite: -(eqcP (HhF (edge x))) -{x}(f_finv (Inode g)) Enode Dy; EAuto.
  Exists k'.
    Split; RightDone.
    Step Hk'EX: (u : (ecpY ?)) (cface u (ecpY ?)) -> (invariant edge k' u) = false.
      Move=> u HuX; Rewrite: /invariant (fconnect_invariant Hk'F HuX) Ek'X.
      Step HeuX: (adj (ecpY ?) (edge u)) By Rewrite: -(adjF HuX) adjE.
      Rewrite: (adj_ecpY Hgcp) /fband in HeuX; Case/hasP: HeuX {HuX} => [v].
      Case/mapsP=> [y Hy []] {v} H; Rewrite: ~{u H}(fconnect_invariant Hk'F H) Ek'.
      Move: (uniq_ctrenum Hcp') HkE; Rewrite: /cpmap -/cpmap -/g cpring_ecpY.
      Move: {mc HkE HhE}(Adds false mc) (ctrenum (Adds CpY cp)) {x Hx} => mc p.
      Def Dx: x : (ecpY g) := (ecpY g); Def Dnx: nx := (node x).
      Simpl; Case/and4P=> [H _ H' _]; Move: H H'; Rewrite: /setU1 /=.
      Do 3 (Case/norP; Clear); Rewrite: !(mem_insertE Hg'E).
      Move=> Hnx; Move/norP=> [_ Hx] HkE.
      Rewrite: mem_seq2 in Hy; Case/orP: Hy; Case/eqP {y}.
        Rewrite: -{x}Enode -Dnx Eh'nX /h (eqcP (HkF (edge nx))) eqd_sym.
        Rewrite: -(fconnect_invariant HkF (cface_node_ecpY ?)) -Dx -Dnx.
        Apply: (etrans (HkE nx)); Rewrite: (mem_insertE Hg'E).
        Apply/hasP=> [[z Hz Hxz]]; Case/hasP: Hnx; Exists z; RightDone.
        Rewrite: !mem_cat in Hz *; Apply/orP; Case/orP: Hz; Move/mem_sieve; Auto.
      Step []: (k (edge x)) = (h' gc).
        By Rewrite: -(eqcP (HkF (edge x))) Eh'X Dx /= Enode (negbE Hgp) /=.
      Apply: (etrans (HkE x)); Rewrite: (mem_insertE Hg'E).
      Apply/hasP=> [[z Hz Hxz]]; Case/hasP: Hx; Exists z; RightDone.
      Rewrite: !mem_cat in Hz *; Apply/orP; Case/orP: Hz; Move/mem_sieve; Auto.
    Move=> u; Case: (fband_icpY 2!gc u) => [[x Hx] | Hu].
      Case: (fband_icpY 2!gc (edge u)) => [[y Hy] | Heu].
        Rewrite: /invariant (fconnect_invariant Hk'F Hx).
        Rewrite: (fconnect_invariant Hk'F Hy) !Ek'.
        Step Hxy: (adj x y).
          By Rewrite: -(adj_icpY gc); Apply/adjP; Exists u; Rewrite: // Sface.
        Case/adjP: Hxy => [z Hxz Hzy]; Rewrite: (fconnect_invariant Hh'F Hxz).
        Rewrite: -(fconnect_invariant Hh'F Hzy); Apply: Hh'E.
      Step Deeu: (edge (edge u)) = u.
        By Move: Heu {Hx}; Rewrite: cface_ecpY; Case: u => [||[||z]].
      By Rewrite: /invariant eqd_sym -{1 u}Deeu; Apply: Hk'EX; Rewrite Sface.
    By Apply: Hk'EX; Rewrite Sface.
  Rewrite: /cpmap -/cpmap !cpring_ecpY !maps_adds {1 2}/negb.
  Rewrite: Ek'nX !sieve_adds !maps_cat !maps_seqn Ek'X; Do 2 Congr Adds.
  Rewrite: -maps_sieve -!maps_comp /comp -/gc -/h.
  Rewrite: (eq_maps 3!(comp k' (icpY gc)) Ek'). 
  By Rewrite: head_cpring (head_cpring g) in Eh; Injection: Eh.
Case: mr mc Emc Emr Dcpc => [|b1 [|b2 mr]] // [|b3 [|b4 [|b5 mc]]] // Emc Emr.
Case Hb: (orb (nsp b3 b1 b4) (nsp b3 b2 b5)); LeftDone.
Case HbA: (and3b b1 b2 (all [b:bool]b mr)); LeftDone.
Simpl in Emr Emc; Injection: Emc => Emc; Injection: Emr => Emr.
Move: {Hrec}(Hrec (Adds b4 (Adds b5 mr)) mc Emr Emc).
Case: (cfctr (Adds b4 (Adds b5 mr)) mc cp) cpc => // [cpc] p' Hrec.
Injection=> [] {p'} k [HkE HkF]; Pose h := [x](k (icpH g x)).
Step HhF: (invariant face h) =1 g.
  Move=> x; Apply/eqP; Apply: (fconnect_invariant HkF).
  By Rewrite: cface_icpH Sface fconnect1.
Def: Hg'E := (plain_ecpH g HgE).
Step HhE: (invariant edge h) =1
 (insertE (cat (sieve (Adds b4 (Adds b5 mr)) (cpring g)) (sieve mc (ctrenum cp)))).
  Move=> x; Rewrite: /invariant /h -icpH_edge; Apply: (etrans (HkE ?)).
  Rewrite: !mem_insertE // cpring_ecpH //.
  Rewrite: {2 (cpring g)}head_proper_cpring //.
  Rewrite: (eq_has (plain_orbit HgE x)) (eq_has (plain_orbit Hg'E (icpH g x))).
  Rewrite: !has_cat icpH_edge {sieve}lock {mem}lock /= -!lock.
  Rewrite: !has_sieve_adds !andbF !orFb orbCA -!orbA; Congr orb.
  Rewrite: /long_cpring /= Enode (negbE Hgp) /= andbF orFb orbCA; Congr orb.
  By Congr orb; Rewrite: -maps_sieve has_maps; Apply: eq_has => [y].
Case: {Hrec}(Hrec h); LeftBy Split.
Pose gc := (cpmap cpc); Move=> h' Hh' Eh.
Move: Hh' (coloring_proper_cpring gc Hh') => [Hh'E Hh'F] Hgcp.
Step EkefX: (k (edge (face (ecpH g)))) = (h g).
  Apply: (fconnect_invariant HkF); Apply connect1; Apply/eqP.
  By Rewrite: /= Enode (negbE Hgp).
Step HrgE: (all (invariant edge h) (sieve (Adds b4 (Adds b5 mr)) (cpring g))).
  Apply/allP=> [x Hx]; Rewrite: HhE mem_insertE //.
  Apply/hasP; Exists x; RightBy Apply connect0.
  By Rewrite: mem_cat /setU Hx.
Step HrgN: (fpath (finv node) (node g) (add_last (behead (cpring g)) (node g))).
  Rewrite: (fpath_finv (Inode g)) last_add_last belast_add_last -head_cpring.
  Move: (cycle_rev_cpring g).
  By Rewrite: head_cpring (cycle_path g) rev_adds last_add_last.
Case: b3 Hb HhE HrgE HkE Eh.
  Case: b1 {HbA} => //; Case: b2 => //; Case: b4 b5 => [|] [|] // _ _ _ HkE Eh.
  Exists h'; LeftBy Split.
  Rewrite: -/gc Eh head_proper_cpring // cpring_ecpH //.
  Rewrite: !maps_sieve !maps_adds -maps_comp.
  Rewrite: (fconnect_invariant HkF (cface_node_ecpH Hgp)) -/(h (node g)).
  Do 2 Congr Adds; Apply: eqP; Rewrite: -[u](eqcP (HkF u)) -EkefX.
  Apply: (etrans (HkE ?)).
  By Rewrite: insertE_cat mem_cat; Apply/orP; Right; Apply: setU11.
Case Hb12: (andb b1 b2).
  Case: b1 Hb12 HbA => //; Case: b2 => // [] _ HbA.
  Case: b4 => //; Case: b5 => // [] _ HhE HrgE HkE Eh.
  Step Hgcl: (long_cpring gc).
    Rewrite: size_long_cpring -(size_maps h') Eh; Move/(introT eqP): Emr HbA.
    Rewrite: -size_ring_cpmap -/g; Case: (cpring g) => [|x0 [|x1 p]] {x0 x1}//=.
    Rewrite: !ltnS !eqdSS; Elim: {}mr p => [|[|] m Hrec] [|x p] //=; Auto.
  Rewrite: (head_proper_cpring Hgp) head_proper_cpring //= in Eh.
  Injection: Eh => Eh EhX EhnX.
  Step EhfeX: (h' (face (edge gc))) = (h (face (edge g))).
    Rewrite: head_long_cpring //= in Eh; Move: HrgN Eh HrgE.
    Rewrite: head_proper_cpring //= drop0; Case/andP; Clear.
    Elim: {}mr {-2}(g::g) (drop (2) (cpring g)) => [|b m Hrec] // x [|y p] //=.
    Case/andP; Move/eqP=> Dy Hp; Rewrite: -(finv_eq_monic (Enode g) x) Dy.
    Case: b; RightBy Injection=> _.
    Move=> /= Eh; Case/andP; Move/eqcP=> [] Hmp.
    Rewrite: -(eqcP (HhF (edge y))); EAuto.
  Step Eh'A: (h' (node gc)) = (h' (face (edge gc))).
    Rewrite: EhnX EhfeX (eqcP (HhF (edge g))).
    Rewrite: /h -(fconnect_invariant HkF (cface_node_ecpH Hgp)).
    Transitivity (k (face (edge (node (ecpH g))))); Apply: eqP.
      Rewrite: eqd_sym [u](eqcP (HkF u)); Apply: (etrans (HkE ?)).
      Rewrite: head_cpring; Apply: setU11.
    Rewrite: Enode eqd_sym -[u](eqcP (HkF u)) /= Enode (negbE Hgp) set11.
    Apply: (etrans (HkE (ecpH g))).
    By Rewrite: cpring_ecpH //; Do 2 Apply: setU1r; Apply: setU11.
  Step Hh'FA: (invariant 1!(ecpA gc) face h') =1 gc.
    Rewrite: /invariant /= /ecpA_face; Move=> x.
    Case (cface (edge gc) (node gc)); LeftBy Apply: Hh'F.
    Case: (x =P (edge gc)) => [Dx | _].
      By Rewrite: /setA -(eqcP (Hh'F x)) Dx -Eh'A set11.
    Case: ((face x) =P (node gc)) => [Dx | _]; RightBy Apply: Hh'F.
    By Rewrite: /setA -(eqcP (Hh'F x)) Dx -Eh'A set11.
  Exists h'.
    Split; RightDone.
    Rewrite: /invariant /= /ecpA_edge /= -/gc; Move=> x.
    Case (cface (edge gc) (node gc)); RightBy Apply: Hh'E.
    Case: (x =P gc) => /= [Dx | _].
      Rewrite: -[y](eqcP (Hh'F y)) Enode Eh'A [y](eqcP (Hh'F y)) Dx; Apply: Hh'E.
    Case: (x =P (node (node gc))) => /= [Dx | _]; RightBy Apply: Hh'E.
    Rewrite: -[y](eqcP (Hh'F y)) -Eh'A -{(node gc)}Enode -Dx [y](eqcP (Hh'F y)).
    Apply: Hh'E.
  Rewrite: /cpmap -/cpmap -/gc cpring_ecpA Hgcl cpring_ecpH //=.
  By Rewrite: -maps_sieve -maps_comp; Rewrite: drop_behead in Eh.
Case: b1 b2 b4 b5 Hb12 {HbA} => [|] [|] // [|] [|]  // _ _;
   Rewrite: /cpmap -/cpmap -/gc.
 Move=> _ _ HkE Eh; Exists h'; LeftBy Split.
  Rewrite: Eh (head_proper_cpring Hgp) cpring_ecpH // !maps_sieve !maps_adds.
  Rewrite: -maps_comp; Congr Adds; Apply: eqP.
   Rewrite: /h -(fconnect_invariant HkF (cface_node_ecpH Hgp)) eqd_sym.
   Rewrite: -{1 ((ecpH g)::(dart ?))}Enode [u](eqcP (HkF u)).
   Apply: (etrans (HkE ?)); Rewrite: head_cpring; Apply: setU11.
 Move=> HhE HrgE HkE Eh.
  Pose k' := [u]if pick x in [x](cface u (icpK gc x)) then (h' x) else Color0.
  Step Hk'F : (invariant face k') =1 (ecpK gc).
    Move=> u; Apply/eqP; Rewrite: /k' -(eq_pick 2![x](cface u (icpK ? x))) //.
    Move=> x; Apply: cface1.
  Step Ek': (x : gc) (k' (icpK ? x)) = (h' x).
    Move=> x; Rewrite: /k'.
    Case: (pickP [y](cface (icpK (cpmap cpc) x) (icpK ? y))) => [y Hy | Hx].
      By Rewrite: cface_icpK Sface in Hy; Apply: (fconnect_invariant Hh'F).
    Case/idP: (Hx x); Apply connect0.
  Rewrite: (head_proper_cpring Hgp) (head_proper_cpring Hgcp) /= in Eh.
  Injection: Eh => Eh EhX EhnX.
  Step EkX: (k (ecpH g)) = (h' (node gc)).
    Apply: eqP; Rewrite: EhnX -{((ecpH g)::(dart ?))}Enode [u](eqcP (HkF u)).
    Rewrite: /h -(fconnect_invariant HkF (cface_node_ecpH Hgp)).
    Apply: (etrans (HkE ?)); Rewrite: head_cpring; Apply: setU11.
  Exists k'.
    Split; RightDone; Pose x0 := ((ecpN (ecpR' gc)) :: (ecpK gc)).
    Step Hk'EX: (invariant edge k' x0) = false.
      Rewrite: /invariant; Step []: (h' (face (edge gc))) = (k' (edge x0)).
        Rewrite: [u](eqcP (Hh'F u)) -Ek'; Apply: (fconnect_invariant Hk'F).
        By Apply connect1; Apply/eqP; Rewrite: /ecpK /x0 ecpR'_eq /= Enode set11.
      Step []: (k (ecpH g)) = (k' x0).
        Symmetry; Rewrite: EkX -Ek'; Apply: (fconnect_invariant Hk'F).
        By Apply connect1; Apply/eqP; Rewrite: /ecpK /x0 ecpR'_eq.
      Step []: (h (face (edge g))) = (h' (face (edge gc))).
        Move: HrgN HrgE (introT eqP Emr); Rewrite: -size_ring_cpmap -/g.
        Rewrite: (head_proper_cpring Hgp) /= !eqdSS ; Case/andP; Clear.
        Move: {-2}(g::g) (drop (2) (cpring g)) Eh.
        Elim: {}mr => [|b m Hrec] x [|y p] //= Eh;
          Case/andP; Move/eqP=> Dy; Rewrite: -(finv_eq_monic (Enode g) x) ~Dy.
          Step Hgcl: (long_cpring gc) = false.
            By Rewrite: size_long_cpring -(size_maps h') head_proper_cpring //= Eh.
          By Move/eqP: Hgcl; Case/esym.
        Case: b Eh => [|] /= Eh Hp.
          By Case/andP; Case/eqcP; Rewrite: -(eqcP (HhF (edge y))); EAuto.
        Step Hgcl: (long_cpring gc).
          By Rewrite: size_long_cpring -(size_maps h') head_proper_cpring //= Eh.
        By Rewrite: head_long_cpring // in Eh; Injection: Eh.
      Step []: (k (edge (ecpH g))) = (h (face (edge g))).
        Rewrite: (eqcP (HhF (edge g))); Symmetry; Apply: (fconnect_invariant HkF).
        By Apply: connect1; Apply/eqP; Rewrite: /= Enode (negbE Hgp) set11.
      Apply: (etrans (HkE ?)).
      Move: (uniq_ctrenum Hcp'); Rewrite: /cpmap -/cpmap -/g cpring_ecpH //.
      Rewrite: !cat_adds -2!cat1s 2!insertE_cat uniq_catC -catA uniq_cat.
      Case/and3P=> [_ Ug _]; Rewrite: -rot_size_cat has_rot -insertE_cat in Ug.
      Rewrite: has_sym catA in Ug; Move: {Ug}(hasPn Ug ? (setU11 ? ?)).
      Rewrite: !mem_insertE //; Move=> Ug; Apply/hasP=> [[v Hv Huv]].
      Case/hasP: Ug; Exists v; RightDone; Move: Hv; Rewrite: !mem_cat.
      Case/orP=> [Hv]; Apply/orP; RightBy Right; Apply: (mem_sieve Hv).
      By Left; Apply: (mem_sieve 2!(Adds true mr)).
    Move=> [||x] //; LeftBy Rewrite: /invariant eqd_sym.
    Rewrite: -{(Icp x)}/(icpK gc x) /invariant icpK_edge !Ek'; Apply: Hh'E.
  Rewrite: cpring_ecpK cpring_ecpH // maps_sieve !maps_adds -!maps_comp.
  Rewrite: (eq_maps 3!(comp k' (icpK gc)) Ek') Eh maps_sieve; Congr Adds.
  By Rewrite: EkX (fconnect_invariant Hk'F (cface_node_ecpK ?)) Ek'.
 Move=> HhE _ _ Eh; Exists h'; LeftBy Split.
  Rewrite: Eh (head_proper_cpring Hgp) cpring_ecpH // !maps_sieve !maps_adds.
  Rewrite: -maps_comp; Congr Adds; Apply: eqP.
   Rewrite: (fconnect_invariant HkF (cface_node_ecpH Hgp)).
   Rewrite: -{1 (g::g)}Enode [u](eqcP (HhF u)).
   Apply: (etrans (HhE ?)); Rewrite: head_cpring; Apply: setU11.
 Move=> HhE HrgE HkE Eh.
  Pose k' := [u]if pick x in [x](cface u (icpK gc x)) then (h' x) else Color0.
  Step Hk'F : (invariant face k') =1 (ecpK gc).
    Move=> u; Apply/eqP; Rewrite: /k' -(eq_pick 2![x](cface u (icpK ? x))) //.
    Move=> x; Apply: cface1.
  Step Ek': (x : gc) (k' (icpK ? x)) = (h' x).
    Move=> x; Rewrite: /k'.
    Case: (pickP [y](cface (icpK (cpmap cpc) x) (icpK ? y))) => [y Hy | Hx].
      By Rewrite: cface_icpK Sface in Hy; Apply: (fconnect_invariant Hh'F).
    Case/idP: (Hx x); Apply connect0.
  Rewrite: (head_proper_cpring Hgp) (head_proper_cpring Hgcp) /= in Eh.
  Injection: Eh => Eh EhX EhnX.
  Exists k'.
    Split; RightDone; Pose x0 := ((ecpN (ecpR' gc)) :: (ecpK gc)).
    Step Hk'EX: (invariant edge k' x0) = false.
      Rewrite: /invariant; Step []: (h' (face (edge gc))) = (k' (edge x0)).
        Rewrite: [u](eqcP (Hh'F u)) -Ek'; Apply: (fconnect_invariant Hk'F).
        By Apply connect1; Apply/eqP; Rewrite: /ecpK /x0 ecpR'_eq /= Enode set11.
      Step []: (h (face (edge g))) = (h' (face (edge gc))).
        Move: HrgN HrgE (introT eqP Emr); Rewrite: -size_ring_cpmap -/g.
        Rewrite: (head_proper_cpring Hgp) /= !eqdSS ; Case/andP; Clear.
        Move: {-2}(g::g) (drop (2) (cpring g)) Eh.
        Elim: {}mr => [|b m Hrec] x [|y p] //= Eh;
          Case/andP; Move/eqP=> Dy; Rewrite: -(finv_eq_monic (Enode g) x) ~Dy.
          Step Hgcl: (long_cpring gc) = false.
            By Rewrite: size_long_cpring -(size_maps h') head_proper_cpring //= Eh.
          By Move/eqP: Hgcl; Case/esym.
        Case: b Eh => [|] /= Eh Hp.
          By Case/andP; Case/eqcP; Rewrite: -(eqcP (HhF (edge y))); EAuto.
        Step Hgcl: (long_cpring gc).
          By Rewrite: size_long_cpring -(size_maps h') head_proper_cpring //= Eh.
        By Rewrite: head_long_cpring // in Eh; Injection: Eh.
      Step []: (k (edge (ecpH g))) = (h (face (edge g))).
        Rewrite: (eqcP (HhF (edge g))); Symmetry; Apply: (fconnect_invariant HkF).
        By Apply: connect1; Apply/eqP; Rewrite: /= Enode (negbE Hgp) set11.
      Step []: (k (node (ecpH g))) = (k' x0).
        Rewrite: (fconnect_invariant HkF (cface_node_ecpH Hgp)) -/(h (node g)).
        Symmetry; Rewrite: -EhnX -Ek'; Apply: (fconnect_invariant Hk'F).
        By Apply connect1; Apply/eqP; Rewrite: /ecpK /x0 ecpR'_eq.
      Step []: (k (edge (node (ecpH g)))) = (k (edge (ecpH g))).
        Rewrite: -[u](eqcP (HkF u)) Enode; Symmetry; Apply: eqP.
        Apply: (etrans (HkE ?)); Rewrite: cpring_ecpH //; Apply: setU11.
      Apply: (etrans (HkE ?)).
      Move: (uniq_ctrenum Hcp'); Rewrite: /cpmap -/cpmap -/g cpring_ecpH //.
      Rewrite: !cat_adds -cat1s insertE_cat uniq_cat; Case/and3P=> [_ Ug _].
      Rewrite: has_sym -cat_adds in Ug; Move: {Ug}(hasPn Ug ? (setU11 ? ?)).
      Rewrite: !mem_insertE //; Move=> Ug; Apply/hasP=> [[v Hv Huv]].
      Case/hasP: Ug; Exists v; RightDone; Move: Hv; Rewrite: !mem_cat.
      Case/orP=> [Hv]; Apply/orP; RightBy Right; Apply: (mem_sieve Hv).
      By Left; Apply: (mem_sieve 2!(Adds true mr)).
    Move=> [||x] //; LeftBy Rewrite: /invariant eqd_sym.
    Rewrite: -{(Icp x)}/(icpK gc x) /invariant icpK_edge !Ek'; Apply: Hh'E.
  Rewrite: cpring_ecpK cpring_ecpH // maps_sieve !maps_adds -!maps_comp.
  Rewrite: (eq_maps 3!(comp k' (icpK gc)) Ek') Eh maps_sieve; Congr Adds.
  Rewrite: (fconnect_invariant Hk'F (cface_node_ecpK ?)) Ek'.
  By Rewrite: (fconnect_invariant HkF (cface_node_ecpH Hgp)).
 Move=> HhE HrgE HkE Eh.
  Pose k' :=[u]if pick x in [x](cface u (icpU gc x)) then (h' x) else (k (ecpH g)).
  Step Hk'F : (invariant face k') =1 (ecpU gc).
    Move=> u; Apply/eqP; Rewrite: /k' -(eq_pick 2![x](cface u (icpU ? x))) //.
    Move=> x; Apply: cface1.
  Step Ek': (x : gc) (k' (icpU ? x)) = (h' x).
    Move=> x; Rewrite: /k'.
    Case: (pickP [y](cface (icpU gc x) (icpU ? y))) => [y Hy | Hx].
      By Rewrite: cface_icpU Sface in Hy; Apply: (fconnect_invariant Hh'F).
    Case/idP: (Hx x); Apply connect0.
  Step Ek'X: (k' (ecpU gc)) = (k (ecpH g)).
    Rewrite: /k'; Case: (pickP [y](cface (ecpU gc) (icpU ? y))) => [y Hy | Hx] //.
    By Rewrite: cface_ecpU in Hy.
  Rewrite: (head_proper_cpring Hgp) head_cpring /= in Eh.
  Step Ek'eX: (h (face (edge g))) = (k' (edge (ecpU gc))).
    Step []: (h' (node gc)) = (k' (edge (ecpU gc))).
      By Rewrite: -[u](eqcP (Hk'F u)) -Ek'.
    Move: HrgN HrgE; Rewrite: (head_proper_cpring Hgp) /=.
    Case/andP=> [_ H]; Case/and3P=> [_ _ H']; Move: H H'.      
    Move: {-2}(g::g) (drop (2) (cpring g)) Eh.
    Elim: {}mr => [|b m Hrec] x [|y p] //= Eh.
    Case/andP; Move/eqP=> Dy; Rewrite: -(finv_eq_monic (Enode g) x) ~Dy.
    Case: b Eh => [|] /= Eh Hp; RightBy Injection Eh.
    By Case/andP; Case/eqcP; Rewrite: -(eqcP (HhF (edge y))); EAuto.
  Exists k'.
    Split; RightDone.
    Step Hk'EX: (invariant edge k' (ecpU gc)) = false.
      Rewrite: /invariant Ek'X -Ek'eX.
      Step []: (k (edge (ecpH g))) = (h (face (edge g))).
        Rewrite: (eqcP (HhF (edge g))); Symmetry; Apply: (fconnect_invariant HkF).
        By Apply: connect1; Apply/eqP; Rewrite: /= Enode (negbE Hgp) set11.
      Apply: (etrans (HkE ?)).
      Move: (uniq_ctrenum Hcp'); Rewrite: /cpmap -/cpmap -/g cpring_ecpH //.
      Rewrite: !cat_adds -2!cat1s 2!insertE_cat !uniq_cat.
      Case/and5P=> [_ _ _ Ug _]; Rewrite: has_sym in Ug.
      Move: {Ug}(hasPn Ug ? (setU11 ? ?)).
      Rewrite: !mem_insertE //; Move=> Ug; Apply/hasP=> [[v Hv Huv]].
      Case/hasP: Ug; Exists v; RightDone; Move: Hv; Rewrite: !mem_cat.
      Case/orP=> [Hv]; Apply/orP; RightBy Right; Apply: (mem_sieve Hv).
      By Left; Apply: (mem_sieve 2!mr).
    Move=> [||x] //; LeftBy Rewrite: /invariant eqd_sym.
    Rewrite: -{(Icp x)}/(icpU gc x) /invariant -icpU_edge !Ek'; Apply: Hh'E.
  Rewrite: cpring_ecpU cpring_ecpH // maps_sieve !maps_adds -!maps_comp.
  Rewrite: (eq_maps 3!(comp k' (icpU gc)) Ek') head_cpring maps_adds Eh Ek'X.
  Rewrite maps_sieve; Congr Adds.
  Rewrite: (fconnect_invariant HkF (cface_node_ecpH Hgp)) -/(h (node g)).
  Apply: (etrans (esym Ek'eX)); Transitivity (h g); Apply: eqP.
    Rewrite: [x](eqcP (HhF x)); Apply: (etrans (HhE ?)).
    Rewrite: head_proper_cpring //; Do 2 Apply: setU1r; Apply: setU11.
  Rewrite: -{1 (g::g)}Enode [x](eqcP (HhF x)); Apply: (etrans (HhE ?)).
  Rewrite: head_cpring; Apply: setU11.
 Move=> HhE HrgE HkE Eh.
  Pose k' :=[u]if pick x in [x](cface u (icpY gc x)) then (h' x) else (k (ecpH g)).
  Step Hk'F : (invariant face k') =1 (ecpY gc).
    Move=> u; Apply/eqP; Rewrite: /k' -(eq_pick 2![x](cface u (icpY ? x))) //.
    Move=> x; Apply: cface1.
  Step Ek': (x : gc) (k' (icpY ? x)) = (h' x).
    Move=> x; Rewrite: /k'.
    Case: (pickP [y](cface (icpY gc x) (icpY ? y))) => [y Hy | Hx].
      By Rewrite: cface_icpY Sface in Hy; Apply: (fconnect_invariant Hh'F).
    Case/idP: (Hx x); Apply connect0.
  Step Ek'X: (k' (ecpY gc)) = (k (ecpH g)).
    Rewrite: /k'; Case: (pickP [y](cface (ecpY gc) (icpY ? y))) => [y Hy | Hx] //.
    By Rewrite: cface_ecpY in Hy.
  Rewrite: (head_proper_cpring Hgp) head_cpring /= in Eh.
  Injection: Eh => Eh EhnX.
  Step Ehng: (h (node g)) = (h g).
    Symmetry; Rewrite: -{1 (g::g)}Enode [x](eqcP (HhF x)); Apply: eqP.
    Apply: (etrans (HhE ?)); Rewrite: head_cpring; Apply: setU11. 
  Step Ek'nX: (k' (node (ecpY ?))) = (k (node (ecpH ?))).
    Rewrite: (fconnect_invariant Hk'F (cface_node_ecpY ?)) Ek' EhnX -Ehng.
    By Rewrite: (fconnect_invariant HkF (cface_node_ecpH Hgp)).
  Step Eh'X: (h' gc) = (h (face (edge g))).
    Rewrite: head_proper_cpring //= in Eh; Move: HrgN HrgE {HhE HkE}.
    Rewrite: head_proper_cpring //=.
    Case/andP=> [_ H]; Case/andP=> [_ H']; Move: H H'.
    Elim: {}mr {-2}(g::g) (drop (2) (cpring g)) Eh => [|b m Hrec] x [|y p] //= Eh.
    Case/andP; Move/eqP=> Dy Hp; Rewrite: -(finv_eq_monic (Enode g) x) ~Dy.
    Case: b Eh => [|] /= Eh; RightBy Injection: Eh.
    Case/andP; Case/eqcP; Rewrite: -[z](eqcP (HhF z)); EAuto.
  Exists k'.
    Split; RightDone.
    Step Hk'EX: (u : (ecpY ?)) (cface u (ecpY ?)) -> (invariant edge k' u) = false.
      Move=> u HuX; Rewrite: /invariant (fconnect_invariant Hk'F HuX) Ek'X.
      Step HeuX: (adj (ecpY ?) (edge u)) By Rewrite: -(adjF HuX) adjE.
      Rewrite: (adj_ecpY Hgcp) /fband in HeuX; Case/hasP: HeuX {HuX} => [v].
      Case/mapsP=> [y Hy []] {v} H; Rewrite: ~{u H}(fconnect_invariant Hk'F H) Ek'.
      Move: HkE (uniq_ctrenum Hcp') {x Hx}.
      Rewrite: /cpmap -/cpmap -/g cpring_ecpH //; Move=> HkE.
      Rewrite: -!cat1s -!catA catA insertE_cat uniq_cat has_sym.
      Case/and3P=> [_ Ug _].
      Rewrite: mem_seq2 in Hy; Case/orP: Hy; Case/eqP {y}.
        Rewrite: EhnX -Ehng /h -(fconnect_invariant HkF (cface_node_ecpH Hgp)).
        Rewrite: eqd_sym -{1 ((ecpH g)::(dart ?))}Enode [u](eqcP (HkF u)).
        Apply: (etrans (HkE ?)); Rewrite: mem_insertE // has_cat !has_sieve_adds.
        Rewrite: !andFb !orFb -has_cat; Apply/hasP=> [[u Hu HuX]].
        Move: (hasPn Ug ? (setU11 ? ?)); Rewrite: mem_insertE //; Case/hasP.
        Exists u; RightDone; Rewrite: mem_cat; Apply/orP.
        Rewrite: mem_cat in Hu; Case/orP: Hu => [Hu]; Move: (mem_sieve Hu); Auto.
      Rewrite: Eh'X; Step []: (k (edge (ecpH g))) = (h (face (edge g))).
        Rewrite: [x](eqcP (HhF x)); Symmetry; Apply: (fconnect_invariant HkF).
        By Apply: connect1; Apply/eqP; Rewrite: /= Enode (negbE Hgp) /= set11.
      Apply: (etrans (HkE ?)); Rewrite: mem_insertE // has_cat !has_sieve_adds.
      Rewrite: !andFb !orFb -has_cat; Apply/hasP=> [[u Hu HuX]].
      Move: (hasPn Ug ? (setU1r ? (setU1r ? (setU11 ? ?)))).
      Rewrite: mem_insertE //; Case/hasP.
      Exists u; RightDone; Rewrite: mem_cat; Apply/orP.
      Rewrite: mem_cat in Hu; Case/orP: Hu => [Hu]; Move: (mem_sieve Hu); Auto.
    Move=> u; Case: (fband_icpY 2!gc u) => [[x Hx] | Hu].
      Case: (fband_icpY 2!gc (edge u)) => [[y Hy] | Heu].
        Rewrite: /invariant (fconnect_invariant Hk'F Hx).
        Rewrite: (fconnect_invariant Hk'F Hy) !Ek'.
        Step Hxy: (adj x y).
          By Rewrite: -(adj_icpY gc); Apply/adjP; Exists u; Rewrite: // Sface.
        Case/adjP: Hxy => [z Hxz Hzy]; Rewrite: (fconnect_invariant Hh'F Hxz).
        Rewrite: -(fconnect_invariant Hh'F Hzy); Apply: Hh'E.
      Step Deeu: (edge (edge u)) = u.
        By Move: Heu {Hx}; Rewrite: cface_ecpY; Case: u => [||[||z]].
      By Rewrite: /invariant eqd_sym -{1 u}Deeu; Apply: Hk'EX; Rewrite Sface.
    By Apply: Hk'EX; Rewrite Sface.
  Rewrite: /cpmap -/cpmap cpring_ecpY cpring_ecpH // !maps_sieve !maps_adds.
  Rewrite:  Ek'nX Ek'X -!maps_comp (eq_maps 3!(comp k' (icpY gc)) Ek') Eh.
  By Rewrite maps_sieve.
 Move=> HhE HrgE HkE Eh.
  Pose k' :=[u]if pick x in [x](cface u (icpY gc x)) then (h' x) else (k (ecpH g)).
  Step Hk'F : (invariant face k') =1 (ecpY gc).
    Move=> u; Apply/eqP; Rewrite: /k' -(eq_pick 2![x](cface u (icpY ? x))) //.
    Move=> x; Apply: cface1.
  Step Ek': (x : gc) (k' (icpY ? x)) = (h' x).
    Move=> x; Rewrite: /k'.
    Case: (pickP [y](cface (icpY gc x) (icpY ? y))) => [y Hy | Hx].
      By Rewrite: cface_icpY Sface in Hy; Apply: (fconnect_invariant Hh'F).
    Case/idP: (Hx x); Apply connect0.
  Step Ek'X: (k' (ecpY gc)) = (k (ecpH g)).
    Rewrite: /k'; Case: (pickP [y](cface (ecpY gc) (icpY ? y))) => [y Hy | Hx] //.
    By Rewrite: cface_ecpY in Hy.
  Rewrite: (head_proper_cpring Hgp) head_cpring /= in Eh.
  Injection: Eh => Eh EhnX.
  Step Ehfeg: (h (face (edge g))) = (h g).
    Rewrite: [x](eqcP (HhF x)); Apply: eqP.
    Apply: (etrans (HhE ?)); Rewrite: head_proper_cpring //; Apply: setU11. 
  Step Ek'nX: (k' (node (ecpY ?))) = (k (node (ecpH ?))).
    Rewrite: (fconnect_invariant Hk'F (cface_node_ecpY ?)) Ek' EhnX.
    By Rewrite: (fconnect_invariant HkF (cface_node_ecpH Hgp)).
  Step Eh'X: (h' gc) = (h (face (edge g))).
    Rewrite: head_proper_cpring //= in Eh; Move: HrgN HrgE {HhE HkE}.
    Rewrite: head_proper_cpring //=.
    Case/andP=> [_ H]; Case/andP=> [_ H']; Move: H H'.
    Elim: {}mr {-2}(g::g) (drop (2) (cpring g)) Eh => [|b m Hrec] x [|y p] //= Eh.
    Case/andP; Move/eqP=> Dy Hp; Rewrite: -(finv_eq_monic (Enode g) x) ~Dy.
    Case: b Eh => [|] /= Eh; RightBy Injection: Eh.
    Case/andP; Case/eqcP; Rewrite: -[z](eqcP (HhF z)); EAuto.
  Exists k'.
    Split; RightDone.
    Step Hk'EX: (u : (ecpY ?)) (cface u (ecpY ?)) -> (invariant edge k' u) = false.
      Move=> u HuX; Rewrite: /invariant (fconnect_invariant Hk'F HuX) Ek'X.
      Step HeuX: (adj (ecpY ?) (edge u)) By Rewrite: -(adjF HuX) adjE.
      Rewrite: (adj_ecpY Hgcp) /fband in HeuX; Case/hasP: HeuX {HuX} => [v].
      Case/mapsP=> [y Hy []] {v} H; Rewrite: ~{u H}(fconnect_invariant Hk'F H) Ek'.
      Move: HkE (uniq_ctrenum Hcp') {x Hx}.
      Rewrite: /cpmap -/cpmap -/g cpring_ecpH //; Move=> HkE.
      Rewrite: -!cat1s -!catA catA insertE_cat uniq_cat has_sym.
      Case/and3P=> [_ Ug _].
      Rewrite: mem_seq2 in Hy; Case/orP: Hy; Case/eqP {y}.
        Rewrite: EhnX /h -(fconnect_invariant HkF (cface_node_ecpH Hgp)).
        Rewrite: eqd_sym -{1 ((ecpH g)::(dart ?))}Enode [u](eqcP (HkF u)).
        Apply: (etrans (HkE ?)); Rewrite: mem_insertE // has_cat !has_sieve_adds.
        Rewrite: !andFb !orFb -has_cat; Apply/hasP=> [[u Hu HuX]].
        Move: (hasPn Ug ? (setU11 ? ?)); Rewrite: mem_insertE //; Case/hasP.
        Exists u; RightDone; Rewrite: mem_cat; Apply/orP.
        Rewrite: mem_cat in Hu; Case/orP: Hu => [Hu]; Move: (mem_sieve Hu); Auto.
      Rewrite: Eh'X; Step []: (k (edge (ecpH g))) = (h (face (edge g))).
        Rewrite: [x](eqcP (HhF x)); Symmetry; Apply: (fconnect_invariant HkF).
        By Apply: connect1; Apply/eqP; Rewrite: /= Enode (negbE Hgp) /= set11.
      Apply: (etrans (HkE ?)); Rewrite: mem_insertE // has_cat !has_sieve_adds.
      Rewrite: !andFb !orFb -has_cat; Apply/hasP=> [[u Hu HuX]].
      Move: (hasPn Ug ? (setU1r ? (setU1r ? (setU11 ? ?)))).
      Rewrite: mem_insertE //; Case/hasP.
      Exists u; RightDone; Rewrite: mem_cat; Apply/orP.
      Rewrite: mem_cat in Hu; Case/orP: Hu => [Hu]; Move: (mem_sieve Hu); Auto.
    Move=> u; Case: (fband_icpY 2!gc u) => [[x Hx] | Hu].
      Case: (fband_icpY 2!gc (edge u)) => [[y Hy] | Heu].
        Rewrite: /invariant (fconnect_invariant Hk'F Hx).
        Rewrite: (fconnect_invariant Hk'F Hy) !Ek'.
        Step Hxy: (adj x y).
          By Rewrite: -(adj_icpY gc); Apply/adjP; Exists u; Rewrite: // Sface.
        Case/adjP: Hxy => [z Hxz Hzy]; Rewrite: (fconnect_invariant Hh'F Hxz).
        Rewrite: -(fconnect_invariant Hh'F Hzy); Apply: Hh'E.
      Step Deeu: (edge (edge u)) = u.
        By Move: Heu {Hx}; Rewrite: cface_ecpY; Case: u => [||[||z]].
      By Rewrite: /invariant eqd_sym -{1 u}Deeu; Apply: Hk'EX; Rewrite Sface.
    By Apply: Hk'EX; Rewrite Sface.
  Rewrite: /cpmap -/cpmap cpring_ecpY cpring_ecpH // !maps_sieve !maps_adds.
  Rewrite:  Ek'nX Ek'X -!maps_comp (eq_maps 3!(comp k' (icpY gc)) Ek') Eh.
  By Rewrite maps_sieve.
Move=> HhE HrgE HkE Eh.
Pose k' :=[u]if pick x in [x](cface u (icpH gc x)) then (h' x) else (k (ecpH g)).
Step Hk'F : (invariant face k') =1 (ecpH gc).
  Move=> u; Apply/eqP; Rewrite: /k' -(eq_pick 2![x](cface u (icpH ? x))) //.
  Move=> x; Apply: cface1.
Step Ek': (x : gc) (k' (icpH ? x)) = (h' x).
  Move=> x; Rewrite: /k'.
  Case: (pickP [y](cface (icpH gc x) (icpH ? y))) => [y Hy | Hx].
    By Rewrite: cface_icpH Sface in Hy; Apply: (fconnect_invariant Hh'F).
  Case/idP: (Hx x); Apply connect0.
Step Ek'X: (k' (ecpH gc)) = (k (ecpH g)).
  Rewrite: /k'; Case: (pickP [y](cface (ecpH gc) (icpH ? y))) => [y Hy | Hx] //.
  By Rewrite: cface_ecpH in Hy.
Rewrite: (head_proper_cpring Hgp) head_proper_cpring //= in Eh.
Injection: Eh => Eh EhX EhnX.
Step Ek'nX: (k' (node (ecpH ?))) = (k (node (ecpH ?))).
  Rewrite: (fconnect_invariant Hk'F (cface_node_ecpH Hgcp)) Ek' EhnX.
  By Rewrite: (fconnect_invariant HkF (cface_node_ecpH Hgp)).
Step Eh'feX: (h' (face (edge gc))) = (h (face (edge g))).
  Move: HrgN HrgE (introT eqP Emr) {HhE HkE}; Rewrite: -size_ring_cpmap -/g.
  Rewrite: head_proper_cpring //= !eqdSS; Case/andP; Clear.
  Elim: {}mr {-2}(g::g) (drop (2) (cpring g)) Eh => [|b m Hrec] x [|y p] //= Eh;
    Case/andP; Move/eqP=> Dy Hp; Rewrite: -(finv_eq_monic (Enode g) x) ~Dy.
    Step Hgcl: (long_cpring gc) = false.
      By Rewrite: size_long_cpring -(size_maps h') head_proper_cpring //= Eh.
    By Rewrite: -EhnX; Case/eqP: Hgcl.
  Case: b Eh => [|] /= Eh.
    By Case/andP; Case/eqcP; Rewrite: -[z](eqcP (HhF z)); EAuto.
  Step Hgcl: (long_cpring gc).
    By Rewrite: size_long_cpring -(size_maps h') head_proper_cpring //= Eh.
  By Rewrite: (head_long_cpring Hgcl) in Eh; Injection: Eh.
Exists k'.
  Split; RightDone.
  Step Hk'EX: (u : (ecpH ?)) (cface u (ecpH ?)) -> (invariant edge k' u) = false.
    Move=> u HuX; Rewrite: /invariant (fconnect_invariant Hk'F HuX) Ek'X.
    Step HeuX: (adj (ecpH ?) (edge u)) By Rewrite: -(adjF HuX) adjE.
    Rewrite: (adj_ecpH Hgcp) /fband in HeuX; Case/hasP: HeuX {HuX} => [v].
    Case/mapsP=> [y Hy []] {v} H; Rewrite: ~{u H}(fconnect_invariant Hk'F H) Ek'.
    Move: HkE (uniq_ctrenum Hcp') {x Hx}.
    Rewrite: /cpmap -/cpmap -/g cpring_ecpH //; Move=> HkE.
    Rewrite: -!cat1s -!catA catA insertE_cat uniq_cat has_sym.
    Case/and3P=> [_ Ug Ug']; Rewrite: insertE_cat uniq_catC -insertE_cat in Ug'.
    Simpl in Ug'; Case/andP: Ug' => [Ug' _]; Rewrite: /= /setU1 in Ug'; Move: Ug'.
    Repeat (Case/norP; Clear); Move=> Ug'.
    Rewrite: mem_seq3 in Hy; Case/or3P: Hy; Case/eqP {y}.
        Rewrite: EhnX /h -(fconnect_invariant HkF (cface_node_ecpH Hgp)).
        Rewrite: eqd_sym -{1 ((ecpH g)::(dart ?))}Enode [u](eqcP (HkF u)).
        Apply: (etrans (HkE ?)); Rewrite: mem_insertE // has_cat !has_sieve_adds.
        Rewrite: !andFb !orFb -has_cat; Apply/hasP=> [[u Hu HuX]].
        Move: (hasPn Ug ? (setU11 ? ?)); Rewrite: mem_insertE //; Case/hasP.
        Exists u; RightDone; Rewrite: mem_cat; Apply/orP.
        Rewrite: mem_cat in Hu; Case/orP: Hu => [Hu]; Move: (mem_sieve Hu); Auto.
      Rewrite: EhX -[u](eqcP (HkF u)).
      Step []: (k (edge (face (ecpH g)))) = (h g).
        Apply: (fconnect_invariant HkF); Apply: connect1; Apply/eqP.
        By Rewrite: /= Enode (negbE Hgp).
      Apply: (etrans (HkE ?)); Rewrite: mem_insertE //=.
      Apply/hasP=> [[u Hu HuX]]; Move: Ug'; Rewrite: (mem_insertE Hg'E); Case/hasP.
      Exists u; RightDone; Rewrite: mem_cat; Apply/orP.
      Rewrite: mem_cat in Hu; Case/orP: Hu => [Hu]; Move: (mem_sieve Hu); Auto.
    Rewrite: Eh'feX; Step []: (k (edge (ecpH g))) = (h (face (edge g))).
      Rewrite: [x](eqcP (HhF x)); Symmetry; Apply: (fconnect_invariant HkF).
      By Apply: connect1; Apply/eqP; Rewrite: /= Enode (negbE Hgp) /= set11.
    Apply: (etrans (HkE ?)); Rewrite: mem_insertE // has_cat !has_sieve_adds.
    Rewrite: !andFb !orFb -has_cat; Apply/hasP=> [[u Hu HuX]].
    Move: (hasPn Ug ? (setU1r ? (setU1r ? (setU11 ? ?)))).
    Rewrite: mem_insertE //; Case/hasP.
    Exists u; RightDone; Rewrite: mem_cat; Apply/orP.
    Rewrite: mem_cat in Hu; Case/orP: Hu => [Hu]; Move: (mem_sieve Hu); Auto.
  Move=> u; Case: (fband_icpH 2!gc u) => [[x Hx] | Hu].
    Case: (fband_icpH 2!gc (edge u)) => [[y Hy] | Heu].
      Rewrite: /invariant (fconnect_invariant Hk'F Hx).
      Rewrite: (fconnect_invariant Hk'F Hy) !Ek'.
      Step Hxy: (adj x y).
        By Rewrite: -(adj_icpH gc); Apply/adjP; Exists u; Rewrite: // Sface.
      Case/adjP: Hxy => [z Hxz Hzy]; Rewrite: (fconnect_invariant Hh'F Hxz).
      Rewrite: -(fconnect_invariant Hh'F Hzy); Apply: Hh'E.
    Step Deeu: (edge (edge u)) = u.
      By Move: Heu {Hx}; Rewrite: cface_ecpH; Case: u => [||[||[||z]]].
    By Rewrite: /invariant eqd_sym -{1 u}Deeu; Apply: Hk'EX; Rewrite Sface.
  By Apply: Hk'EX; Rewrite Sface.
Rewrite: /cpmap -/cpmap !cpring_ecpH // !maps_sieve !maps_adds.
Rewrite:  Ek'nX Ek'X -!maps_comp (eq_maps 3!(comp k' (icpH gc)) Ek') Eh.
By Rewrite maps_sieve.
Qed.

Lemma sparse_cfctr : (mr, mc : bitseq; cp : cprog)
  (size mr) = (cprsize cp) -> (size mc) = (ctrmsize cp) ->
  let g = (cpmap cp) in let r = (cpring g) in
  let cc = (cat (maps edge (sieve mr r)) (insertE (sieve mc (ctrenum cp)))) in
  if (cfctr mr mc cp) is (Some _) then (sparse (Adds g cc)) else true.
Proof.
Move=> /= mr mc cp; Elim: cp mr mc => [|s cp Hrec] mr mc //.
Move: (cfctr_config_prog mr mc (Adds s cp)).
Case Dcpc: (cfctr mr mc (Adds s cp)) => // [cpc].
Case: s Dcpc => // [n||] Dcpc Hcp' Emr Emc;
  Def: Hcp := (config_prog_cubic Hcp'); Simpl in Dcpc Hcp Emr Emc;
  Move: Hrec (cpmap_plain Hcp) (cpmap_cubic Hcp) (cpmap_proper Hcp);
  Rewrite: /cpmap -/cpmap; Pose g := (cpmap cp); Move=> Hrec HgE HgN Hgp.
    Rewrite: cpring_ecpR /= -(rot_rotr n mr).
    Rewrite: -(size_rotr n mr) in Emr; Move: Dcpc (Hrec ? ? Emr Emc).
    Case: (cfctr (rotr n mr) mc cp) => //= [cp'] _ {cp' cpc}; Apply: etrans.
    Apply: simple_perm.
      Move=> y; Congr orb.
        Rewrite: !(Sface (permF g) y); Symmetry; Apply: (!same_cnode g).
        Apply: fconnect_iter.
      Apply: eq_has_r => [x] {y}; Rewrite: !mem_cat; Congr orb.
      Rewrite: -{x}(Eface g) !(mem_maps (Iedge g)).
      By Apply: mem_sieve_rot; Rewrite: /g size_ring_cpmap.
    Rewrite: /= !size_cat !size_maps; Congr S; Congr addn; Rewrite: /rot sieve_cat.
      Rewrite: -rot_size_cat size_rot -sieve_cat ?cat_take_drop //.
      By Rewrite: !size_take Emr -size_ring_cpmap.
    By Rewrite: !size_drop Emr -size_ring_cpmap.
  Rewrite: /g.
  Case Dcp: cp mc mr Emc Emr Dcpc => [|s cp'] [|b3 mc] // [|b1 [|b2 mr]] //.
    Case: mr {cp Dcp g Hrec Hcp Hcp' HgE HgN Hgp} => [|b3 [|b4 mr]] //.
    By Case: b1 b2 b3 => [|] [|] [|].
  Rewrite: -Dcp -/g; Step Hg'E: (plain (ecpY g)) By Apply: plain_ecpY.
  Case Hb123: (nsp b1 b2 b3) => // [] Emc Emr; Simpl in Emr Emc.
  Injection: Emr => Emr; Injection: Emc => Emc.
  Move: {Hrec}(Hrec (Adds b3 mr) mc Emr Emc).
  Case: (cfctr (Adds b3 mr) mc cp) => // [p] Hrec _ {p cpc}.
  Step []: (maps (icpY g) (Adds (node g) (ctrenum cp))) = (ctrenum (Adds CpY cp)).
    By Rewrite: /= /g Dcp.
  Move: Hrec; Pose p := (cat (maps edge (sieve (Adds b3 mr) (cpring g)))
                             (insertE (sieve mc (ctrenum cp)))).
  Rewrite: sparse_adds -(eq_has (mem_cpring g)); Move/andP=> [Up Hp].
  Step HpY: (sparse (Adds (ecpY g) (maps (icpY g) (Adds (node g) p)))).
    Rewrite: maps_adds !sparse_adds; Apply/and3P; Split.
        Rewrite: -(eq_has (mem_cpring (ecpY g))) cpring_ecpY -maps_adds.
        Apply/hasP=> [[u]]; Case/mapsP=> /= [y Hy []] {u} Hry.
        Rewrite: /setU1 /= (mem_maps (icpY_inj 2!g)) in Hry.
        Case/setU1P: Hy => [Dy | Hy].
          By Move: (uniq_cpring g); Rewrite: head_cpring Dy /= Hry.
        By Case/hasP: Up; Exists y; RightBy Apply mem_behead.
      Apply/hasP=> [[u]]; Case/mapsP=> [y Hy []] {u} Hry; Rewrite Snode in Hry.
      Def: Hy' := (hasPn Up y Hy); Case/idP: {}Hy'.
      By Rewrite: mem_cpring cnode1 Snode -(cnode_injcp 1!(seq1 CpY) 3!y).
    Elim: p Up Hp => [|x p Hrec] //=; Move/norP=> [Hx Up].
    Rewrite: sparse_adds (!sparse_adds (ecpY g)).
    Move/andP=> [Hpx Hp]; Apply/andP; Split; RightBy Apply: Hrec.
    Apply/hasP=> [[u]]; Case/mapsP=> [y Hy []] Hxy {u}.
    Case/hasP: Hpx; Exists y; LeftDone.
    By Rewrite: -(cnode_injcp 1!(seq1 CpY) 3!x).
  Move: HpY; Rewrite: -maps_sieve /p head_cpring cpring_ecpY -!cat1s !sieve_cat //.
  Rewrite: !maps_cat !insertE_cat -maps_sieve -!maps_comp -!catA.
  Rewrite: -rot_size_cat sparse_rot -!catA -/g; Move=> HpY.
  Rewrite: -rot_size_cat sparse_rot -!catA 2!catA sparse_catCA -!catA.
  Move: (sieve mr (behead (cpring g))) (!sieve g mc (ctrenum cp)) HpY => r1 r2.
  Pose r1' := (maps (comp (icpY g) edge) r1).
  Pose r2' := (insertE (maps (icpY g) r2)).
  Step []: r1' = (maps (comp edge (icpY g)) r1) By Done.
  Step []: r2' = (maps (icpY g) (insertE r2)).
    By Rewrite: ~/r2'; Elim: r2 => // *; Repeat Congr Adds.
  Move: {r1 r2 r1' r2'}(cat r1' (cat r2' (seq1 (ecpY g)))) => r Hrec.
  Rewrite: {1 cat}lock catA -lock sparse_catCA -!catA.
  Case: b1 b2 b3 Hb123 Hrec {p Up Hp Emc Emr} => [|] [|] [|] //= _;
    Rewrite: !(!sparse_adds (ecpY g)).
      By Rewrite: (eq_has (cnode1 (icpY g (node g)))) /= set11 /=.
    By Rewrite: 2![u : (ecpY g)](eq_has (cnode1 u)) /= set11 /=.
  By Case/andP.
Case: mc mr Emc Emr Dcpc => [|b3 [|b4 [|b5 mc]]] [|b1 [|b2 mr]] // Emc Emr.
Simpl in Emr Emc; Injection: Emc => Emc.
Case Hb: (orb (nsp b3 b1 b4) (nsp b3 b2 b5)); LeftDone.
Case (and3b b1 b2 (all [b:bool]b mr)); LeftDone.
Move: {Hrec}(Hrec (Adds b4 (Adds b5 mr)) mc Emr Emc).
Case: (cfctr (Adds b4 (Adds b5 mr)) mc cp) => // [p'] Hrec _ {cpc p'}.
Def: Hg'E := (plain_ecpH g HgE).
Step []: (Adds (face (ecpH g))
           (maps (icpH g) (Adds (node g) (Adds g (ctrenum cp)))))
     = (ctrenum (Adds CpH cp)) By Done.
Move: Hrec; Pose p := (cat (maps edge (sieve (Adds b4 (Adds b5 mr)) (cpring g)))
                           (insertE (sieve mc (ctrenum cp)))).
Rewrite: sparse_adds -(eq_has (mem_cpring g)); Move/andP=> [Up Hp].
Step HpH: (sparse (Adds (ecpH g) (maps (icpH g) (Adds (node g) (Adds g p))))).
  Rewrite: !maps_adds !sparse_adds; Apply/and4P; Split.
        Rewrite: -(eq_has (mem_cpring (ecpH g))) cpring_ecpH // -!maps_adds.
        Apply/hasP=> [[u]]; Case/mapsP=> /= [y Hy []] {u} Hry.
        Rewrite: /long_cpring /= Enode (negbE Hgp) /setU1 /= in Hry.
        Rewrite: (mem_maps (icpH_inj 2!g)) in Hry.
        Move: (uniq_cpring g); Rewrite: head_proper_cpring //=.
        Case/setU1P: Hy => [Dy | Hy]; LeftBy Rewrite: Dy /setU1 Hry orbT.
        Case/setU1P: Hy => [Dy | Hy]; LeftBy Rewrite: {5 (g::g)}Dy Hry /= andbF.
        By Case/hasP: Up; Exists y; RightBy Exact (mem_drop Hry).
      Rewrite: -maps_adds.
      Apply/hasP=> [[u]]; Case/mapsP=> [y Hy []] {u} Hry; Rewrite Snode in Hry.
      Simpl in Hy; Case/setU1P: Hy => [Dy | Hy].
        Move: Hry; Rewrite: fconnect_orbit /orbit.
        Step HyN: (setC (rev (cpring (ecpH g))) (icpH g y)).
          Rewrite: -Dy /setC mem_rev cpring_ecpH //= /setU1.
          Rewrite: /long_cpring /= Enode (negbE Hgp) /= (mem_maps (icpH_inj 2!g)).
          Move: (uniq_cpring g); Rewrite: head_proper_cpring //= drop0.
          By Case/andP; Clear; Case/andP.
        Pose Hg'N := (cubic_ecpH HgN); Rewrite: /quasicubic /cubicb in Hg'N.
        Rewrite: (eqnP (subsetP Hg'N ? HyN)) -Dy /= (negbE Hgp) /= set11 /=.
        By Rewrite: /setU1 /= /eqd /= /eqd /= /eqd /= (negbE Hgp).
      Def: Hy' := (hasPn Up y Hy); Case/idP: {}Hy'.
      By Rewrite: mem_cpring cnode1 Snode -(cnode_injcp 1!(seq1 CpH) 3!y).
    Apply/hasP=> [[u]]; Case/mapsP=> [y Hy []] {u} Hry; Rewrite Snode in Hry.
    Def: Hy' := (hasPn Up y Hy); Case/idP: {}Hy'.
    By Rewrite: mem_cpring Snode -(cnode_injcp 1!(seq1 CpH) 3!y).
  Elim: p Up Hp => [|x p Hrec] //=; Move/norP=> [Hx Up].
  Rewrite: sparse_adds (!sparse_adds (ecpH g)).
  Move/andP=> [Hpx Hp]; Apply/andP; Split; RightBy Apply: Hrec.
  Apply/hasP=> [[u]]; Case/mapsP=> [y Hy []] Hxy {u}.
  Case/hasP: Hpx; Exists y; LeftDone.
  By Rewrite: -(cnode_injcp 1!(seq1 CpH) 3!x).
Move: HpH {Up Hp}.
Rewrite: ~/p head_proper_cpring // cpring_ecpH // -!cat1s !maps_cat.
Rewrite: !sieve_cat // -!maps_sieve -/g !sieve1 !maps_cat !maps_seqn.
Move: (sieve mr (drop (2) (cpring g))) (!sieve g mc (ctrenum cp)) => r1 r2.
Rewrite: !insertE_cat !insertE_seqb -!maps_comp -!catA !icpH_edge.
Pose r1' := (maps (comp (icpH g) edge) r1).
Pose r2' := (insertE (maps (icpH g) r2)).
Pose r0 := (seq1 (ecpH g)); Pose x1 := (icpH g (node g)); Pose x2 := (icpH g g).
Pose x5 := (icpH g (edge g)); Pose x4 := (icpH g (edge (node g))).
Step []: r1' = (maps (comp edge (icpH g)) r1) By Done.
Step []: r2' = (maps (icpH g) (insertE r2)).
  By Rewrite: ~/r2'; Elim: r2 => // *; Repeat Congr Adds.
Rewrite: /seq1 /maps !seq1I -/x1 -/x2; Simpl in b1 b2 b3 b4 b5.
Rewrite: {1 cat}lock catA -lock sparse_catCA -!catA.
Pose r := (cat r0 (cat (seqn b4 x4) (cat (seqn b5 x5) (cat r1' r2')))); Move=> HpH.
Step Hrec: (sparse (cat (seqn b1 x1) (cat (seqn b3 x1) (cat (seqn b4 x1)
                   (cat (seqn b2 x2) (cat (seqn b3 x2) (cat (seqn b5 x2) r))))))).
  Move: HpH; Rewrite: {sparse}lock; ClearBody r.
  Case: b3 b1 b2 b4 b5 Hb => [|] [|] [|] [|] [|] // _ /=.
   Rewrite: -lock -!cat1s (!sparse_catCA (ecpH g)) /seq1 /cat.
    By Rewrite: (!sparse_adds (ecpH g)); Case/andP.
   By Rewrite: -lock (!sparse_adds (ecpH g)); Case/andP.
   Rewrite: -lock -!cat1s (!sparse_catCA (ecpH g)) /seq1 /cat.
    By Rewrite: (!sparse_adds (ecpH g)); Case/andP.
   By Rewrite: -lock (!sparse_adds (ecpH g)); Case/andP.
  By Rewrite: -lock 2!(!sparse_adds (ecpH g)); Case/and3P.
Apply: etrans Hrec {HpH}; Apply: simple_perm.
  Move=> u; Rewrite: /r !(!fband_cat (permF (ecpH g))).
  Pose fb := (!fband (permF (ecpH g))); Case (fb r2' u); LeftBy Rewrite: !orbT.
  Case (fb r1' u); LeftBy Rewrite: !orbT.
  Case (fb r0 u); LeftBy Rewrite: !orbT.
  Case (fb (seqn b5 x5) u); LeftBy Rewrite: !orbT.
  Case (fb (seqn b4 x4) u); LeftBy Rewrite: !orbT.
  Case (fb (seqn b4 x1) u); LeftBy Rewrite: !orbT.
  Case (fb (seqn b5 x2) u); LeftBy Rewrite: !orbT.
  Rewrite: !orbF !orFb; Congr orb.
    Case b1; [Congr orb | Done].
    By Rewrite: 2!cface1r /= /long_cpring /=  Enode (negbE Hgp) /= set11.
  Rewrite: orbA orbC; Repeat Congr orb.
      By Case b3; LeftBy Congr orb; Rewrite: cface1r /= set11.
    By Case b2; LeftBy Congr orb; Rewrite: cface1r /= Enode (negbE Hgp) /=.
  By Case b3; LeftBy Congr orb; Rewrite: 2!cface1r /= Enode (negbE Hgp) /=.
By Rewrite: /r !size_cat !size_seqn; Repeat NatCongr.
Qed.

Fixpoint ctrband [cm : bitseq; cp : cprog] : cpmask :=
  Cases cp cm of
    (Adds (CpR n) cp') _ =>
    let (mr, mk) = (ctrband cm cp') in (Cpmask (rot n mr) mk)
  | (Adds CpY Seq0) _ =>
    (Cpmask (seqn (3) false) seq0)
  | (Adds CpY cp') (Adds b1 cm') =>
    if (ctrband cm' cp') is (Cpmask (Adds a0 (Adds a1 mr)) mk) then
      (Cpmask (cat (seq3 (orb b1 a0) false (orb b1 a1)) mr) mk)
    else (Cpmask seq0 seq0)
  | (Adds CpH cp') (Adds b1 (Adds b0 (Adds b2 cm'))) =>
    if (ctrband cm' cp') is (Cpmask (Adds a0 (Adds a1 (Adds a2 mr))) mk) then
      (Cpmask (cat (seq3 (orb b0 a0) b1 (orb b2 a2)) mr)
              (Adds (or4b b0 b1 b2 a1) mk))
    else (Cpmask seq0 seq0)
  | _ _ =>
   (Cpmask seq0 seq0)
  end.

Lemma ctrband_correct : (cm : bitseq; cp : cprog)
  (size cm) = (ctrmsize cp) -> (config_prog cp) ->
  (and (proper_cpmask cp (ctrband cm cp))
       (fband (insertE (sieve cm (ctrenum cp)))) =1
           (fband (cpsieve (ctrband cm cp) cp))).
Proof.
Move=> cm cp Ecm Hcp; Elim: cp Hcp cm Ecm=> // [s cp Hrec] Hcp.
Move: Hcp (config_prog_cubic Hcp) Hrec => /=.
Case: s => // [n||] Hcp Hcpq; Move: (cpmap_plain Hcpq) (cpmap_proper Hcpq);
  Rewrite: /cpmap -/cpmap; Pose g := (cpmap cp); Move=> HgE Hgp Hrec cm Ecm.
    Case: (ctrband cm cp) {Hrec Ecm Hcp}(Hrec Hcp ? Ecm) => [mr mk].
    Case; Move/andP=> [Emr Emc] Erec.
    Split; LeftBy Rewrite: /= size_rot Emr.
    Rewrite: /cpsieve /cpmap -/cpmap -/g cpring_ecpR /=.
    Move=> x; Rewrite: Erec -/g /= !fband_cat /=; Congr orb.
    By Rewrite: sieve_rot ?fband_rot // (eqP Emr) -size_ring_cpmap.
  Rewrite: /g; Case Dcp: cp cm Hcp Ecm => [|s cp'] // [|b1 cm] //.
  Rewrite: -Dcp -/g; Move=> Hcp Ecm; Simpl in Ecm; Injection: Ecm => Ecm.
  Case: (ctrband cm cp) {Hrec}(Hrec Hcp ? Ecm) => [mr mk].
  Case; Move/andP=> [Emr Emk].
  Step Hmr: (ltn (1) (size mr)).
    By Rewrite: (eqP Emr) -size_ring_cpmap -size_proper_cpring.
  Case: mr Hmr Emr => [|a0 [|a1 mr]] // _ Emr Erec.
  Split; LeftBy Rewrite: /= -(eqP Emr) /= set11.
  Step []: (maps (icpY g) (Adds (node g) (ctrenum cp))) = (ctrenum (Adds CpY cp)).
    By Rewrite: /= /g Dcp.
  Move=> u; Rewrite: /cpsieve /cpmap -/cpmap -/g.
  Rewrite: cpring_ecpY /behead (head_proper_cpring Hgp).
  Rewrite: /cpker -/cpker -maps_adds -!maps_sieve (insertE_icpY g) maps_adds.
  Rewrite: !sieve_adds insertE_cat insertE_seqb -!catA !fband_cat orFb /fband.
  Rewrite: !has_seqb -maps_sieve !has_maps -/g.
  Case: (fband_icpY u) => [[x Hx] | Hu].
    Step Eu: (comp (cface u) (icpY g)) =1 (cface x).
      By Move=> y; Rewrite: /comp (same_cface Hx) cface_icpY.
    Rewrite: !(eq_has Eu) !(same_cface Hx) cface_icpY !has_cat !has_seqb.
    Rewrite: orbCA cface1r Enode; Symmetry.
    Rewrite: Sface (same_cface (cface_node_ecpY g)) cface_icpY Sface.
    Rewrite: /fband in Erec; Rewrite: Erec /cpsieve -/g has_cat.
    Rewrite: {2 (cpring g)}(head_proper_cpring Hgp) !has_sieve_adds !orbA.
    By Do 2 Congr orb; Rewrite: !demorgan2 -!orbA; Repeat BoolCongr.
  Step Eu: (comp (cface u) (icpY g)) =1 set0.
    By Move=> y; Rewrite: /comp -(same_cface Hu) (cface_ecpY 2!g).
  By Rewrite: !(eq_has Eu) !has_set0 -!(same_cface Hu) !(cface_ecpY 2!g) !andbF.
Case: cm Ecm => [|b1 [|b0 [|b2 cm]]] // Ecm; Simpl in Ecm; Injection: Ecm => Ecm.
Case: (ctrband cm cp) {Hrec}(Hrec Hcp ? Ecm) => [mr mk].
Case; Move/andP=> [Emr Emk].
Step Hgl: (long_cpring g) By Apply: cfmap_long.
Step Hmr: (ltn (2) (size mr)).
  By Rewrite: (eqP Emr) -size_ring_cpmap -size_long_cpring.
Case: mr Hmr Emr => [|a0 [|a1 [| a2 mr]]] // _ Emr Erec; Simpl in Emr.
Split; LeftBy Rewrite: /= -(eqP Emr) /= set11.
Move=> u; Rewrite: /cpsieve /cpmap -/cpmap -/g.
Rewrite: cpring_ecpH // /drop /cpker -/cpker -/g (head_long_cpring Hgl).
Rewrite: sieve_adds -!maps_adds -!maps_sieve (!insertE_cat (ecpH g)).
Rewrite: (!insertE_seqb (ecpH g)) (insertE_icpH g).
Pose fX := (face (ecpH g)); Def: EfX := (erefl fX); Rewrite: {2}/fX /= in EfX.
Case EfX; Step []: (face (icpH g (edge (node g)))) = (edge fX).
  Rewrite: /= Enode (negbE Hgp) /=; Rewrite: /eqd /= set11 /eqd /=.
  By Rewrite: (inj_eqd (Iedge g)) eqd_sym (negbE Hgp).
Rewrite: !sieve_adds -!catA -maps_sieve -maps_cat /fband !has_cat !has_seqb.
Rewrite: /fX -!cface1r !has_maps; Symmetry; Rewrite orbCA; Congr orb.
Rewrite: Sface (same_cface (cface_node_ecpH Hgp)) Sface.
Case: (fband_icpH u) => [[x Hx] | Hu].
  Step Eu: (comp (cface u) (icpH g)) =1 (cface x).
    By Move=> y; Rewrite: /comp (same_cface Hx) cface_icpH.
  Rewrite: !(same_cface Hx) !cface_icpH !(eq_has Eu); Rewrite: /fband in Erec.
  Rewrite: !insertE_cat !insertE_seqb !has_cat !has_seqb Erec.
  Rewrite: /cpsieve -/g {2 (cpring g)}(head_long_cpring Hgl) has_cat.
  Rewrite: !has_sieve_adds -cface1r (cface1r (edge (node g))) Enode.
  By Rewrite: !demorgan2 -!orbA; Repeat BoolCongr.
Step Eu: (comp (cface u) (icpH g)) =1 set0.
  By Move=> y; Rewrite: /comp -(same_cface Hu) cface_ecpH.
By Rewrite: !(eq_has Eu) !has_set0; Rewrite: /comp in Eu; Rewrite: !Eu !andbF.
Qed.

Definition cfcontract_mask [cf : config] : bitseq :=
  (ctrmask (cfprog cf) (cfcontract_ref cf)).

Definition cfcontract [cf : config] : (seq (cfmap cf)) :=
  (sieve (cfcontract_mask cf) (ctrenum (cfprog cf))).

Fixpoint cptriad [ccm : cpmask; cp : cprog; i : nat] : bool :=
  if i is (S i') then
    let (mrt, mkt) = (cpadj (cpmask1 cp i') cp) in
    let (mrc, mkc) = ccm in
    let mct = (cat (sieve mrc mrt) (sieve mkc mkt)) in
    if (andb (has negb mct) (ltn (2) (count id mct))) then true else
    (cptriad ccm cp i')
  else false.
  
Definition valid_ctrm [cm : bitseq; cp : cprog] : bool :=
  let n = (count id cm) in
  if n =d (4) then (cptriad (ctrband cm cp) cp (cpksize cp)) else
  (set3 (1) (2) (3) n).

Definition contract_ctree [cf : config] : (option ctree) :=
  let cp = (cfprog cf) in let cm = (cfcontract_mask cf) in
  if (cfctr (seqn (cprsize cp) false) cm cp) is (Some cpc) then
    if (valid_ctrm cm cp) then (Some ctree (cpcolor cpc)) else (None ctree)
  else (None ctree).

Lemma contract_ctreeP : (cf : config)
  if (contract_ctree cf) is (Some ct) then
    let r = (cfring cf) in let cc = (cfcontract cf) in
       (valid_contract r cc)
    /\ (et : colseq) (cc_ring_trace cc (rev r) et) ->
                      (ctree_mem ct (etrace (behead et)))
  else True.
Proof.
Move=> [sym ccr cp]; Rewrite: /contract_ctree /cfcontract /cfcontract_mask /=.
Rewrite: /cfring rev_rev /cfmap ~{sym}/= -size_ring_cpmap.
Pose g := (cpmap cp); Pose r := (cpring g).
Pose cm := (ctrmask cp ccr); Pose mr0 := (seqn (size r) false).
Step Emr0: (size mr0) = (cprsize cp) By Rewrite: -size_ring_cpmap /mr0 size_seqn.
Step Ecm: (size cm) = (ctrmsize cp) By Apply: size_ctrmask.
Move: (sparse_cfctr Emr0 Ecm) (cfctr_correct Emr0 Ecm).
Case: (cfctr mr0 cm cp) (cfctr_config_prog mr0 cm cp) => //= [cpc] Hcp.
Def: HgE := (cpmap_plain (config_prog_cubic Hcp)).
Rewrite: -/g -/r; Pose cc := (sieve cm (ctrenum cp)); Move=> UccN Hcc.
Case Hcm: (valid_ctrm cm cp); RightDone.
Rewrite: /mr0 sieve_false /= in UccN; Split.
  Move: Hcm; Rewrite: /valid_ctrm eqd_sym.
  Step []: (size cc) = (count id cm).
    Apply: eqP; Move: (introT eqP Ecm); Rewrite: -size_ctrenum /cc.
    Elim: {}cm (ctrenum cp) => [|[|] m Hrec] [|x p] //; Apply: Hrec.
  Move=> Hcm; Split; Try By Case/andP: UccN.
      Move: (uniq_ctrenum Hcp); Rewrite: -/g -/r insertE_cat uniq_cat disjoint_has.
      Move/and3P=> [_ Ur _]; Apply/hasP=> [[x Hxc Hxr]]; Case/hasP: Ur.
      Exists x; Rewrite: !mem_insertE // in Hxr *; Apply/hasP.
        By Case/hasP: Hxr => [y Hy Hxy]; Exists y; LeftBy Exact (mem_sieve Hy).
      By Exists x; [Rewrite: -mem_rev | Apply: connect0].
    By Rewrite: /set4; Case: ((4) =d (size cc)) Hcm; Rewrite: ?orbT ?orbF.
  Move=> Dcc; Move: Hcm; Rewrite: Dcc /=.
  Move=> H; Apply/set0P=> [Hccr]; Case/negPf: H; Move: Hccr.
  Elim: {-2}(cpksize cp) (leqnn (cpksize cp)) => //= [i Hrec] Hi.
  Move: (cpsieve1 Hi Hcp) (proper_cpmask1 cp i).
  Pose x := (sub (cpmap cp) (cpker cp) i).
  Move: (cpmask1 cp i) => cmx Hx Hcmx.
  Case: (cpadj cmx cp) (cpadj_proper Hcmx) (cpsieve_adj Hcp Hcmx) => [mrt mkt].
  Case: {-4}(ctrband cm cp) (ctrband_correct Ecm Hcp) => [mrc mkc].
  Rewrite: -/cc /= -/g -/r; Case; Move/andP=> [Emrc Emkc] Hmc.
  Move/andP=> [Emrt Emkt] Hmt Hccr.
  Apply: cases_of_if; RightBy Clear; Apply: Hrec => //; Apply ltnW.
  Move/andP=> [Hmtc Hmtc']; Rewrite: -size_ring_cpmap -/g -/r in Emrc Emrt.
  Pose mt := (cat mrt mkt); Pose mc := (cat mrc mkc); Pose q :=(cat r (cpker cp)).
  Step Emtq: ((size mt) =d (size q)).
    By Rewrite: /mt /q !size_cat (eqP Emrt) (eqP Emkt) (size_cpker Hcp) set11.
  Step Emcq: ((size mc) =d (size q)).
    By Rewrite: /mc /q !size_cat (eqP Emrc) (eqP Emkc) (size_cpker Hcp) set11.
  Step Uq: (simple q) By Apply: cpmap_simple.
  Rewrite: -sieve_cat -/mt -/q ?(eqP Emrt) // ~Hx in Hmt.
  Rewrite: -sieve_cat -/mc -/q ?(eqP Emrc) // in Hmc.
  Rewrite: -sieve_cat -/mt -/mc ?(eqP Emrt) ?(eqP Emrc) // in Hmtc Hmtc'.
  Case/andP: {Hccr}(Hccr x) {Hrec}; Split.
    Apply/hasP=> [[y Hy Hyx]].
    Rewrite: /q simple_cat in Uq; Case/and3P: Uq; Clear; Case/hasP; Exists x.
      By Apply: mem_sub; Rewrite: (size_cpker Hcp).
    By Apply/hasP; Exists y; LeftBy Rewrite: -mem_rev.
  Apply/andP; Split.
    Apply: (leq_trans Hmtc') {Hmtc'}.
    Apply: (!leq_trans (fcard face (setI (adj x) (fband (insertE cc))))).
      Rewrite: leq_eqVlt; Apply/orP; Left; Apply/eqP.
      Transitivity (fcard face (fband (filter (fband (sieve mt q)) (sieve mc q)))).
        Rewrite: simple_fcard_fband.
          Move: {}mc {}mt Emcq Emtq Uq; Rewrite: simple_recI.
          Elim: {}q => [|y q' Hrec] [|b m] // [|b' m'] //= Emq Em'q.
          Move/andP=> [Hy Uq'];  Pose q1 := (sieve m q'); Pose q2 := (sieve m' q').
          Step Hy': (m'' : bitseq) (fband (sieve m'' q') y) = false.
            Move=> m''; Apply/hasP=> [[z Hz Hyz]]; Case/hasP: Hy.
            By Exists z; LeftBy Exact (mem_sieve Hz).
          Step Ebq': (filter (fband (Adds y q2)) q1) = (filter (fband q2) q1).
            Move/idPn: (Hy' m); Rewrite: -/q1.
            Elim: q1 {Hrec} => [|z q1 Hrec] //=; Move/norP=> [Hz Hq1].
            By Rewrite: Sface (negbE Hz) Hrec.
          By Case: b; Rewrite: /= Hrec //; Case: b' => //=;
            Rewrite: ?connect0 ?Ebq' // /q2 Hy'.
        Step Uq1: (simple (sieve mc q)).
          Move: Uq; Elim: {}mc {}q => [|[|] m Hrec] [|y q'] //=;
            Rewrite: !simple_adds; Move/andP=> [Hy Uq']; Auto.
          Rewrite: Hrec // andbT; Apply/hasP=> [[z Hz Hyz]].
          By Case/hasP: Hy; Exists z; LeftBy Exact (mem_sieve Hz).
        Elim: (sieve mc q) Uq1 => [|y q1 Hrec] //=.
        Rewrite: !simple_adds; Move/andP=> [Hy Uq'].
        Case: (fband (sieve mt q) y); Auto.
        Rewrite: simple_adds Hrec // andbT; Apply/hasP=> [[z Hz Hyz]].
        By Rewrite: mem_filter in Hz; Case/hasP: Hy; Case/andP: Hz; Exists z.
      Apply: eq_n_comp_r => [y]; Apply/idP/idP.
        Move/hasP=> [z Hz Hyz]; Rewrite: mem_filter in Hz; Case/andP: Hz.
        Rewrite: Hmt /= orbF -(adjF Hyz) Sadj //; Move=> Hxy Hccz.
        By Rewrite: /setI Hxy Hmc; Apply/hasP; Exists z.
      Move/andP=> [Hxy Hccy]; Rewrite: Hmc in Hccy.
      Case/hasP: Hccy => [z Hz Hyz]; Apply/hasP; Exists z; Auto.
      By Rewrite: mem_filter /setI Hz andbT Hmt /= orbF -(adjF Hyz) Sadj.
    Rewrite: count_filter -(size_maps [y : g](froot face (edge y))).
    Apply: (leq_trans ? (card_size ?)); Apply: subset_leq_card.
    Apply/subsetP=> [y]; Move/and3P=> [Dy Hxy Hyc].
    Case/adjP: Hxy => [z Hxz Hzy].
    Rewrite: -(eqP Dy) -(rootP (Sface g) Hzy); Apply: maps_f.
    Rewrite: mem_filter /setI -fconnect_orbit Hxz.
    By Rewrite: (closed_connect (fbandF (insertE cc)) Hzy) Hyc.
  Apply/subsetP=> [Hccx].
  Step Hct: (sub_set (fband (sieve mc q)) (fband (sieve mt q))).
    Move=> y Hy; Rewrite: -Hmc in Hy; Case/hasP: Hy => [z Hz Hyz].
    Rewrite: (closed_connect (fbandF (sieve mt q)) Hyz) Hmt /= orbF Sadj //; Auto.
  Move: {}mc {}mt Emcq Emtq Uq Hct Hmtc; Rewrite: simple_recI.
  Elim: {}q => [|y q' Hrec] [|b m] // [|b' m'] //= Emq Em'q.
  Move/andP=> [Hy Uq'].
  Step Hy': (m'' : bitseq) (fband (sieve m'' q') y) = false.
    Move=> m''; Apply/hasP=> [[z Hz Hyz]]; Case/hasP: Hy.
    By Exists z; LeftBy Exact (mem_sieve Hz).
  Case: b; Case: b'; Move=> Hct; Try Apply: (Hrec m m'); Auto.
      Move=> z Hz; Move: (Hct z) => /=.
      Case Hzy: (cface z y) => /=; Auto.
      By Rewrite: (closed_connect (fbandF (sieve m q')) Hzy) Hy' in Hz.
    By Move: (Hct y); Rewrite: /= connect0 !Hy'; Move=> H; Move: (H (erefl ?)).
  Move=> z Hz; Move: (Hct z) => /=.
  Case Hzy: (cface z y) => /=; Auto.
  By Rewrite: (closed_connect (fbandF (sieve m q')) Hzy) Hy' in Hz.
Move=> et [k Hk Det]; Rewrite: ~{et}Det.
Rewrite: {1}/mr0 sieve_false in Hcc; Case: {Hk Hcc}(Hcc ? Hk).
Step []: r = (sieve (maps negb mr0) r).
  By Rewrite: /mr0; Elim: {}r => [|x r' Hrec] //=; Congr Adds.
Move: k => k' k Hk [] {k'}; Apply/(ctree_mem_cpcolor ? ?).
Split; LeftBy Apply even_etrace.
Pose et := (trace (maps k (cpring (cpmap cpc)))).
Rewrite: /etrace; Pose h := (etrace_perm (behead et)).
Exists (comp h k); LeftBy Apply: coloring_inj => //; Apply permc_inj.
Rewrite: sumt_permt (maps_comp h k) -/(permt h) trace_permt -/et.
Rewrite: /permt -maps_adds; Congr (maps h).
Step Het: (sumt et) = Color0 By Apply: sumt_trace.
Case Det: et (introT eqP Het) {h} => [|e et'] /=.
  By Move: (congr size Det); Rewrite: /et size_trace size_maps head_cpring.
By Rewrite: -eq_addc0; Case/eqcP.
Qed.

End ConfigContract.

Unset Implicit Arguments.

    
