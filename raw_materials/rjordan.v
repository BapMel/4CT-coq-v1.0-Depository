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
Require jordan.
Require geometry.

(* A somewhat more standard, but more complex and slightly weaker version  *)
(* of the Jordan property, based on simple rings rather than contours. For *)
(* completeness mainly, we show that it is equivalent to the definition we *)
(* use in the four color theorem proof.                                    *)

Set Implicit Arguments.

Section RingJordan.

Variable g : hypermap.

(* Darts x in the band of a ring r, such that (edge x) lies inside r. This *)
(* excludes border darts!                                                  *)
Definition inner_dart [r : (seq g); x : g] : bool :=
  let rx = (fproj r x) in let rx' = (face (edge (prev r rx))) in
  (andb (fband r x) (ltn (findex face rx' x) (findex face rx x))).

(* Darts x in the band of a ring r, such that (node x) lies outside r.     *)
(* Again, this excludes the border. Note that the definition is not quite  *)
(* dual to inner_dart; this is because we have the ring chord start from   *)
(* an inner dart and end at an outer dart.                                 *)
Definition outer_dart [r : (seq g); x : g] : bool :=
  let rx = (fproj r x) in let rx' = (face (edge (prev r rx))) in
  (andb (fband r x) (ltn (findex face rx' rx) (findex face rx' x))).

(* Intuitively, this says that r is a simple ring, and p is a simple chord *)
(* that links an inner dart x to an outer dart of r without crossing any   *)
(* of the faces of r.                                                      *)

Definition moebius_ring [r : (seq g); x : g; p : (seq g)] : bool :=
  (and5b (cycle rlink r) (path rlink x p)
         (inner_dart r x) (outer_dart r (face (edge (last x p))))
         (simple (cat r p))).

Definition ring_jordan : Prop :=
  (r : (seq g); x : g; p : (seq g)) (moebius_ring r x p) = false.

(* We first reduce the complex ring-based definition above to a simpler    *)
(* the contour-based definition, closely related to the basic definition.  *)

Definition preborderb [x : g ; p : (seq g)] : bool :=
  if p is (Adds y _) then x =d (node y) else true.

Definition borderb [x : g ; p : (seq g)] : bool :=
  if p is (Adds y _) then (negb (face x) =d y) else true.

Fixpoint border [c : (seq g)] : (seq g) :=
  if c is (Adds x c') then
    if (borderb x c') then (Adds x (border c')) else (border c')
  else seq0.

Definition simple_moebius [c : (seq g)] : bool :=
  (andb (moebius c) (simple (border c))).

Lemma last_border : (x : g; c : (seq g)) (last x (border c)) = (last x c).
Proof.
Move=> x c; Elim: c x => //= [y c []] x.
Case Hy: (borderb y c) => //; Elim: c x y Hy => //= [z c Hrec] x y _.
By Case Hz: (borderb z c) => //; Rewrite: (Hrec x z Hz) (Hrec y z Hz).
Qed.

Lemma fband_border : (c : (seq g)) (fband (border c)) =1 (fband c).
Proof.
Move=> c x; Elim: c => //= [y c H]; Case Hy: (borderb y c); Rewrite: /= ~H //.
By Case: c Hy => //= [z c]; Case/eqP; Rewrite: -!cface1r orbA orbb.
Qed.

Lemma path_border : (x : g; c : (seq g)) (path clink x c) ->
  (path rlink if (preborderb x c) then x else (node x) (border c)).
Proof.
Move=> x c; Elim: c x => [|y c Hrec] x //=.
Move/andP => [Hxy Hc]; Move: {Hrec}(Hrec ? Hc) => Hp.
Step Hxey: (rlink if (x =d (node y)) then x else (node x) y).
  Case: (x =P (node y)) => [Dx | Hny].
    By Rewrite: /rlink cface1 Dx Enode connect0.
  Case/clinkP: Hxy => [Dx | Dfx]; LeftBy Case Hny.
  By Rewrite: /rlink 2!cface1 Enode Dfx connect0.
Case Hy: (borderb y c) => /=.
  Rewrite: Hxey; Case Hy': (preborderb y c) Hp => //.
  Case: c Hc Hy Hy' {Hxy EpF} => //= [z c].
  By Case/andP; Case/clinkP=> [[]]; Rewrite set11.
Case: c (border c) Hy Hp {Hc EpF} => [|z c] [|t p] //=; Move/eqP=> Dfy.
Move/andP=> [Ht Hp]; Rewrite: ~Hp andbT; Apply: (connect_trans Hxey).
Apply: (connect_trans ? Ht) {Ht}.
Case: (y =P (node z)) => [Dy | _]; RightBy Rewrite: cface1r Enode connect0.
By Rewrite: {2 y}Dy -Dfy Eface connect0.
Qed.

Fixpoint contour [x : g; p : (seq g)] : (seq g) :=
  if p is (Adds y p') then
    (cat (traject face (face (edge x)) (S (findex face (face (edge x)) y)))
         (contour y p'))
  else seq0.

Lemma contourP : (x : g; p : (seq g))
  (path rlink x p) -> (simple p) ->
  let c = (contour x p) in
  (and4 (preborderb x c) (path clink x c) (uniq c) (border c) = p).
Proof.
Move=> x p; Elim: p x => [|y p Hrec] x //=.
Rewrite: simple_adds; Move/andP=> [Hxy Hp]; Move/andP=> [Upy Up].
Move: {Hrec Hp Up}(contour y p) (Hrec ? Hp Up) => c [Hy Hc Uc Dp]; Split.
 By Rewrite: Eedge set11.
 Rewrite: -{1 x}Eedge clinkN path_cat last_traject iter_findex -?cface1 //.
  Rewrite: Hc andbT; Apply: (sub_path (!sub_relUr ? ? ?)); Apply fpath_traject.
 Rewrite: -uniq_adds -cat_adds uniq_cat Uc andbT; Apply/andP; Split.
    Apply: (etrans (looping_uniq ? ? ?)); Rewrite: /looping.
    Rewrite: iter_findex -?cface1 //; Apply/trajectP => [[i Hi Dy]]; Move: {}Hi.
    Rewrite: -Dy findex_iter ?ltnn //.
    By Apply: (leq_trans Hi); Apply ltnW; Apply findex_max; Rewrite: -cface1.
  Apply/hasP=> [[z Hz Hyz]]; Rewrite: -Dp fband_border in Upy.
  Case/hasP: Upy; Exists z; Auto.
  Case/(trajectPx face ? (S ?) ?): Hyz => [i _ []].
  By Rewrite: -(same_cface Hxy) iter_f fconnect_iter.
Pose z := (face (edge x)); Rewrite: /rlink cface1 -/z in Hxy.
Move: (findex face z y) {Hxy}(iter_findex Hxy) => i; Elim: i z => [|i Hrec] z /=.
  Move=> Dz; Rewrite: Dz Dp; Case Hy': (borderb y c) => //.
  Case/idP: Upy; Rewrite: -Dp fband_border.
  By Case: c Hy' {Hy Hc Uc Dp} => //= [t c]; Case/eqP; Rewrite fconnect1.
Rewrite: f_iter -iter_f set11 /=; Apply: Hrec. 
Qed.

Lemma contour_cat : (x : g; p1, p2 : (seq g))
  (contour x (cat p1 p2)) = (cat (contour x p1) (contour (last x p1) p2)).
Proof.
By Move=> x p1 p2; Elim: p1 x => //= [y p1 Hrec] x; Rewrite: -catA -Hrec.
Qed.

Lemma contour_border : (x : g; c : (seq g))
  (preborderb x c) -> (path clink x c) -> (uniq c) -> (contour x (border c)) = c.
Proof.
Move=> nx [|x c] //; Rewrite: {4 Adds}lock /=.
Move/eqP=> Dnx; Case/andP=> [_]; Rewrite: ~{nx}Dnx.
Elim: c x => [|y c Hrec] x /=; LeftBy Unlock; Rewrite: /= Enode findex0.
Move/andP=> [Hxy Hc]; Move/andP=> [Ux Uc]; Rewrite: -lock {2 Adds}lock /=.
Move: {Hrec Hc Uc}(Hrec ? Hc Uc); Unlock; Case Db: (border (Adds y c)) => [|z p].
  By Move: (fband_border (Adds y c) y); Rewrite: Db /= connect0.
Simpl; Case: ((face x) =P y) => [Dfx | Hfx] /=; Rewrite: !Enode.
  Step [Hyz Hcz]: (cface y z) /\ (Adds y c z).
    Rewrite: -{1 2 z}(congr (head x) Db) ~{z Db Hxy Ux Dfx}.
    Apply: andP; Elim: c y => [|z c Hrec] y /=; LeftBy Rewrite: connect0 setU11.
    Case: ((face y) =P z) (Hrec z) => [[]|_] /=; RightBy Rewrite: connect0 setU11.
    By Case/andP=> [Hyz Hcz]; Rewrite: cface1 Hyz setU1r.
  Step []: (S (findex face y z)) = (findex face x z); RightBy Rewrite Dfx; Case.
  Rewrite: -{2 z}(iter_findex Hyz) -{3 y}Dfx iter_f findex_iter //.
  Rewrite: ltn_neqAle -arity_face Dfx (findex_max Hyz) andbT.
  Apply/eqP=> [H]; Move: {H}(congr [n](iter n face y) H).
  Rewrite: iter_face_arity /= (iter_findex Hyz) -Dfx.
  By Move=> H; Rewrite: -(Iface ? H) -mem_adds Hcz in Ux.
By Case/clinkP: Hxy => [Dx | Dy]; [ Case; Rewrite: findex0 Dx Enode | Case Hfx].
Qed.

Lemma border_cat : (x : g; c1, c2 : (seq g))
  let b' = [b]if (borderb (last x c1) c2) then b else (behead (belast x b)) in
  (border (cat c1 c2)) = (cat (b' (border c1)) (border c2)).
Proof.
Move=> x c1 c2; Elim: c1 x =>  [|y c1 Hrec] x /=; LeftBy Rewrite if_same.
Rewrite: ~{Hrec}(Hrec y); Case: c1 => [|z c1] //=.
  By Rewrite: !if_same; Case: (borderb y c2).
Case: ((face y) =d z) (borderb (last z c1) c2) => [|] [|] //=;
  Case Hz: (borderb z c1) => //=; Case Dbc1: (border c1) => //=.
Move: (fband_border c1 (head z c1)); Rewrite: ~Dbc1 /=.
By Case: c1 Hz => //= [t c1] _; Rewrite connect0.
Qed.

Section TrajectArith.

Variables d : dataSet; f : d -> d.
Hypothesis Hf : (injective f).

Lemma trajectS : (x : d; n : nat)
 (Adds x (traject f (f x) n)) = (traject f x (S n)).
Proof. Done. Qed.

Lemma traject_addn : (x : d; n1, n2 : nat)
  (traject f x (addn n1 n2)) = (cat (traject f x n1) (traject f (iter n1 f x) n2)).
Proof.
By Move=> x n1 n2; Elim: n1 x => //= [n1 Hrec] x; Rewrite: Hrec iter_f.
Qed.

End TrajectArith.

Section FindexArith.

Variables d : finSet; f : d -> d.
Hypothesis Hf : (injective f).

Lemma same_order : (x, y : d) (fconnect f x y) -> (order f x) = (order f y).
Proof. By Move=> *; Apply: eq_card; Apply: (same_connect (fconnect_sym Hf)). Qed.

Lemma findex_sym : (x, y : d) (fconnect f x y) -> (negb x =d y) ->
  (addn (findex f x y) (findex f y x)) = (order f x).
Proof.
Move=> x y Hxy Dxy; Pose n := (order f x); Pose i := (findex f x y).
Step Hi: (leq i n) By Apply ltnW; Apply: findex_max.
Rewrite: -(iter_order Hf x) -/n -(leq_add_sub Hi); Congr addn.
Rewrite: addnC /addn iter_plus {2}/i iter_findex // findex_iter //.
Case Di: i => [|i']; LeftBy Case/eqP: Dxy; Rewrite: -(iter_findex Hxy) -/i Di.
By Rewrite: Di in Hi; Rewrite: -(leq_subS Hi) subSS /n (same_order Hxy) leq_subr.
Qed.

Lemma leq_findex_connect : (x, y, z : d)
  (fconnect f x z) -> (leq (findex f x y) (findex f x z)) -> (fconnect f x y).
Proof.
Move=> x y z Hxz Hxyz; Move: Hxz.
By Rewrite: !fconnect_orbit -!index_mem; Apply: leq_trans.
Qed.

Lemma add_findex_leql : (x, y, z : d)
  (fconnect f x z) -> (leq (findex f x y) (findex f x z)) ->
  (addn (findex f x y) (findex f y z)) = (findex f x z).
Proof.
Move=> x y z Hxz Hxyz; Def: Hxy := (leq_findex_connect Hxz Hxyz).
Rewrite: -{1 z}(iter_findex Hxz) -(leq_add_sub Hxyz); Congr addn.
Rewrite: addnC /addn iter_plus iter_findex // findex_iter // -(same_order Hxy).
By Apply: leq_trans (findex_max Hxz); Rewrite: ltnS leq_subr.
Qed.

Lemma add_findex_leqr : (x, y, z : d)
  (fconnect f x y) -> (fconnect f x z) -> (leq (findex f y z) (findex f x z)) ->
  (addn (findex f x y) (findex f y z)) = (findex f x z).
Proof.
Move=> x y z Hxy Hxz Hxyz; Def: Exz := (leq_add_sub (ltnW (findex_max Hxz))).
Rewrite: -{1 y}(iter_order Hf) -(same_order Hxy) -Exz.
Rewrite: -{1 3 (findex f x z)}(leq_add_sub Hxyz) addnC; Congr addn.
Rewrite: -addnA addnC {1}/addn iter_plus iter_findex.
  Rewrite: -{4 z}(iter_findex Hxz) -iter_plus addnI -addnA {1}/addn iter_plus.
  Rewrite: addnC Exz (iter_order Hf) findex_iter //.
  By Apply: leq_trans (findex_max Hxz); Rewrite: ltnS leq_subr.
By Apply: (connect_trans ? Hxz); Rewrite fconnect_sym.
Qed.

End FindexArith.

Lemma ring_moebius_simple : (r : (seq g); x : g; p : (seq g))
  (moebius_ring r x p) -> {c : (seq g) | (simple_moebius c)}.
Proof.
Move=> r x p; Case/and5P; Pose y := (face (edge (last x p))).
Move=> Hr Hp Hx Hy UrpF.
Case/andP: Hx; Case/fprojP; Move: (fproj r x) => rx Hrx Hxrx.
Pose rx' := (face (edge (prev r rx))); Move=> Hrx'.
Case/andP: Hy; Case/fprojP; Move: (fproj r y) => ry Hry Hyry.
Pose ry' := (face (edge (prev r ry))); Move=> Hry'.
Case/rot_to: {}Hry {}Hr => [i r' Dr].
Rewrite: -(cycle_rot i) Dr (cycle_path x) /=; Move/andP=> [Er' Hr'].
Step Upr'F: (simple (cat p (Adds ry r'))).
  Apply: etrans UrpF; Rewrite: -Dr; Apply: simple_perm.
    By Move=> z; Rewrite: !fband_cat fband_rot orbC.
  By Rewrite: !size_cat size_rot addnC.
Step Hpr': (path rlink x (cat p (Adds ry r'))).
  By Rewrite: path_cat Hp /= -(rlinkFr Hyry) /y {1}/rlink fconnect1.
Case: (contourP Hpr' Upr'F); Pose c := (contour x (cat p (Adds ry r'))).
Move=> Hxc Hc Uc Ecp; Exists c; Rewrite: /simple_moebius Ecp Upr'F andbT.
Rewrite: /moebius Uc /=; Case Dc: c Hxc Hc => [|x0 c'].
  By Move: (congr size Ecp); Rewrite: Dc size_cat /= addnS.
Simpl; Case/eqP; Move/andP=> [_ Hc']; Rewrite: Hc' andbT.
Move: (last_border x c); Rewrite: Ecp Dc last_cat /=; Case.
Step Ur: (uniq r) By Move: (simple_uniq UrpF); Rewrite: uniq_cat; Case/and3P.
Def: Urn := (cycle_prev Ur).
Rewrite: -(cycle_rot i) Dr (cycle_path x) /= in Urn.
Case/andP: Urn; Move/eqP=> Dry' _.
Rewrite: (finv_eq_monic (Enode g)) Dry' -/ry'.
Rewrite: /rlink cface1 Dry' -/ry' in Er'.
Move: Dc; Rewrite: /c contour_cat /= -/y -cat_add_last headI /=; Injection=> [] _.
Rewrite: mem2_cat -orbA orbCA; Apply/orP; Left.
Step Eyry': (negb ry' =d y) By Apply/eqP=> [Dy]; Rewrite: Dy findex0 in Hry'.
Step Hiyry': (ltn (0) (findex face y ry')).
  By Rewrite: /findex /orbit -orderSpred /= (negbE Eyry').
Step Hyry': (cface ry' y) By Rewrite: (same_cface Er') Sface.
Step Eyry: (negb y =d ry) By Apply/eqP=> [Dy]; Rewrite: Dy ltnn in Hry'.
Step Hiyry: (leq (findex face y ry') (findex face y ry)).
  Rewrite: -(leq_add2l (findex face ry' y)).
  Rewrite: (findex_sym (Iface g) Hyry' Eyry') (arity_cface Hyry').
  Rewrite: -(findex_sym (Iface g) Hyry Eyry) addnC leq_add2r.
  By Rewrite: -(add_findex_leql (Iface g) Hyry' (ltnW Hry')) leq_addl.
Rewrite: -(add_findex_leql (Iface g) Hyry Hiyry).
Step Hi1y: (ltn (1) (arity y)).
  Rewrite: -(arity_cface Hyry'); Apply: leq_trans (findex_max Hyry').
  By Rewrite ltnS; Apply: leq_trans Hry'.
Rewrite: -(findex_iter Hi1y) in Hiyry'; Rewrite: Sface in Hyry'.
Rewrite: -(add_findex_leql (Iface g) Hyry' Hiyry') findex_iter //.
Rewrite: add1n addSnnS /= traject_addn iter_findex -?cface1 //.
Rewrite: -catA mem2_cat -orbA orbCA; Apply/orP; Left.
Rewrite: /= mem2_adds set11; Change ((contour (prev r ry) (Adds ry r') x) :: Prop).
Rewrite: -Dr; Rewrite: -(mem_rot i) in Hrx.
Case/splitPr Dri: (rot i r) / Hrx => [r1 r2].
Rewrite: contour_cat /contour mem_cat /setU mem_cat /setU orbCA; Apply/orP; Left.
Move: (cycle_prev Ur); Rewrite: -(cycle_rot i) (cycle_path ry) Dri path_cat -Dri.
Rewrite: Dr {S}lock /= Dry'; Case/and3P=> [_]; Move/eqP=> Drx' _.
Rewrite: Drx' -/rx' -lock.
Step Hrxx': (cface rx rx').
  Move: Hr; Rewrite: -(cycle_rot i) Dri (cycle_path x) path_cat -Dri Dr /=.
  By Rewrite: Dry' Drx' /rlink cface1 Sface; Case/and3P.
Rewrite: Sface (same_cface Hrxx') in Hxrx; Def: Dx := (iter_findex Hxrx).
Apply/trajectP; Exists (findex face rx' x); Auto.
Step Erxx': (negb rx =d rx') By Apply/eqP=> [H]; Rewrite: H ltnn in Hrx'.
Rewrite: ltnS -(leq_add2l (findex face rx rx')) (findex_sym (Iface g) Hrxx' Erxx').
Rewrite: -(same_cface Hrxx') in Hxrx.
By Rewrite: (add_findex_leqr (Iface g)) //; Apply: ltnW => //; Apply findex_max.
Qed.

Lemma simple_moebius_ring : (c : (seq g)) (simple_moebius c) ->
  {r : (seq g) & {x : g & {p : (seq g) | (moebius_ring r x p)}}}.
Proof.
Move=> c; Case Dc: c => // [fex c']; Case/andP; Case/and3P; Rewrite: -Dc.
Pose ry' := (finv node (last fex c')); Pose x := (node fex).
Step Dry': ry' = (face (edge (last x c))).
  By Rewrite: Dc -(finv_eq_monic (Enode g)).
Move: ry' Dry' => ry' Dry' Hx Uc Hc' UcF.
Step Hc: (path clink x c) By Rewrite: Dc /x /= clinkN.
Step Hxc: (preborderb x c) By Rewrite: Dc /x /= set11.
Def: Ec := (contour_border Hxc Hc Uc).
Step Hcry': (c ry') By Rewrite Dc; Apply: setU1r; Exact (mem2l Hx).
Step Hcry'F: (fband (border c) ry').
  By Rewrite: fband_border; Apply: (subsetP (ring_fband c)).
Case/fprojP: {}Hcry'F; Move: (fproj (border c) ry') => ry Hry Hry'ry.
Case/splitPr Dpr: (border c) / Hry => [p r']; Pose r := (Adds ry r').
Def: Hpr := (path_border Hc); Rewrite: Hxc Dpr path_cat /= in Hpr.
Case/and3P: Hpr => [Hp Ep Hr'].
Def: Er' := (last_border x c); Rewrite: Dpr /= last_cat /= in Er'.
Exists r; Exists x; Exists p.
Move: Ec; Rewrite: Dpr contour_cat /= -cat_adds trajectS.
Pose y := (face (edge (last x p))); Pose n := (S (findex face y ry)).
Pose q := (traject face y n); Move=> Ec.
Step Hyry: (cface y ry) By Rewrite: /y -cface1.
Step Hr : (path rlink (last ry r') r).
  By Rewrite: /r /= Er' {1}/rlink cface1 -Dry' Hry'ry.
Step [Ur Ebcr] : (simple r) /\ (border (contour (last ry r') r)) = r.
  Rewrite: Dpr simple_cat in UcF; Case/and3P: UcF => [_ _ Ur].
  By Split; RightBy Case: (contourP Hr Ur).
Step Hqry' : (q ry').
  Rewrite: Dpr simple_cat simple_adds in UcF; Case/and4P: UcF.
  Move=> Up; Move/norP=> [Hpry _] Hr'ry Ur'.
  Rewrite: -Ec mem_cat /setU mem_cat in Hcry'.
  Case/or3P: Hcry'; Auto; Move/(subsetP (ring_fband ?) ?); Rewrite: -fband_border.
    Case: (contourP Hp Up) => [_ _ _ Dp].
    By Rewrite: Dp (closed_connect (fbandF p) Hry'ry) (negbE Hpry).
  Case: (contourP Hr' Ur') => [_ _ _ Dr'].
  By Rewrite: Dr' (closed_connect (fbandF r') Hry'ry) (negbE Hr'ry).
Rewrite: /q in Hqry'; Case/trajectP: Hqry'=> [i Hi Ery'].
Pose q1 := (traject face y i).
Step Hiy: (ltn i (arity y)) By Apply: (leq_trans Hi); Apply: findex_max.
Step Dn : n = (addn i (S (findex face ry' ry))).
  Rewrite: addnS -(findex_iter Hiy) Ery'; Congr S.
  By Rewrite: (add_findex_leql (Iface g)) // -Ery' findex_iter.
Rewrite: ~/q ~Dn traject_addn -/q1 Ery' !catA -catA in Ec.
Case Hpq1ry': (cat (contour x p) q1 ry').
  By Rewrite: -Ec uniq_cat /= Hpq1ry' andbF in Uc.
Step Hcrx: (contour (last ry r') r x).
  Step Hprx: (mem2 c ry' x) By Rewrite: Dc -cat1s mem2_cat Hx orbT.
  By Rewrite: -Ec (mem2l_cat Hpq1ry') /= mem2_adds set11 Dry' -Er' in Hprx.
Step Hrc: (cycle rlink r) By Rewrite: (cycle_path x).
Apply/and5P; Split; Auto; Try By Rewrite: simple_catC /r -Dpr.
  Rewrite: /inner_dart; Step HrxF: (fband r x).
    By Rewrite: -Ebcr fband_border; Apply: (subsetP (ring_fband ?)).
  Rewrite HrxF; Move: (fproj r x) (fprojP HrxF) => rx [Hrx Hxrx].
  Pose rx' := (face (edge (prev r rx))).
  Step Hrx'rx: (cface rx' rx) By Rewrite: /rx' -cface1; Apply: (prev_cycle Hrc).
  Case/splitPr Dr: r / {}Hrx (cycle_prev (simple_uniq Ur)) => [r1 r2].
  Rewrite: (cycle_path ry) path_cat -Dr {3 r}Dr /= -Dr; Case/and3P=> [_].
  Move/eqP=> Drx' _; Move: Hcrx; Rewrite: Dr contour_cat /= Drx' -/rx' -cat_adds.
  Rewrite: trajectS; Pose q := (traject face rx' (S (findex face rx' rx))).
  Rewrite: mem_cat /setU mem_cat /setU orbCA orbC; Case/orP=> [Hqx].
    Move: Ur; Rewrite: Dr simple_catC /= simple_adds simple_cat fband_cat.
    Case/and4P=> [H Ur2 _ Ur1]; Case/idP: H.
    Rewrite: Dr path_cat /= in Hr; Case/and3P: Hr=> [Hr1 _ Hr2].
    Move: (contourP Hr1 Ur1) (contourP Hr2 Ur2) => [_ _ _ []] [_ _ _ []].
    Rewrite: !fband_border -orbC -fband_cat.
    By Apply/hasP; Exists x; Rewrite: ?mem_cat 1?Sface.
  Rewrite: /q in Hqx; Case/trajectP: Hqx => [j Hj Dx].
  Step Dj: j = (findex face rx' x).
    By Rewrite: -Dx findex_iter; RightBy Apply: (leq_trans Hj); Apply findex_max.
  Step Exrx: (negb x =d rx).
    Apply/eqP=> [Drx]; Rewrite: Dc in Uc; Case/andP: Uc; Case/idP.
    Step Hfex: (contour (last ry r) r fex).
      Rewrite: Dr -cat_add_last; Case Dr2: r2 => [|x2 r2'].
        By Rewrite: cats0 last_add_last headI -{1 rx}Drx /x /= Enode setU11.
      Rewrite: contour_cat last_add_last mem_cat; Apply/or3P; Constructor 2.
      By Rewrite: -Drx /x Enode set11.
    Case Dp: p Ec => [|x' p'].
      Rewrite: /q1; Case Di: i => [|i'].
        By Rewrite: Di /= /y Dp /= /x Enode in Ery'; Rewrite: Ery' (mem2l Hx).
      Rewrite: Dc /=; Injection=> [] _; Rewrite mem_cat; Apply/orP; Right.
      By Rewrite: Dry' -Er'.
    Rewrite: Dc /=; Injection=> [] _; Rewrite mem_cat; Apply/orP; Right.
    By Rewrite: Dry' -Er'.
  Rewrite: Dj ltnS in Hj; Rewrite: -(leq_add2l (findex face x rx)).
  Rewrite: (findex_sym (Iface g) Hxrx Exrx).
  Rewrite: addnS addnC (add_findex_leql (Iface g) Hrx'rx Hj).
  By Rewrite: (arity_cface Hxrx) -(arity_cface Hrx'rx) findex_max.
Step Hrry: (r ry) By Apply: setU11.
Rewrite: /outer_dart -/y; Apply/andP; Split; LeftBy Apply/hasP; Exists ry.
Rewrite: (fproj_cface r Hyry) (simple_fproj Ur Hrry).
Move: (cycle_prev (simple_uniq Ur)); Rewrite: (cycle_path x).
Case/andP; Case/eqP; Clear; Rewrite: /= Er' -Dry' leqNgt.
Apply/idP=> [Hy]; Move: Ec Uc; Rewrite: /q1; Case Di: i => [|i'].
  Case/lastP Dp: p / {}p => [|p' z].
    By Rewrite: Dc; Injection=> _ []; Rewrite: /= (mem2l Hx).
  Move: (simple_uniq UcF); Rewrite: Dpr uniq_cat; Case/and3P; Clear; Case/hasP.
  Exists z; RightBy Rewrite: Dp mem_add_last /= setU11.
  Rewrite: lastI Er' -{(last x c)}Eedge -Dry' -Ery' Di /= /y Eedge.
  By Rewrite: mem_add_last Dp last_add_last /= setU11.
Case; Rewrite: uniq_cat; Case/and3P; Clear; Case/hasP; Exists y.
  Rewrite: mem_cat; Apply/orP; Left; Apply/trajectP.
  Exists (findex face ry' y); LeftDone.
  By Rewrite: iter_findex // (same_cface Hry'ry) Sface.
By Rewrite: mem_cat /setU /= setU11 orbT.
Qed.

Lemma borderSpred : (c : (seq g))
  (size (border c)) = (if c is Seq0 then (0) else (S (pred (size (border c))))).
Proof.
Case=> // [x c]; Move: (fband_border (Adds x c) x).
By Case: (border (Adds x c)) => //=; Rewrite: connect0.
Qed.

Lemma simplify_moebius :
  (c : (seq g)) (moebius c) -> {c' : (seq g) | (simple_moebius c')}.
Proof.
Pose cR := [c; z](drop (S (index z::g c)) c).
Pose cF := [c; z](andb (borderb z (cR c z)) (fband (cR c z) z)).
Move=> c; Elim: {c}(S (size (border c))) {-2}c (ltnSn (size (border c))) => //.
Move=> n Hrec c; Pose b := (border c); Move=> Hn Hcm.
Case Dc: c {}Hcm => // [x c']; Case/and3P; Pose y := (face (edge (last x c'))).
Rewrite: -Dc (finv_eq_monic (Enode g)); Move=> Hxy Uc Hc'.
Step Hxc: (preborderb (node x) c) By Rewrite: Dc /= set11.
Step Hc: (path clink (node x) c) By Rewrite: Dc /= clinkN.
Pose i := (find (cF c) c); Case: (leqP (size c) i) => [Hi].
  Exists c; Rewrite: /simple_moebius ~Hcm -/b /= simple_recI ~{n Hn Hrec}.
  Move: Hi Uc; Rewrite: ~/b ~/i leqNgt -has_find ~{Dc Hc Hxc}.
  Elim: c => //= [z c Hrec]; Rewrite: /cF {1 2}/cR /= set11 drop0.
  Move/norP=> [Hz Hc]; Move/andP=> [Uz Uc].
  Step UcF: (simple_rec (border c)).
    Apply: Hrec Uc; Apply/hasP=> [[t Hct Ht]]; Case/hasP: Hc; Exists t; Auto.
    By Rewrite: /cR /=; Case: (t =P z) => // [Dt]; Rewrite: -Dt Hct in Uz.
  By Case: (borderb z c) Hz => //=; Rewrite: ~UcF andbT fband_border.
Move: (cat_take_drop i c);  Pose c1 := (take i c); Rewrite: (drop_sub x Hi).
Pose z := (sub x c i); Pose c2 := (drop (S i) c); Move=> Ec.
Step Hz: (cF c z) By Apply: sub_find; Rewrite: has_find.
Pose q := (orbit face (face z)); Pose j := (find c q).
Step Hcq: (has c q).
  Apply/hasP; Exists z; LeftBy Rewrite: /q -fconnect_orbit Sface fconnect1.
  By Rewrite: -Ec mem_cat /setU /= setU11 orbT.
Step Hj: (ltn j (size q)) By Rewrite: /j -has_find.
Pose t' := (sub x q j); Pose q1 := (take j q).
Step Hcq1: (negb (has c q1)).
  Apply/(has_subPx x ? ?)=> [[k Hk Ek]].
  Def: Hkj := Hk; Rewrite: /q1 (size_takel (ltnW Hj)) in Hkj.
  By Case/idP: (before_find x Hkj); Rewrite: -(cat_take_drop j q) -/q1 sub_cat Hk.
Step Hzc2: (borderb z c2) By Case/andP: Hz; Rewrite: /cR /z index_uniq.
Step Hc2t': (c2 t').
  Move: (sub_find x Hcq); Rewrite: -/j -/t' -Ec -cat_add_last mem_cat.
  Case/orP=> // [Hc1t']; Case/andP: Hz; Clear; Case/idPn.
  Rewrite: /cR {1}/z index_uniq // -/c2 /fband (eq_has (cface1 z)).
  Rewrite: (eq_has (fconnect_orbit face (face z))) -/q has_sym.
  Step Eq: (last z q) = z.
    By Rewrite: /q /orbit last_traject arity_face iter_face_arity.
  Step Hq: (fpath face z q) By Apply: fpath_traject.
  Move: (uniq_orbit face (face z)) Hq Eq; Rewrite: -/q.
  Rewrite: has_sym -Ec has_cat /= orbA in Hcq1; Case/norP: Hcq1; Clear.
  Move/negbE=> H; Rewrite: -(cat_take_drop j q) -/q1 has_cat has_sym ~H /=.
  Rewrite: (drop_sub x Hj) -/t' last_cat /= uniq_cat path_cat /=.
  Case/and3P=> [_ _ Uq2]; Case/and3P=> [_ _]; Move: {}Uc Uq2.
  Rewrite: -Ec -cat_add_last uniq_cat has_sym; Case/and3P=> [_ Uc12 _].
  Elim: (drop (S j) q) t' Hc1t' {Hrec} => [|t'' q2 Hrec] t' Ht' /=;
    Rewrite: (negbE (hasPn Uc12 ? Ht')) //.
  Move/andP=> [Ut' Uq2]; Move/andP=> [Dt'' Hq2] Eq2; Apply: Hrec Uq2 {}Hq2 {}Eq2.
  Rewrite: mem_add_last /= in Ht'; Case/setU1P: Ht' => [Dt' | Ht'].
    By Rewrite: -Dt' -Eq2 mem_lastU in Ut'.
  Step Ht'c1z: (ltn (S (index t' c)) (size (add_last c1 z))).
    By Rewrite: -Ec index_cat Ht' size_add_last ltnS index_mem.
  Step Ht'i: (ltn (index t' c) i).
    By Rewrite: size_add_last /c1 (size_takel (ltnW Hi)) in Ht'c1z.
  Step Hct': (c t') By Rewrite: -Ec mem_cat /setU Ht'.
  Move/nandP: (before_find x Ht'i); Rewrite: sub_index // /cR -{2 4 c}Ec.
  Rewrite: -cat_add_last drop_cat Ht'c1z; Case.
    Rewrite: (drop_sub x Ht'c1z) {1 S}lock /= negb_elim (eqP Dt'') eqd_sym -lock.
    By Case/eqP; Apply mem_sub.
  Case/hasP; Exists z.
    Rewrite: drop_add_last; RightBy Rewrite size_add_last in Ht'c1z.
    By Rewrite: mem_cat /setU mem_add_last /= setU11.
  By Apply/connectP; Exists (Adds t'' q2); LeftBy Rewrite: /= Dt''.
Step Hq1: (fpath face z (add_last q1 t')).
  Step Hq: (fpath face z q) By Apply: fpath_traject.
  Move: Hq; Rewrite: -(cat_take_drop (S j) q) (take_sub x) // path_cat -/q1 -/t'.
  By Case/andP.
Pose c1' := (take i c').
Step Dc1': (Adds x c1') = (add_last c1 z) By Rewrite: /c1 /z -take_sub // Dc.
Step Ec1': (last x c1') = z By Move: (congr (last x) Dc1'); Rewrite last_add_last.
Step Ec': (cat c1' c2) = c' By Rewrite: /c1' /c2 Dc /= cat_take_drop.
Case/splitPr: c2 / Hc2t' Hzc2 Ec Ec' => [c2 c3] Hzc2 Ec Ec'.
Step Hc2t': (negb (face (last z c2)) =d t').
  Case Dc2: c2 Hzc2 => [|fez c2'] /= Hzfez; LeftBy Rewrite: (negbE Hzfez).
  Apply/eqP=> [Dt'] {Hzfez}.
  Rewrite: -cats1 path_cat in Hq1; Case/and3P: Hq1; Clear.
  Rewrite: -~Dt' /eqdf (inj_eqd (Iface g)).
  Case/lastP: q1 Hcq1 => [|q1' t''].
    Move=> _ /= Dz; Move: Uc; Rewrite: -Ec uniq_cat /=; Case/and4P=> [_ _].
    By Rewrite: mem_cat /setU Dc2 (eqP Dz) mem_last.
  Rewrite: last_add_last has_add_last -Ec mem_cat /= Dc2.
  Move/norP=> [H _] Dt''; Case/orP: H; Right; Apply/orP; Right.
  By Rewrite: (eqP Dt'') mem_cat /setU mem_last.
Step Ec2: (last z c2) = (node t').
  Move: Hc; Rewrite: -Ec path_cat /= path_cat /=; Case/and5P=> [_ _ _].
  By Case/clinkP=> // [Dt']; Case/eqP: Hc2t'.
Step Hq1t': (face (last z q1)) =d t'.
  By Move: Hq1; Rewrite: -cats1 path_cat; Case/and3P.
Step Hzq1: (q' : (seq g)) (borderb z (cat (add_last q1 t') q')) = false.
  By Move=> *; Move: Hq1; Rewrite: headI /=; Case/andP => *; Apply: negbIf.
Pose c'' := (Adds x (cat c1' (cat (add_last q1 t') c3))).
Step Hc''n : (ltn (addn (size (border c'')) (size (border c2))) n).
  Rewrite ltnS in Hn; Apply: leq_trans Hn.
  Rewrite: /b -Ec -cat_add_last (border_cat x) last_add_last Hzc2.
  Rewrite: (border_cat z) {1 6 border}lock /= Hc2t' !size_cat addnCA addnC -addnS.
  Rewrite: leq_add2l -lock /c'' -cat_adds Dc1' (border_cat x) last_add_last Hzq1.
  Rewrite: size_cat size_behead size_belast borderSpred -Dc1' -addSn leq_add2l.
  Elim: {}q1 {}z Hq1 {Hrec} => /= [|z'' q1' Hrec] z'; Case/andP; Case/eqP.
    By Rewrite leqnn.
  By Move=> H; Case: q1' H {Hrec}(Hrec ? H) => [|z''' q1'] /=;
    Case/andP; Case/eqP; Clear; Rewrite set11.
Step [Hc'' Hc2]: (path clink (node x) c'') /\ (path clink z c2).
  Rewrite: /c'' -cat_adds Dc1' !path_cat /= !last_add_last.
  Move: Hc; Rewrite: -Ec -cat_add_last !path_cat /= !last_add_last.
  Move/and4P=> [H1 H2 _ H3]; Rewrite: ~H1 ~H3 andbT /=; Split; Auto.
  Apply: (sub_path ? Hq1); Apply: (!sub_relUr).
Step Uc'': (uniq (cat c2 c'')).
  Rewrite: /c'' cat_add_last -!cat_adds uniq_catCA catA uniq_catCA -!catA.
  Rewrite: Dc1' cat_add_last /= Ec uniq_catC uniq_cat Uc Hcq1.
  Move: (uniq_orbit face (face z)); Rewrite: -/q -(cat_take_drop j q) uniq_cat.
  By Case/andP.
Step Dy: (finv node (last t' c3)) = y.
  By Rewrite: (finv_eq_monic (Enode g)) /y -Ec' !last_cat.
Case Hc2y: (c2 y).
  Case/splitPr Dc2: c2 / Hc2y => [c12 c23]; Apply (Hrec (cat c'' (Adds y c23))).
    Apply: leq_trans Hc''n; Rewrite: ltnS Dc2 !(border_cat x) !size_cat.
    Rewrite: !addnA leq_add2r; Apply: (leq_trans ? (leq_addr ? ?)).
    Case (borderb (last x c'') (Adds y c23)); LeftBy Apply leqnn.
    By Rewrite: size_behead size_belast -subn1 leq_sub_add leq_addl.
  Rewrite: /c'' cat_adds; Apply/and3P; Split.
      Rewrite: Dc2 !last_cat /= in Ec2 *; Rewrite: Ec2 (finv_f (Inode g)).
      Rewrite: cat_add_last -!catA catA mem2_cat -orbA orbCA; Apply/orP; Left.
      Rewrite: cat_adds mem2_adds set11.
      Move: Uc Hxy; Rewrite: -/y -Ec' -Ec -cat_add_last -Dc1' /=; Case/andP; Clear.
      Rewrite: Dc2 -!catA catA uniq_cat; Case/and3P=> [_]; Case/norP=> [Hy _] _.
      Rewrite: (mem2l_cat (negbE Hy)) cat_adds mem2_adds set11 -!mem_adds.
      By Rewrite: -!cat_adds !mem_cat /setU orbC.
    By Move: Uc''; Rewrite: Dc2 -catA uniq_cat uniq_catC; Case/and3P.
  Move: Hc''; Rewrite: path_cat /= clinkN /=; Move=> H; Rewrite: ~H /=.
  Apply/andP; Split; RightBy Move: Hc2; Rewrite: Dc2 path_cat /=; Case/and3P.
  By Rewrite: /y -Ec' !last_cat last_add_last /= -{1 (last t' c3)}Eedge clinkN.
Case Hc2nx: (c2 (node x)).
  Case/splitPr Dc2: c2 / Hc2nx => [c12 c23]; Rewrite: -cat_add_last in Dc2.
  Apply (Hrec (cat (add_last c12 (node x)) c'')).
    Apply: leq_trans Hc''n; Rewrite: addnC ltnS Dc2 !(border_cat x) !size_cat.
    Rewrite: leq_add2r last_add_last.
    Case H23: (borderb (node x) c23) (borderb (node x) c'')  => [|] [|];
      Rewrite: ?leq_addr // size_behead size_belast.
      By Rewrite: -subn1 leq_sub_add addnCA leq_addr.
    Rewrite: (borderSpred c23) borderSpred headI -headI /=.
    By Case: {}c23 H23 => // *; Rewrite: addnS ltnS leq_addr.
  Step Dfez: (head (node x) c12) = (face (edge z)).
    Move: Hc2 Hzc2; Rewrite: Dc2 headI /=; Case/andP; Case/clinkP=> [Dz].
      By Rewrite: Dz Enode.
    By Rewrite: Dz set11.
  Rewrite: headI cat_adds; Apply/and3P; Split.
      Rewrite: /c'' !last_cat Dfez Eedge /= -cat_adds Dc1' !last_cat last_add_last.
      Rewrite: Dy mem2_cat -orbA orbCA mem2_cat -!orbA; Apply/orP; Left.
      Rewrite: -{2 z}(last_add_last z c1) headI /= mem2_last -headI.
      Move: Uc Hxy; Rewrite: -/y -Ec' -Ec -cat_add_last -Dc1' /=; Case/andP; Clear.
      Rewrite: !uniq_cat; Case/and5P=> [_ _ _]; Rewrite: has_sym {1 c2}Dc2.
      Rewrite: cat_add_last has_cat /= orbCA -mem_adds; Case/norP=> [Hnx _] _.
      Rewrite: catA (mem2r_cat (negbE Hnx)); Move/mem2l.
      Rewrite: mem_cat /setU Hc2y orbF; Apply: (!setU1r).
    Rewrite: -cat_adds -headI.
    By Move: Uc''; Rewrite: Dc2 -catA uniq_catCA uniq_cat; Case/and3P.
  Move: (last_add_last x c12 (node x)); Rewrite: headI /= path_cat; Case/esym.
  Rewrite: Hc'' andbT; Move: Hc2; Rewrite: Dc2 path_cat headI /= -andbA.
  By Case/and3P.
Apply (Hrec c''); LeftBy Apply: leq_trans Hc''n; Rewrite: ltnS leq_addr.
Rewrite: /c''; Apply/and3P; Split.
    Rewrite: cat_add_last !last_cat /= Dy; Apply mem2_splice.
    By Move: Hxy; Rewrite: -/y -Ec' catA mem2lr_splice.
  By Move: Uc''; Rewrite uniq_cat; Case/and3P.
By Case/andP: Hc''.
Qed.

Theorem rjordanP : (reflect ring_jordan (planarb g)).
Proof.
Apply: (iffP (planarP g)) => [Hg r x p | Hg c]; Apply/idP.
  Case/ring_moebius_simple=> [c]; Case/andP; Case/negPf; Apply Hg.
Case/simplify_moebius=> [c']; Case/simple_moebius_ring=> [r [x [p Hrxp]]].
By Case/idP: (Hg r x p).
Qed.

End RingJordan.

Unset Implicit Arguments.
