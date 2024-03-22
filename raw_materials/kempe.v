(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require tacticext.
Require boolprop.
Require funs.
Require dataset.
Require natprop.
Require seq.
Require color.
Require chromogram.
Require finset.
Require paths.
Require connect.
Require hypermap.
Require walkup.
Require jordan.
Require geometry.
Require coloring.

Set Implicit Arguments.

(* The proof of the kempe closure property of planar quasitriangulations.  *)
(* This is the main link between the reflected combinatorial reducibility  *)
(* proofs, and the mathematical theory of planar graphs developed in the   *)
(* rest of the proof. The result is also reused to validate the reduction  *)
(* to internally 5-connected triangulations.                               *)
(* We start by showing a side result that if a color sequence's edge trace *)
(* can be matched by a coloring, then in fact the color sequence can be    *)
(* matched exactly.                                                        *)
(* The file also contains a three small functions on chromograms that      *)
(* mangle chromograms by flipping brackets in various ways. These are used *)
(* to match changes in the perimeter as edges are removed in the main      *)
(* theorem, which proceeds by induction on the graph size, much as the     *)
(* proof of the euler formula; indeed, it uses the `euler_tree' lemma from *)
(* that proof to do the edge selection.                                    *)

Section KempeMap.

(* Negate the bit of the first unmatched pop. *)

Fixpoint gram_neg_rec [n : nat; w : chromogram] : chromogram :=
  Cases w n of
    (Adds Gpush w') _ => (Adds Gpush (gram_neg_rec (S n) w'))
  | (Adds Gskip w') _ => (Adds Gskip (gram_neg_rec n w'))
  | (Adds s w') (S n) => (Adds s (gram_neg_rec n w'))
  | (Adds Gpop0 w') (0) => (Adds Gpop1 w')
  | (Adds Gpop1 w') (0) => (Adds Gpop0 w')
  | Seq0 _ => w
  end.

Definition gram_neg : chromogram -> chromogram := (gram_neg_rec (0)).

Lemma match_gram_neg : (b0 : bool; et : colseq; w : chromogram)
    (matchg (Seq b0) et (gram_neg w))
       = (matchg (Seq (negb b0)) et w).
Proof.
Move=> b0 et w; Pose sb := (seq0::bitseq).
Step Esb: (b : bool) (Adds b sb) = (add_last sb b) By Done.
Rewrite: /gram_neg -{(0)}/(size sb) 2!~Esb.
Elim: w et sb => [|s w Hrec] et lb; LeftBy Case lb.
Case Ds: s; (Case: et => [|e et]; LeftBy Case lb); First [
  By Case: e [b](Hrec et (Adds b lb)); Simpl
| By Case: e; Case: lb => [|b lb]; Rewrite: /= ?if_negb ?Hrec].
Qed.

(* Flip the next unmatched pop into a push, and adjust the bit of the next *)
(* pop so that the total parity is inverted. This rebalances a chromogram  *)
(* that has two extra pops.                                                *)

Fixpoint gram_flip_rec [n : nat; w : chromogram] : chromogram :=
  Cases w n of
    (Adds Gpush w') _ => (Adds Gpush (gram_flip_rec (S n) w'))
  | (Adds Gskip w') _ => (Adds Gskip (gram_flip_rec n w'))
  | (Adds s w') (S n) => (Adds s (gram_flip_rec n w'))
  | (Adds Gpop0 w') (0) => (Adds Gpush (gram_neg w'))
  | (Adds Gpop1 w') (0) => (Adds Gpush w')
  | Seq0 _ => (Adds Gpush w)
  end.

Definition gram_flip : chromogram -> chromogram := (gram_flip_rec (0)).

Lemma match_gram_flip : (et : colseq; w : chromogram)
    (matchg seq0 et (gram_flip w))
       = (orb (matchg (Seq true false) et w) (matchg (Seq false true) et w)).
Proof.
Move=> et w; Pose lb0 := (Adds true (Adds false seq0)).
Rewrite: /gram_flip; Pose lb0' := (Adds false (Adds true seq0)).
Rewrite: -(cat0s lb0) -(cat0s lb0'); Pose sb := (seq0::bitseq).
Rewrite: -{(0)}/(size sb); Elim: w et sb => [|s w Hrec] et lb.
  By Case: et lb => [|[|||] [|e et]] [|b lb].
Case s; (Case: et => [|e et]; LeftBy Case lb); First [
  By Case: e [b](Hrec et (Adds b lb)); Simpl
| By Case: e; Case: lb => [|[|] lb];
  Rewrite: /= ?if_negb ?Hrec // /= ?orbF ?match_gram_neg].
Qed.

(* Rotate a chromogram by moving the first symbol at the end, and flipping *)
(* it if it's a push. We check for imbalanced chromograms first, to ensure *)
(* that matchg is always preserved.                                        *)

Definition gram_rot [w : chromogram] : chromogram :=
  if (set0b [b](gram_balanced (0) b w)) then w else
  Cases w of
    (Adds Gpush w') => (gram_flip (add_last w' Gpop1))
  | (Adds Gskip w') => (add_last w' Gskip)
  | _ => w
  end.

Lemma match_gram_rot : (et : colseq; w : chromogram)
  (matchg seq0 (rot (1) et) (gram_rot w)) = (matchg seq0 et w).
Proof.
Move=> et w; Rewrite: /gram_rot; Case Hw0: (set0b [b](gram_balanced (0) b w)).
  By Apply/idP/idP; Case/matchg_balanced; Rewrite (set0P Hw0).
Move/set0Pn: Hw0 => [b0]; Case: et w => [|e et]; LeftBy Do 4 Case=> //.
Rewrite: rot1_adds; Move=> [|[|||] w] /= Hw; Try By Case: e et; Do 2 Try Case.
  Cut (b : bool; lb : bitseq) (gram_balanced (size lb) b0 w) ->
    (matchg (Adds b lb) (add_last et e) (add_last w Gpop1)) =
      (andb e =d (ccons true (negb (last b lb))) (matchg (belast b lb) et w)).
    By Move=> Ew; Rewrite: match_gram_flip !Ew //; Case e; Rewrite: ?orbF.
  Move=> b lb; Rewrite andbC; Elim: w lb b b0 et {Hw} => [|s w Hrec] lb b b0 et.
    By Case: lb => // [] _; Case: b; (Case: et; [Case: e | Do 2 Try Case]).
  Case: et => [|e' et]; LeftBy Case: s; Case: e {Hrec} => //; Case: b; Case: w.
  Case: s; Case: e' => //=; First [Apply: Hrec | Apply: (Hrec (Adds b lb))
      | Case: b; Case: lb => [|b' lb] //=; Apply: Hrec].
Elim: w (seq0::bitseq) et {b0 Hw} => [|s w Hrec] lb et.
  By Case e; Case: et; Do 2 Try Case.
Case: et => [|e' et]; LeftBy Case e; Case: s lb => [|||] [|[|] lb] //; Case w.
By Case: s; Case: e' => //=; Try Apply: (Hrec (Adds ? lb));
  Case: lb => [|[|] lb'] //=; Case e.
Qed.

(* The main theorem, in one big piece.                                      *)

Theorem kempe_map : (g : hypermap; r : (seq g))
 (ucycle_planar_plain_quasicubic r) -> (kempe_closed (ring_trace r)).
Proof.
Move=> g r; Do 3 Case; Move=> HgE HgN; Move/andP=> [Hr Ur] Hpg.
Move=> et [k Hk Det]; Split.
  Move=> h; Exists (comp h k).
    Move: (iso_inj (iso_permc h)) Hk => Ih [HkE HkN].
    By Split; Move=> x; Rewrite [f](invariant_inj f Ih k).
  By Rewrite: (maps_comp h k) -/(permt h) trace_permt -Det.
Cut (r : (seq g))
    (fcycle node r) -> (uniq r) -> (quasicubic r) ->
    (EX w | (matchg seq0 (urtrace (maps k r)) w)
          & (et : colseq; Hpc: (matchg seq0 et w))
            (EX k' | (coloring k') & et = (urtrace (maps k' r)))).
  Move=> H; Case: {H}(H (rot (1) r)); Rewrite: ?cycle_rot ?uniq_rot //.
    By Apply: subset_trans HgN; Apply/subsetP=> [x]; Rewrite: /setC mem_rot.
  Move=> w Hw Hpc; Rewrite: maps_rot urtrace_trace -Det in Hw.
  Exists w; LeftDone; Move=> et' Het'; Case: (Hpc ? Het') => [k' Hk' Det'].
  By Rewrite: maps_rot urtrace_trace in Det'; Exists k'.
Move{r et Hr Ur HgN Det}=> r Hr Ur HgN; Move: r Hr Ur Hpg HgE HgN k Hk.
Elim: {g}(S (card g)) {-3 -4}g (ltnSn (card g)) => [|n Hrec] g Hn //.
Move=> r Hr Ur Hpg HgqE HgqN k [HkE HkF]; Case Dr: r Hr Ur HgqN => [|r0 r'].
  By Do 3 Clear; Exists (seq0::chromogram); RightBy Case; LeftBy Exists k; Split.
Move: {HgqE}(plain_eq HgqE) (plain_neq HgqE) => Dee HgE.
Rewrite: -Dr /=; Move=> Hr Ur HgqN.
Step HkN: (x : g) ~(k (node x)) = (k x).
  Move=> x Hkx; Case/eqcP: (HkE (node x)).
  By Rewrite: -(eqcP (HkF (edge (node x)))) Enode.
Step HgN: (x : g) (x =d (node x)) = false.
  By Move=> x; Apply/eqP=> [Dnx]; Case (HkN x); Congr k.
Case Hgpi: (negb (has [z](setU1 z (setC r) (face z)) r)).
  Step HgNp: (planar (permN g)) By Rewrite: planar_permN.
  Case/set0Pn: (euler_tree (planarP ? HgNp) r0) => /= [] x; Move/andP=> [Hrx Hx].
  Step Hr0: (r r0) By Rewrite: Dr /= setU11.
  Def: Er := (fconnect_cycle Hr Hr0).
  Case/hasP: Hgpi; Exists x; LeftBy Rewrite: -Er.
  Case/orP: Hx => [Hx | Hfx].
    Case/clinkP: Hx => /=; LeftBy Case; Rewrite setU11.
    By Move=> *; Case/eqP: (HgE x).
  By Rewrite: /cross_edge /= -(same_cnode Hrx) Er in Hfx; Apply: setU1r.
Case/hasP: Hgpi {r0 r' Dr} => [] z.
Def Di: i := (if (index z r) is (S i) then (subn (size r) (S i)) else (0)).
Elim: i r Di Hr Ur HgqN => [|i Hreci] r Di Hr Ur HgqN Hrz.
  Case Dr: {1 2 3}r {}Hrz {Di}(introT eqP Di) => [|z' p]; LeftDone.
  Rewrite: /= /setU1; Case Hz': (negb z =d z').
    Rewrite: eqd_sym (negbE Hz') eqd_sym subSS eqn_sub0 leqNgt /=.
    By Move=> H; Rewrite: index_mem H.
  Do 2 Clear; Case/eqP: {z'}Hz' Dr => [] Dr.
  Move: {Hrz}(fconnect_cycle Hr Hrz) => EpN.
  Rewrite: Dr /= -cats1 path_cat /= {2}/eqdf andbT in Hr Ur.
  Move/andP: Hr => [Hp Ep]; Move/andP: Ur => [Hpz Up].
  Case Dp: p Hp => [|nz p'] /=; LeftBy Rewrite: Dp /= eqd_sym HgN in Ep.
  Case/andP; Move/eqP=> Dnz Hp'; Pose fz := (face z); Pose ez := (edge z).
  Step Hez: (setC1 z ez) By Rewrite: /setC1 /ez eqd_sym HgE.
  Pose ez' := ((subdI Hez)::(walkupN z)); Pose g' := (walkupE ez').
  Step Deez' : (edge ez') = ez'.
    By Apply: subdE_inj; Rewrite: /= /skip1 /= /ez Dee set11.
  Step Hg'n : (ltn (card g') n).
    Move: (card_sub_dom (setC1 ez')) => /= E; Rewrite: ~E -ltnS.
    Apply: leq_trans Hn; Rewrite: -(cardC (set1 z)) card1 add1n !ltnS.
    Apply: (leq_trans (max_card ?)). 
    By Move: (card_sub_dom (setC1 z)) => /= E; Rewrite: ~E leqnn.
  Pose h := ([x'](subdE (subdE x')) :: g' -> g).
  Step Hh: (x : g; Hzx : (negb z =d x); Hezx : (negb ez =d x))
           {x' : g' | (h x') = x}.
    Move=> x Hzx Hezx.
    By Exists ((subdI Hezx::(setC1 ez' (subdI Hzx::(setC1 z x))))::g').
  Step Ehd : (x', y' : g') (x' =d y') = ((h x') =d (h y')) By Done.
  Step Ih : (injective h) By Move=> x' y' Ex'y'; Do 2 Apply: subdE_inj.
  Step Hzh : (x' : g') (z =d (h x')) = false By Move=> [[x Hx] Hx']; Apply negbE.
  Step Hezh : (x' : g') (ez =d (h x')) = false By Move=> [x' Hx']; Apply negbE.
  Step DhE : (x' : g') (h (edge x')) = (edge (h x')).
    Move=> [[x Hzx] Hezx]; Rewrite: /setC1 /eqd /= in Hezx *.
    Rewrite: /h /= /skip_edge1 /= /eqd /= /skip1 /= /ez Dee !set11 /=.
    By Rewrite: /skip1 /= -(Dee z) (inj_eqd (Iedge g)) (negbE Hezx).
  Pose nez := (node ez); Step DhN : (x' : g') (h (node x')) =
   [nx := (node (h x'))]if z =d nx then nez else if ez =d nx then nz else nx.
    Move=> [[x Hzx] Hezx]; Rewrite: /setC1 {2}/eqd /= in x Hzx Hezx *.
    Rewrite: /h /= /skip1 /= (fun_if (subdE 2!(setC1 z))) {1}/eqd /=.
    Rewrite: /skip_edge1 /= -{3 6 9 15 z}Dee Eedge-/ez.
    Rewrite: !(inj_eqd (Iedge g)) !HgN.
    Case Hznx: (z =d (node x)).
      Rewrite: -(eqP Hznx) !(eqd_sym ez) (negbE Hez) set11.
      By Rewrite: {1 z}(eqP Hznx) (inj_eqd (Inode g)) eqd_sym (negbE Hezx).
    Case Heznx: (ez =d (node x)); RightBy Rewrite Heznx.
    By Rewrite: (eqP Heznx) (inj_eqd (Inode g)) eqd_sym (negbE Hzx).
  Def: Hpg' : (planar g') := (planar_walkupE ? (planar_walkupN ? Hpg)).
  ClearBody h g'; Step Hg'qE : (plain g').
    Apply/plainP=> [x' _].
    By Split; [Apply Ih; Rewrite: !DhE Dee | Rewrite: Ehd DhE HgE]. 
  Step Hg'k: (coloring (comp k h)).
    Split; Move=> x'; Rewrite: /invariant /comp; LeftBy Rewrite DhE; Apply: HkE.
    Rewrite: -{2 x'}Eface DhE DhN /setA; Move: {x'}(h (face x')) => y.
    Rewrite: -{1 y}Enode; Case: (z =P (node y)) => [[]|_].
      By Rewrite: (eqcP (HkF (edge z))) -{(edge z)}Enode; Apply: HkF.
    Case: ((edge z) =P (node y)) => [[]|_]; RightBy Apply: HkF.
    By Rewrite: Dee (eqcP (HkF z)) -{z}Enode Dnz; Apply: HkF.
  Move=> Hz; Step [r' Hr' Dr'] : (EX r' | (fcycle node r') &
    (maps h r') = (if z =d fz then p' else (Adds nez (Adds fz p)))).
    Step Hup: (x' : g'; q : (seq g)) (fpath node (h x') q)
      -> (negb (q z)) -> (negb (q (edge z)))
      -> (EX q' | (maps h q') = q & (fpath node x' q')).
      Move{Hrec}=> x' q; Elim: q x' => [|y q Hrec] x'; LeftBy Exists (Seq0 g').
      Rewrite: /= {1}/eqdf /setU1 !(eqd_sym y); Move/andP => [Dnx Hq].
      Move/norP=> [Hzy Hqz]; Move/norP=> [Hezy Hqez].
      Case: {Hzy Hezy}(Hh ? Hzy Hezy) => [y' Dy].
      Rewrite: -Dy in Hq; Case: {Hrec Hq Hqz Hqez}(Hrec y' Hq Hqz Hqez).
      Move=> q' Dq Hq'; Exists (Adds y' q'); LeftBy Rewrite: /= Dy Dq.
      By Rewrite: /= Hq' /eqdf Ehd DhN (eqP Dnx) -Dy Hzh Hezh set11.
    Rewrite: Dp /= in Hpz; Case/norP: Hpz => [Hznz Hpz].
    Case Hfz: (z =d fz) Hz => [|] /= Hz.
      Step Eez: ez = nz By Rewrite: /ez -(Eface g z) Dee -(eqP Hfz).
      Case: p' Dp Hpz Hp' => [|nnz p'] Dp; LeftBy Exists (Seq0 g').
      Rewrite: Dp /= -Eez /setU1 !(eqd_sym nnz) in Up *; Case/andP: Up.
      Move/norP=> [Heznnz Hp'ez] _; Move/norP=> [Hznnz Hp'z]; Case/andP.
      Move/eqP => Dnnz Hp'; Move: (Hh ? Hznnz Heznnz) => [nnz' Ennz].
      Rewrite: -Ennz in Hp'; Case: (Hup ? ? Hp' Hp'z Hp'ez) => [q' Dp' Hq'].
      Exists (Adds nnz' q'); RightBy Rewrite: /= Ennz Dp'.
      Rewrite: /= -cats1 path_cat Hq' /eqdf /= Ehd DhN.
      Rewrite: Dp -Dp' /= -Ennz last_maps in Ep.
      By Rewrite: (eqP Ep) Ennz set11 -Dnnz -/nez set11.
    Rewrite eqd_sym in Hznz; Case: (Hh ? Hznz).
      By Rewrite: -Dnz eqd_sym (monic2F_eqd (Enode g)) /ez Dee -/fz Hfz.
    Move=> nz' Dnz'; Rewrite: -Dnz' in Hp'; Case: (Hup ? ? Hp' Hpz).
      Apply/idP=> [Hpez]; Case/idP: Hz; Rewrite: -EpN Snode cnode1.
      By Rewrite: /fz -{1 z}Dee Eedge Snode EpN Dr Dp /= /setU1 Hpez !orbT.
    Move=> q' Dq' Hq'; Case (Hh nez).
        Apply/eqP=> [Dnez]; Case/idP: Hz; Rewrite: -EpN Snode.
        By Rewrite: /fz {2 z}Dnez /nez /ez -{2 z}Eface Dee -cnode1r fconnect1.
      By Rewrite: /nez HgN.
    Move=> nez' Dnez'; Move: (cubicP HgqN ? Hz) => [Dfz _].
    Step Hezfz: (ez =d fz) = false.
      By Rewrite: eqd_sym /ez -(Eface g z) -/fz Dee HgN.
    Case: (Hh fz (negbI Hfz) (negbI Hezfz)) => [fz' Dfz'].
    Exists (Adds nez' (Adds fz' (Adds nz' q')));
      RightBy Rewrite: /= Dfz' Dnez' Dnz' Dq' -Dp.
    Rewrite: /= -cats1 path_cat Hq' /eqdf /= !Ehd !DhN.
    Rewrite: Dp -Dq' /= -Dnz' last_maps in Ep.
    Rewrite: Dnez' Dfz' Dnz' (eqP Ep) !set11 {2 3}/fz -{3 4 z}Dee Eedge -/ez.
    Rewrite: set11 (negbE Hez) /nez {1 4 5}/ez -{2 3 4 z}Eface Dee -/fz Dfz /=.
    By Rewrite: Hfz Hezfz !set11. 
  Step Hg'qN: (quasicubic r').
    Apply/cubicP => [y' Hy']; Pose y := (h y'); Case Hy: (maps h r' y).
      By Rewrite: /y (mem_maps Ih) in Hy; Case (negP Hy').
    Rewrite Dr' in Hy; Case Hry: (r y).
      Rewrite: Dr /= /setU1 {1}/y Hzh /= in Hry.
      Case: (z =P fz) Hy => [Dfz | _] Hy.
        Rewrite: Dp /= /setU1 Hy orbF in Hry.
        By Rewrite: -Dnz Dfz /fz -(Dee z) Eedge -/ez /y Hezh in Hry.
      By Rewrite: /= /setU1 Hry !orbT in Hy.
    Case: (cubicP HgqN ? (negbI Hry)) => [Dnnny _].
    Case Hzny: (z =d (node y)).
      By Rewrite: -EpN Snode (eqP Hzny) fconnect1 in Hry.
    Step Dny': (h (node y')) = (node y).
      Rewrite: DhN -/y /= Hzny; Case: (ez =P (node y)); RightDone.
      Move=> Dez; Rewrite: /fz -{2 3 z}Dee -/ez Dez Enode {1}/y Hzh in Hy.
      By Rewrite: /= /setU1 set11 /= !orbT in Hy.
    Step Dnny': (h (node (node y'))) = (node (node y)).
      Rewrite: DhN Dny' /=; Case: (z =P (node (node y))) => [Dz | _].
        By Rewrite: -EpN -Dnnny -Dz fconnect1 in Hry.
      Case: (ez =P (node (node y))) => [Dez | _]; RightDone.
      Rewrite: {1}/fz -{2 z}Dee -/ez /nez Dez Enode Dnnny Hzny in Hy.
      By Rewrite: /= /setU1 set11 in Hy.
    Split; LeftBy Apply Ih; Rewrite: DhN Dnny' -/y Dnnny /= /y Hzh Hezh.
    By Rewrite: Ehd Dny' -/y eqd_sym HgN.
  Step Ur': (uniq r').
    Rewrite: -(uniq_maps Ih) Dr'.
    Case Hfz: (z =d fz) Hz; LeftBy Rewrite Dp in Up; Case/andP: Up.
    Rewrite: /= Up; Move=> Hpfz; Move: (cubicP HgqN ? Hpfz) => [Efz _].
    Rewrite: /setC Dr /= /setU1 Hfz /= in Hpfz.
    Rewrite: {1}/fz -(Dee z) Eedge -/ez -/nez in Efz.
    Rewrite: /setU1 (negbE Hpfz) -Efz eqd_sym HgN /= andbT.
    Apply/idP => [Hpnez]; Move: (EpN nez).
    Rewrite: Dr /= (setU1r z Hpnez) Snode cnode1.
    By Rewrite: Efz Snode EpN Dr /= /setU1 Hfz (negbE Hpfz).
  Case: {n Hrec Hn Hg'n Hr' Ur'}(Hrec ? Hg'n ? Hr' Ur' Hpg' Hg'qE Hg'qN ? Hg'k).
  Rewrite: ~{Hpg' Hg'qE Hg'qN Hg'k}(maps_comp k h) Dr'; Move=> w Hw Hwet.
  Step Huk : (k' : g' -> color; Hk' : (coloring k'); e1 : color)
     (if z =d fz then (negb e1 =d Color0)
      else (proper_trace (ptrace (urtrace (maps k' r')))))
     -> {k'' : g -> color | (coloring k'') & k' =1 (comp k'' h)
             /\ ((z =d fz) -> (addc (k'' z) (k'' nz)) = e1)}.
    Move=> k'; Step [k1 Dk1]: {k1 : g -> color | k' =1 (comp k1 h)}.
      Exists [x]if pick x' in [x'](x =d (h x')) then (k' x') else Color0.
      Move=> x'; Unfold comp; Case: (pickP [y'](h x') =d (h y')).
        By Move=> y' Dy'; Rewrite: (Ih ? ? (eqP Dy')).
      By Move=> H; Case: (elimF eqP (H x')).
    Move=> [Hk'E Hk'F] e1 He1.
    Step Hk1fz: (z =d fz) = false -> ~ (k1 fz) = (k1 (last z p)).
      Move=> Hfz Dk1nz; Move: He1; Rewrite: (eq_maps Dk1) (maps_comp k1 h).
      Rewrite: Dr' Hfz /proper_trace /= Dk1nz Dp /= last_maps.
      By Rewrite: {1 addc}lock addcC -lock addcc.
    Exists [x]if z =d x then
                if z =d fz then (addc e1 (k1 (last z p))) else (k1 fz)
              else if ez =d x then (k1 (last z p)) else (k1 x).
      Split; Move=> x; Apply/eqP.
        Rewrite: -{1 z}Dee -/ez {2}/ez !(inj_eqd (Iedge g)).
        Rewrite: -(addc_inv (k1 (last z p)) e1) -(addcC e1) in He1.
        Case Hezx: (ez =d x).
          Rewrite: -(eqP Hezx) (negbE Hez); Case Hfz: (z =d fz) He1; Auto.
          By Move=> He1 De1; Rewrite: De1 addcc in He1.
        Case Hzx: (z =d x).
          Case Hfz: (z =d fz) He1 => [|] He1; RightBy Apply nesym; Auto.
          By Move=> De1; Rewrite: -De1 addcc in He1.
        Case: (Hh ? (negbI Hzx) (negbI Hezx)) => [x' []].
        By Move/eqcP: (Hk'E x'); Rewrite: !Dk1 -DhE.
      Case Hzx: (z =d x) => /=.
        Rewrite: -(eqP Hzx) -/fz (eqd_sym ez) /ez -{4 z}Eface Dee -/fz HgN.
        By Case (z =d fz).
      Case Hezx: (ez =d x).
        Rewrite: (eqd_sym z) -{1 z}Eedge -/ez (eqP Hezx) HgN.
        By Rewrite: -{3 x}(eqP Hezx) /ez -{2 z}(eqP Ep) Enode if_same.
      Case: (Hh ? (negbI Hzx) (negbI Hezx)) => [x' Dx'].
      Move/eqcP: (Hk'F x') {}Dx'.
      Rewrite: /= -{3 x'}Eface !Dk1 /comp DhE DhN Dx' /=; Case.
      Pose y := (h (face x')); Case Hzny: (z =d (node y)).
        Move=> Dx; Rewrite: -{1 2 x}Dx /nez Enode (negbE Hez) set11.
        By Rewrite: -(eqP Ep) in Hzny; Rewrite: (Inode ? (eqP Hzny)).
      Case Hezny: (ez =d (node y)).
        Move=> Dx; Rewrite: -{1 x}Dx -Dnz Enode set11.
        Rewrite: -{1 z}Enode Dnz Dx /fz (inj_eqd (Iface g)) eqd_sym Hzx.
        By Rewrite: -(Dee z) -/ez (eqP Hezny) Enode.
      By Case; Rewrite: Enode {1 2}/y Hzh Hezh.
    Split; LeftBy Move=> y; Rewrite: /comp Hzh Hezh Dk1.
    Move=> Hfz; Rewrite: Hfz set11 -Dnz {3 5 z}(eqP Hfz) /fz -{3 5 z}Dee Eedge.
    By Rewrite: -/ez (negbE Hez) set11 -addcA addcc addc0.
  Case Hfz: (z =d fz) Dr' Hw Huk => [|] /= Dr' Hw Huk.
    Step He1k: (k' : g -> color; Hk' : (coloring k'))
               (EX e1 | (negb e1 =d Color0) &
                 (urtrace (maps k' r)) =
                   (Adds e1 (Adds e1 (urtrace (maps k' p'))))).
      Move=> k' [Hk'E Hk'F]; Pose e1 := (addc (k' z) (k' nz)); Exists e1.
        Rewrite: /e1 -eq_addc0; Apply/eqP => [De1]; Case/eqcP: (Hk'E nz).
        By Rewrite: -De1 -{z}Enode Dnz [y](eqcP (Hk'F y)).
      Move: Ep; Rewrite: Dr Dp /urtrace /= addcC last_maps.
      Case: {}p' => [|nnz q] Dz //=.
      Rewrite: /= -{z}Eedge -{z}Eface -/fz Dee -(eqP Hfz) Dnz in Dz.
      By Rewrite: last_maps (Inode g (eqP Dz)) (eqcP (Hk'F nz)).
    Case (He1k k); [By Split | Move=> e1 He1 Dkr; Rewrite Dkr].
    Exists (if e1 =d Color1 then (Adds Gskip (Adds Gskip w))
                            else (Adds Gpush (Adds Gpop0 w))).
      By Case De1: e1 He1.
    Move=> et Het; Step [e1' He1' [et' Het' Det]]:
        (EX e1' | (negb e1' =d Color0) & (EX et' | (matchg seq0 et' w)
          & et = (Adds e1' (Adds e1' et')))).
      By Case: (e1 =d Color1) Het; Case: et => [|e1' et] //; Case De1': e1' => //;
         Move=> Hetw; Exists e1'; Rewrite: De1' //;
         Case: et Hetw => [|[|||] et] //; Exists et.
    Case: (Hwet ? Het') => [k1 Hk1 Det'].
    Case: (Huk ? Hk1 ? He1') => [k' Hk' [Dk' Dk'x]]; Exists k'; LeftDone.
    Rewrite: (eq_maps Dk') (maps_comp k' h) Dr' in Det'.
    Case: (He1k ? Hk') => [e1'' _ Dk'r]; Rewrite: Det Dk'r -Det' -Dk'x //.
    By Rewrite: Dr Dp /= in Dk'r; Injection: Dk'r => _ [].
  Move: Hw; Rewrite: {1 p}Dp /urtrace /= last_maps.
  Pose e1 := (addc (k (last nz p')) (k z)).
  Pose e2 := (addc (k (last nz p')) (k nez)).
  Step [] :  (addc e2 e1) = (addc (k nez) (k fz)).
    Rewrite: /fz (eqcP (HkF z)) /e2 {1 addc}lock addcC -lock -addcA.
    By Rewrite: /e1 addc_inv.
  Case: w Hwet => [|s1 [|s2 w]] Hwet //; LeftBy Case s1; Case e2.
  Rewrite: /fz (eqcP (HkF z)); Move=> Hw.
  Step He1: (negb e1 =d Color0).
    Rewrite: Dp /= (monic2F_eqd (Enode g)) in Ep.
    Rewrite: /e1 -eq_addc0 (eqP Ep) (eqcP (HkF (edge z))).
    Apply negbI; Apply: HkE.
  Step Hs12: Cases s1 s2 of
      Gpush Gpop0 => False
    | Gpush _ => True
    | Gskip Gpush => True
    | _ _ => False
    end.
    By Case: s1 Hw {Hwet} => //; Case: e2 => //; Case: e1 He1 => //; Case s2.
  Exists (Cases s1 s2 of
    Gpush Gpush => (Adds Gskip (gram_flip w))
  | Gpush Gskip => (Adds Gpush (gram_neg w))
  | Gskip _ => (Adds Gpush (gram_neg w))
  | _ _ => (Adds Gskip w)
  end).
    Rewrite: Dr /= Dp /urtrace /= last_maps -/e1; Move: Hw {Hwet}.
    Move: (Adds (addc (k z) (k nz)) (pairmap addc (k nz) (maps k p'))) => et.
    By Case: s1 Hs12 => //; Case: e2 => //; Case: s2 => // [] _;
      Case: e1 He1; Rewrite: //= ?match_gram_neg //;
      Move=> _ Hw'; Rewrite: match_gram_flip Hw' ?orbT.
  Move=> [|e et]; LeftBy Case: (s1) Hs12; Case s2.
  Move=> Het; Pose m01etw := (matchg (Seq false true) et w).
  Pose e' := Cases s1 s2 m01etw of
    Gpush Gpush true => Color3
  | Gpush Gskip _ => (addc Color1 e)
  | Gskip Gpush _ => Color1
  | _ _ _ => Color2
  end; Case: {Hw Hwet}(Hwet (Adds e' (Adds (addc e' e) et))).
    By Rewrite: ~/e'; Case: s1 Hs12 Het => //; Case: s2 => //; Case: e;
       Rewrite: //= ?match_gram_neg // ?match_gram_flip orbC -/m01etw;
       Case Hw: m01etw.
  Move=> k1 Hk1 Det; Case (Huk ? Hk1 Color0).
    Rewrite: -~Det /ptrace /proper_trace /= addc_inv ~{e'}.
    By Case: e Het => //; Case: s1 {Hs12} => //; Case s2.
  Move=> k' [Hk'E Hk'F] [Dk' _]; Exists k'; LeftBy Split.
  Move: Det; Rewrite: (eq_maps Dk') (maps_comp k' h) Dr' Dr /urtrace /=.
  Rewrite: /fz (eqcP (Hk'F z)); Injection=> [] De De'; Congr Adds.
  By Rewrite: -(addc_inv e' e) De De' -addcA addc_inv.
Step [r' Dr]: (EX r' | r = (rot (1) r')).
  By Exists (rotr (1) r); Rewrite rot_rotr.
Rewrite: Dr cycle_rot in Hr; Rewrite: Dr uniq_rot in Ur.
Rewrite: Dr mem_rot in Hrz.
Move=> Hz; Rewrite: Dr /setU1 /setC mem_rot in Hz.
Case: {Hreci}(Hreci r'); Auto.
    Apply eq_add_S; Move: {Di}(esym Di).
    Case Dj: (index z r) => [|j] //; Rewrite: -~{j}Dj; Case.
    Rewrite: Dr; Case: {}r' Hrz Ur => [|y q]; LeftDone.
    Rewrite: size_rot /rot index_cat /= drop0 take0 /setU1 eqd_sym.
    Case: (z =P y) => [Dz | _].
      By Clear; Move/andP=> [Hqy _]; Rewrite: Dz (negbE Hqy) addn0 subSnn.
    Simpl; Move=> Hqz _; Rewrite: Hqz.
    By Rewrite: -index_mem in Hqz; Rewrite: (leq_subS (ltnW Hqz)).
  By Apply: (subset_trans (introT subsetP [x]?) HgqN);
    Rewrite: Dr /setC mem_rot.
Move=> w Hw Hwet; Exists (gram_rot w).
  By Rewrite: Dr maps_rot urtrace_rot match_gram_rot.
Move=> et; Rewrite: -(rot_rotr (1) et) match_gram_rot Dr.
Move=> Hw'; Case: (Hwet ? Hw') => [k' Hk' Duet]; Exists k'; Auto.
By Rewrite: maps_rot urtrace_rot -Duet.
Qed.

End KempeMap.

Unset Implicit Arguments.
