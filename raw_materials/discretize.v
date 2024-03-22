(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require tacticext.
Require boolprop.
Require funs.
Require dataset.
Require natprop.
Require seq.
Require paths.
Require hypermap.
Require geometry.
Require coloring.
Require znat.
Require grid.
Require matte.
Require gridmap.
Require real.
Require realmap.
Require realprop.
Require approx.

Set Implicit Arguments.

Section DiscretizeMap.

(* Discretizing the coloring problem for an arbitrary finite map. We compute *)
(* a finite hypermap whose colorings induce colorings of the map, using the  *)
(* grid computation package.                                                 *)
(* The discrete approximation is constructed in five steps :                 *)
(* 1) enumerate the regions and adjacencies of m0, choosing a representative *)
(*    border point for each adjacency;                                       *)
(* 2) construct disjoint rectangles covering the border points;              *)
(* 3) construct approximations of the border rectangles;                     *)
(* 4) construct matte approximations of the regions that meet all the        *)
(*    corresponding border rectangles;                                       *)
(* 5) construct a hypermap from the mattes using the grid package.           *)

Variable R : real_model.

Syntactic Definition point := (point R).
Syntactic Definition region := (region R).
Syntactic Definition map := (map R).
Syntactic Definition rect := (rect R).
Syntactic Definition interval := (interval R).

Local Hclassical : excluded_middle := (reals_classic R).

Variable m0 : map.
Hypothesis Hm0 : (finite_simple_map m0).

Definition map_repr : Type := nat -> nat -> point.
Definition adj_repr : Type := nat -> nat -> rect.

Definition adj_point [z1, z2, z : point] : Prop :=
  (adjacent m0 z1 z2) -> (intersect (not_corner m0) (border m0 z1 z2) z).

Definition proper_map_repr [mr : map_repr; n : nat] : Prop :=
  (and (i : nat) (ltn i n) -> (inmap m0 (mr i i))
       (i, j : nat) (ltn i j) -> (ltn j n) ->
         (and ~(m0 (mr i i) (mr j j)) (adj_point (mr i i) (mr j j) (mr i j)))).

Definition cover_map_repr [mr : map_repr; n : nat] : Prop :=
  (subregion (inmap m0) [z](EX i | (ltn i n) & (m0 z (mr i i)))).

Lemma exists_map_repr :
  (EX n | (EXT mr | (proper_map_repr mr n) & (cover_map_repr mr n))).
Proof.
Case: {}Hm0 => [_ [n0 Hmn0]]; Pose n1 := (S n0).
Case: (Hclassical (EXT mr | (proper_map_repr mr n1))).
  Move: Hmn0 => [f Hf] [mr [Hmr Imr]].
  Step [s Ls Ds]: (EX s | (size s) = n1 & (i : nat) (ltn i n1) ->
      let j = (sub (0) s i) in (ltn j n0) /\ (m0 (f j) (mr i i))).
    Elim: {}n1 mr Hmr {Imr} => [|n Hrec] mr Hmr; LeftBy Exists (seq0::natseq).
    Case: {Hrec}(Hrec [i; j](mr (S i) (S j))) {}ltnW => [|s Ls Hs]; Auto.
    Case: (Hf (mr (0) (0))) => [|j Hjn0 Hjf _]; Auto.
    Exists (Seq j & s); LeftBy Rewrite: /= Ls.
    By Move=> [|i]; [Split; LeftBy Apply/ltP | Apply: Hs].
  Clear: Hf Hmr; Step Us: (uniq s).
    Rewrite: -{s}take_size; Move: (leqnn (size s)).
    Elim: {-2}(size s) => [|n Hrec] Hn; LeftBy Rewrite: take0.
    Rewrite: (take_sub (0) Hn) uniq_add_last ~Hrec 1?ltnW // andbT.
    Apply/(subPx (0) ? ?); Rewrite: size_take Hn; Move=> [i Hi Ei].
    Rewrite: Ls in Hn; Case: (Imr ? ? Hi Hn); Case.
    Case: (Ds ? Hn) => [_]; Rewrite: -Ei sub_take //; Apply: (map_trans Hm0).
    By Apply (map_sym Hm0); Case: (Ds ? (ltn_trans Hi Hn)).
  Step [s' Ls' Ds']: (EX s' | (size s') = n0 & s' =1 [i](ltn i n0)).
    Exists (traject S (0) n0); LeftBy Rewrite size_traject.
    Step EitS: (i : nat) (iter i S (0)) = i By Elim=> //= *; Congr S.
    By Move=> i; Apply/trajectP/idP=> [[i' Hi' []] | ]; [Rewrite EitS | Exists i].
  Case/idP: (ltnn n0); Rewrite: -/n1 -Ls -Ls'; Apply: uniq_leq_size => // [i].
  Rewrite: Ds'; Move/(subPx (0) ? ?)=> [j Hj []] {i}; Rewrite Ls in Hj.
  By Case: (Ds ? Hj).
Elim: {n0 Hmn0}n1 => [|n Hrec] Hn.
  By Case: Hn; Exists [i, j : nat](scale_point R (0) Gb00); Split.
Case: (Hclassical (EXT mr:map_repr | (proper_map_repr mr n))); Auto.
Move=> [mr Hmr]; Exists n; Exists mr; Move=> //= z Hz.
Case: (Hclassical (EX i | (ltn i n) & (m0 z (mr i i)))) => [Hmrz]; LeftDone.
Cut (EXT f | (i : nat) (ltn i n) -> (adj_point (mr i i) z (f i))).
  Move=> [f Hf]; Case: Hn; Case: Hmr => [Dmr Hmr].
  Exists [i,j](if (ltn j n) then (mr i j) else if (ltn i j) then (f i) else z).
  Split; LeftBy Move=> i _; Case Hi: (ltn i n); Auto; Rewrite ltnn.
  Move=> i j Hi; Rewrite: ltnS leq_eqVlt orbC !ltnn Hi.
  Case Hj: (ltn j n); LeftBy Rewrite (ltn_trans Hi Hj); Auto.
  Move/(j =P n) => Dj; Rewrite: Dj in Hi; Rewrite Hi; Split; Auto.
  By Move=> Hiz; Case Hmrz; Exists i; RightBy Apply (map_sym Hm0).
Elim: n {Hrec Hn Hmr Hz Hmrz} => [|n [f Hf]].
  By Exists [i : nat](scale_point R (0) Gb00).
Case: (Hclassical (adjacent m0 (mr n n) z)) => [Hn].
  Case: Hn => [t Ht]; Exists [i](if (ltn i n) then (f i) else t).
  Move=> i; Rewrite: ltnS leq_eqVlt orbC; Case Hi: (ltn i n); Auto.
  By Move/(i =P n)=> Di; Rewrite Di; Move.
Exists f; Move=> i; Rewrite: ltnS leq_eqVlt orbC; Case Hi: (ltn i n); Auto.
By Move/(i =P n)=> Di; Rewrite Di; Move=> *; Case Hn.
Qed.

Section AdjRepr.

Variables nr : nat; mr : map_repr.
Hypothesis Hmr : (proper_map_repr mr nr).

Definition proper_adj_repr_at [ar : adj_repr; i, j : nat] : Prop :=
  (and4 (nonempty (ar i j)) -> (adjacent m0 (mr i i) (mr j j))
        (adjacent m0 (mr i i) (mr j j)) -> (ar i j (mr i j))
        (i' : nat) (ltn i' nr) -> (meet (m0 (mr i' i')) (ar i j)) -> (set2 i j i')
        (i', j' : nat) (meet (ar i j) (ar i' j')) -> i = i' /\ j = j').

Lemma exists_proper_adj_repr :
  (EXT ar | (i, j : nat) (regpair nr i j) -> (proper_adj_repr_at ar i j)).
Proof.
Pose ltp := [i, j, i', j'](if j =d j' then (ltn i i') else (regpair j' i j)).
Step Eltp0: (i, j, j' : nat) (ltp i j (0) (S j')) = (ltp i j j' j').
  Move=> i j j'; Rewrite: /ltp /regpair ltnS (leq_eqVlt j).
  Case: (j =P (S j')) => [Dj | _].
    By Rewrite: eqn_leq (ltn_neqAle j) Dj ltnn !andbF.
  By Case: (j =P j') => // [[]]; Rewrite andbT.
Step EltpS: (i, j, i', j' : nat)
   (ltp i j (S i') j') = (orb (andb i =d i' j =d j') (ltp i j i' j')).
  By Move=> i j i' j'; Rewrite: andbC /ltp ltnS (leq_eqVlt i); Case: (j =d j').
Pose patp := [ar; i', j'](i, j : nat)
 if (ltp i j i' j') then (proper_adj_repr_at ar i j) else ~(nonempty (ar i j)).
Cut (EXT ar | (patp ar (0) nr)).        
  Move=> [ar Har]; Exists ar; Move=> i j Hij.
  Move: (Har i j); Rewrite: /ltp Hij; Case: (j =P nr) => // [Dj].
  By Rewrite: Dj /regpair ltnn andbF in Hij.
Elim: {-2}nr (leqnn nr) => [|j' Hrec] Hj'.
  Pose r0 := (real0 R); Pose int0 := (Interval r0 r0).
  Exists [i, j : nat](Rect int0 int0); Move=> i j.
  By Rewrite: /ltp /regpair andbF if_same; Move=> [[x y] [[Hx []]]]; Apply ltrW.
Cut (EXT ar | (patp ar j' j')).
  Move=> [ar Har]; Exists ar; Move=> i j; Rewrite Eltp0; Auto; Apply: Har.
Elim: {1 3}j' (leqnn j') => [|i' Hrec'] Hi'; LeftBy Apply Hrec; Apply ltnW.
Case: {Hrec Hrec'}(Hrec' (ltnW Hi')) => [ar Har].
Case: (Hclassical (adjacent m0 (mr i' i') (mr j' j'))) => [Ha].
  Move: Hmr => [Emr Amr]; Case: (Amr ? ? Hi' Hj').
  Pose zi' := (mr i' i'); Pose zj' := (mr j' j'); Pose zij' := (mr i' j').
  Move=> _ H; Move: {H}(H Ha) => [Hcij' [Hbi' Hbj']].
  Step [rr Err Hrr] : (EXT rr : rect | (rr zij') &
        (i : nat) (ltn i nr) -> (meet (m0 (mr i i)) rr) -> (set2 i' j' i)).
    Elim: {-2}nr (leqnn nr) => [|i Hrec] Hi.
      By Exists (sep_rect zij' zij'); LeftBy Apply mem_sep_rect.
    Case: {Hrec}(Hrec (ltnW Hi)) => [rr Err Hrr]; Pose zi := (mr i i).
    Case: (Hclassical (EXT rr' : rect | (rr' zij') & ~(meet (m0 zi) rr'))).
      Move=> [rr' Err' Hrr']; Def: Drr := (mem_cap_rect rr rr').
      Exists (cap_rect rr rr'); LeftBy Case (Drr zij'); Tauto.
      Move=> k; Rewrite: ltnS leq_eqVlt; Case/setU1P=> [Dk | Hk].
        Rewrite: Dk -/zi; Move=> [z [Hiz Hz]]; Case: Hrr'; Exists z.
        Case (Drr z); Split; Tauto.
      Move=> [z [Hkz Hz]]; Apply Hrr; LeftDone; Exists z.
      Case (Drr z); Split; Tauto.
    Move=> Hzi; Exists rr; LeftDone; Move=> k; Rewrite: ltnS leq_eqVlt.
    Case/setU1P; [Case/esym; Clear; Clear: k rr Err Hrr | Auto].
    Case: Hcij' => [f]; Pose cij' := (corner_map m0 zij'); Move=> Hf.
    Step Hi'n: (ltn i' nr) By Exact (ltn_trans Hi' Hj').
    Step [ii Hii Dii]: (EX ii | (ltn ii (2)) & (m0 (f ii) zi')).
      Case: (Hf zi'); LeftBy Split; Auto; Apply: Emr. 
      By Move=> ii Hii [Dii _]; Exists ii; LeftBy Apply/ltP.
    Step [ij Hij Dij]: (EX ij | (ltn ij (2)) & (m0 (f ij) zj')).
      Case: (Hf zj'); LeftBy Split; Auto; Apply: Emr.
      By Move=> ij Hij [Dij _]; Exists ij; LeftBy Apply/ltP.
    Step [ik Hik Dik]: (EX ik | (ltn ik (2)) & (m0 (f ik) zi)).
      Case: (Hf zi).
        Split; LeftBy Apply: Emr.
        Move=> r Hr Hrzij'; Case: (Hr ? Hrzij') => [rr Hrr Err].
        Case (Hclassical (meet (m0 zi) rr)).
          Move=> [t [Hti Ht]]; Exists t; Split; Auto.
        By Move=> Hirr; Case Hzi; Exists rr.
      By Move=> ik Hik [Dik _]; Exists ik; LeftBy Apply/ltP.
    Step If: (i1, i2, j1, j2 : nat)
      (m0 (f i1) (mr j1 j1)) -> (m0 (f i2) (mr j2 j2)) ->
      (ltn j1 nr) -> (ltn j2 nr) -> (negb j1 =d j2) -> False \/ (negb i1 =d i2).
      Step If': (i1, j1, j2 : nat) (ltn j1 nr) ->
        (m0 (f i1) (mr j1 j1)) -> (m0 (f i1) (mr j2 j2)) -> (leq j1 j2).
        Move=> i1 j1 j2 Hj1 Hmj1 Hmj2; Rewrite: leqNgt; Apply/idP=> [Hj2].
        Case: (Amr ? ? Hj2 Hj1); Case; Apply: (map_trans Hm0) Hmj1.
        By Apply (map_sym Hm0).
      Move=> i1 i2 j1 j2 Hmj1 Hmj2 Hj1 Hj2 Hj12; Right; Apply/eqP=> [Di1].
      Rewrite: Di1 in Hmj1; Rewrite: eqn_leq in Hj12; Case/andP: Hj12; EAuto.
    Apply/norP; Rewrite: ltn_neqAle in Hi'.
    Case/andP: Hi' => [Hi'j' _] [Hi'i Hj'i].
    Case: (If ? ? ? ? Dii Dij) => //.
    Case: {Dii}(If ? ? ? ? Dii Dik) => //.
    Case: {If Dij Dik}(If ? ? ? ? Dij Dik) => //.
    By Case: ii ij ik Hii Hij Hik => [|[|ii]] // [|[|ij]] // [|[|ik]].
  Pose ar' := [i, j](cap_rect (ar i j) (sep_rect zij' (mr i j))).
  Step [rr' [Err' Drr'] Hrr']: (EXT rr' : rect | (rr' zij') /\ (subregion rr' rr)
    & (i, j : nat) (ltp i j j' j') -> (meet (ar' i j) rr') -> i = i' /\ j = j').
    Elim: {1 2}j'=> [|j'' Hrec].
      Exists rr; LeftBy Split; Try Move. 
      By Move=> i j; Rewrite: /ltp /regpair andbF if_same.
    Elim: {1}(S j'') => [|i'' Hreci].
      Case: Hrec => [rr' Drr' Hrr']; Exists rr'; LeftDone.
      Move=> i j; Rewrite: Eltp0; Auto.
    Move: {Hrec}Hreci => [rr' [Err' Drr'] Hrr'].
    Def: Drr'' := (mem_cap_rect rr' (sep_rect (mr i'' (S j'')) zij')).
    Exists (cap_rect rr' (sep_rect (mr i'' (S j'')) zij')).
      Split; LeftBy Case: (Drr'' zij') (mem_sep_rect (mr i'' (S j'')) zij'); Tauto.
      By Move=> z; Case: (Drr'' z) (Drr' z); Tauto.
    Move=> i j Hij [z [Harz Hrrz]]; Rewrite: EltpS in Hij.
    Case: (Drr'' z) => [_ H]; Case: {H Hrrz}(H Hrrz) => [Hrrz Hz].
    Case/orP: Hij; RightBy Move=> Hij; Apply (Hrr' ? ? Hij); Exists z; Split.
    Case/andP; Move/eqP=> Di; Move/eqP=> Dj.
    Def: Dar' := (mem_cap_rect (ar i j) (sep_rect zij' (mr i j))).
    Case: (Dar' z) => [_ H]; Case: {H Harz}(H Harz) => [Harz Hz'].
    Step Emrij: (rr : rect) (rr (mr i j)) -> (rr zij').
      By Rewrite: -Di -Dj in Hz; Apply meet_sep_rect; Exists z; Split.
    Move: (Har i j); Case Hij: (ltp i j i' j'); RightBy Case; Exists z.
    Move=> [Hmrij1 Hmrij2 Harij _]; Step Hmrij: (ar i j (mr i j)).
      By Apply Hmrij2; Apply Hmrij1; Exists z.
    Case Hij': (i =d j').
      Move: Hij; Rewrite: (eqP Hij') /ltp; Case: (j =P j') => [Dj' | _].
        By Rewrite: ltnNge ltnW.
      By Rewrite: /regpair ltn_neqAle leqNgt andbC andbCA andb_neg_b andbF.
    Step Dj': j = j'.
      Apply: eqP; Case: [H](orP (Harij ? Hj' H)) => //; RightBy Rewrite Hij'.
      Rewrite: -/zj'; Apply: Hbj'; Auto.
      By Move=> t Ht; Exists (ar i j); Try Move.
    Split; Auto; Apply: eqP.
    Case: [H](orP (Harij ? (ltn_trans Hi' Hj') H)) => //;
      RightBy Move/eqP=> Di'; Rewrite: -Di' -Dj' ltnn in Hi'.
    Rewrite: -/zi'; Apply: Hbi'; Auto.
    By Move=> t Ht; Exists (ar i j); Try Move.
  Exists [i, j](if (andb i =d i' j =d j') then rr' else (ar' i j)).
  Move=> i j; Rewrite: EltpS /proper_adj_repr_at.
  Case Dij: (andb (i =d i') (j =d j')).
    Case/andP: Dij; Move/eqP=> Di; Move/eqP=> Dj; Rewrite: ~{i}Di ~{j}Dj.
    Split; Auto.
      Move=> i Hi [z [Hiz Hrrz]]; Apply (Hrr ? Hi); Exists z; Split; Auto.
    Move=> i j; Case Dij: (andb (i =d i') (j =d j')).
      By Case/andP: Dij; Split; Apply esym; Apply: eqP.
    Move=> [z [Hrrz Harz]]; Case (Hrr' i j); Try By Try Exists z; Split.
    Def: Dar' := (mem_cap_rect (ar i j) (sep_rect zij' (mr i j))).
    Case: (Dar' z) => [_ H]; Case: {H Harz}(H Harz) => [Harz _].
    Case Hij: (ltp i j i' j') (Har i j); RightBy Case; Exists z.
    Clear; Move: Hij; Rewrite: /ltp; Case: (j =d j') => // [] Hi.
    Exact (ltn_trans Hi Hi').
  Def: Dar' := (mem_cap_rect (ar i j) (sep_rect zij' (mr i j))).
  Case Hij: (ltp i j i' j') (Har i j) {Dij} => //.
    Move=> [Hmrij1 Hmrij2 Harij Iarij]; Split.
     By Move=> [z Hz]; Apply Hmrij1; Exists z; Case: (Dar' z); Tauto.
     By Move/Hmrij2; Case: (Dar' (mr i j)) (mem_sep_rect zij' (mr i j)); Tauto.
     Move=> k Hk [z [Hkz Hz]]; Apply (Harij ? Hk); Exists z; Case (Dar' z).
      By Split; Tauto.
    Move=> i'' j''; Case Dij'': (andb i'' =d i' j'' =d j').
      Case/andP: Dij''; Do 2 (Move/eqP; Case/esym); Apply: Hrr'.
      Move: Hij; Rewrite: /ltp; Case: (j =d j') => // [] Hi.
      Exact (ltn_trans Hi Hi').
    Move=> [z [Hiz Hi''z]]; Apply Iarij; Exists z.
    Split; LeftBy Case (Dar' z); Tauto.
    By Case (mem_cap_rect (ar i'' j'') (sep_rect zij' (mr i'' j'')) z); Tauto.
  Move=> H [z Hz]; Case: H; Case (Dar' z); Exists z; Tauto.
Exists ar; Move=> i j; Rewrite: EltpS.
Case Dij: (andb (i =d i') (j =d j')) (Har i j) => //.
Case/andP: Dij; Do 2 (Move/eqP; Case/esym); Clear: i j.
Rewrite: /ltp set11 ltnn /=; Move=> Harij'; Split.
  By Move=> *; Case Harij'.
  By Move=> *; Case Ha.
  By Move=> i _ [z [_ Hz]]; Case: Harij'; Exists z.
By Move=> i j [z [Hz _]]; Case: Harij'; Exists z.
Qed.

Section DiscrAdj.

Variable ar : adj_repr.
Hypothesis Har : (i, j : nat) (regpair nr i j) -> (proper_adj_repr_at ar i j).

Definition proper_discr_adj_at [s : nat; b : grect; i, j : nat] : Prop :=
  if (garea b) =d (0) then
    ~(adjacent m0 (mr i i) (mr j j))
  else
    (and (mem_approx s (inset2 b) (mr i j))
         (subregion (mem_approx s b) (ar i j))).

Lemma refine_garea0 : (s : nat; b : grect)
    ((garea (iter s refine_rect b)) =d (0)) = ((garea b) =d (0)).
Proof.
Move=> s b; Rewrite: -!leqn0; Elim: s => //= [s Hrec].
By Rewrite: garea_refine_rect -2!double0 !leq_double.
Qed.

Lemma refine_discr_adj : (s, s' : nat; b : grect; i, j : nat)
    (proper_discr_adj_at s' b i j) ->
  (proper_discr_adj_at (addn s s') (iter s refine_rect b) i j).
Proof.
Move=> s s' b i j; Rewrite: /proper_discr_adj_at refine_garea0.
Case: ((garea b) =d (0)) => // [] [Hbmr Hbar]; Split.
  Case: s=> //= [s]; Rewrite: addSn; Apply mem_approx_inset2.
  By Apply: mem_approx_inset; Apply: (!sub_mem_approx R) Hbmr => [p]; Case/andP.
Move=> p; Case (mem_approx_refine_rect s s' b p); Auto.
Qed.

Lemma exists_proper_discr_adj :
  (EX s | (EX da | (i, j : nat) (regpair nr i j)
      -> (proper_discr_adj_at s (da i j) i j))).
Proof.
Pose ltp := [i, j, i', j'](if j =d j' then (ltn i i') else (regpair j' i j)).
Step Eltp0: (i, j, j' : nat) (ltp i j (0) (S j')) = (ltp i j j' j').
  Move=> i j j'; Rewrite: /ltp /regpair ltnS (leq_eqVlt j).
  Case: (j =P (S j')) => [Dj | _].
    By Rewrite: eqn_leq (ltn_neqAle j) Dj ltnn !andbF.
  By Case: (j =P j') => // [[]]; Rewrite andbT.
Step EltpS: (i, j, i', j' : nat)
   (ltp i j (S i') j') = (orb (andb i =d i' j =d j') (ltp i j i' j')).
  By Move=> i j i' j'; Rewrite: andbC /ltp ltnS (leq_eqVlt i); Case: (j =d j').
Pose patp := [s; da; i', j'](i, j : nat)
 if (ltp i j i' j') then (proper_discr_adj_at s (da i j) i j)
                    else (garea (da i j)) =d (0).
Cut (EX s | (EX da | (patp s da (0) nr))).        
  Move=> [s [da Hda]]; Exists s; Exists da; Move=> i j Hij.
  Move: (Hda i j); Rewrite: /ltp Hij; Case: (j =P nr) => // [Dj].
  By Rewrite: Dj /regpair ltnn andbF in Hij.
Elim: {-2}nr (leqnn nr) => [|j' Hrec] Hj'.
  Exists (0); Exists [i, j : nat](Grect (Znat 1) (Znat 0) (Znat 0) (Znat 0)).
  By Move=> i j; Rewrite: /ltp /regpair andbF if_same.
Cut (EX s | (EX da | (patp s da j' j'))).
  Move=> [s [da Hda]]; Exists s; Exists da.
  Move=> i j; Rewrite Eltp0; Auto; Apply: Hda.
Elim: {1 3}j' (leqnn j') => [|i' Hrec'] Hi'; LeftBy Apply Hrec; Apply ltnW.
Case: {Hrec Hrec'}(Hrec' (ltnW Hi')) => [s [da Hda]].
Step Hij': (regpair nr i' j') By Apply/andP; Split.
Case: (Hclassical (adjacent m0 (mr i' i') (mr j' j'))) => [Ha].
  Case: (Har Hij') => [_ H Harij' Iarij']; Move: {H}(H Ha) => Hmrij'.
  Case: (approx_rect Hmrij') => [s' [b [p Dp Hbp] Hbar]]; Exists (S (addn s s')).
  Step Hb: (proper_discr_adj_at (S s') (refine_rect b) i' j').
    Move: (mem_sub_grect Hbp (gtouch_refl ?)).
    Rewrite: /proper_discr_adj_at garea_refine_rect -size_enum_grect.
    Rewrite: -mem_enum_grect; Case: (enum_grect b) => //= [q sq] _ {q sq}; Split.
      By Apply mem_approx_inset2; Exists p.
    Move=> z; Case (mem_approx_refine1_rect s' b z); Auto.
  Exists [i,j](if (andb i =d i' j =d j') then (iter (S s) refine_rect b)
               else (iter (S s') refine_rect (da i j))).
  Move=> i j /=; Rewrite: /proper_discr_adj_at EltpS.
  Case Dij: (andb (i =d i') (j =d j')).
    Rewrite: /= f_iter -iter_f -addnS; Apply: refine_discr_adj.
    By Case/andP: Dij; Do 2 (Move/eqP; Case/esym).
  Rewrite: /= f_iter -addnS addnC; Move: (ltp i j i' j') (Hda i j).
  By Case=> *; [Apply: refine_discr_adj | Rewrite: refine_garea0].
Exists s; Exists da; Move=> i j; Move: (Hda i j); Rewrite: EltpS orbC.
Case: (ltp i j i' j'); LeftDone.
Case Dij: (andb i =d i' j =d j'); RightDone.
Case/andP: Dij; Do 2 (Move/eqP; Case/esym); Move{i j}=> Hg0.
By Rewrite: /proper_discr_adj_at Hg0.
Qed.

Lemma connected_matte : (z : point; r : region; s : nat; m : matte)
  let rm = (mem_approx s m) in
  (r z) -> (subregion rm r) -> (open r) -> (connected r) ->
  (EX s' | (EX m' : matte | let rm' = (mem_approx s' m') in
    (and3 (rm' z) (subregion rm rm') (subregion rm' r)))).
Proof.
Move=> z r s m rm Hrz Hrm Hr Cr.
Pose r1p := [t; s'; m'; rm' := (mem_approx s' m')]
  (and3 (rm' t) (subregion rm rm') (subregion rm' r)).
Pose r1 := ([t](EX s' | (EX m' : matte | (r1p t s' m'))) :: region).
Pose r2 := ([t] (r t) /\ ~(r1 t)).
Step Hrr12: (subregion r (union r1 r2)).
  Move=> t Ht; Rewrite: /union /r2; Case: (Hclassical (r1 t)); Tauto.
Step Hr1r: (meet r1 r).
  Step [p Hmp]: (EX p | (m p)).
    Case: {}m => /= [[|p m'] c H _ _ _] //; Exists p; Apply: setU11.
  Step [t Ht]: (EXT t | (rm t)).
    By Exists (scale_point R s p); Apply: (mem_approx_scale R s m p).
  By Exists t; Split; Auto; Exists s; Exists m; Split; Try Move.
Case: (Hrr12 ? Hrz) => // [Hr2z].
Step Hr2r: (meet r2 r) By Exists z; Split.
Pose sbr := [s'; t : point]
  (EX b | (mem_approx s' (inset b) t) & (subregion (mem_approx s' b) r)).
Step Hr1: (open r1).
  Move=> t [s1 [m1 [Ht Hmm1 Hm1r]]].
  Case: (Hr t (Hm1r ? Ht)) => [rr Hrrt Hrrr].
  Case/approx_rect: Hrrt => [s2 [b2 Hb2t Hb2rr]].
  Step [s3 Hb3 [m3 Hm3]]: (EX s3 | (sbr s3 t) & (EX m3 : matte | (r1p t s3 m3))).
    Exists (addn s1 s2).
      Exists (iter s1 refine_rect b2); LeftBy Apply mem_approx_inset.
      By Move=> u; Case (mem_approx_refine_rect s1 s2 b2 u); Auto.
    Exists (iter s2 refine_matte m1); Rewrite addnC.
    Split; Try By Move=> u; Case (mem_approx_refine_matte s2 s1 m1 u); Auto.
    By Case (mem_approx_refine_matte s2 s1 m1 t); Auto.
  Clear: s1 m1 Ht Hmm1 Hm1r rr Hrrr s2 b2 Hb2t Hb2rr.
  Step [n Hn]: (EX n | (mem_approx s3 [p](leq (matte_order m3 p) n) t)).
    Case: Hb3 => [b [p Hp _] _] {b}; Exists (matte_order m3 p); Exists p; Auto.
    Apply leqnn.
  Elim: n s3 m3 Hn Hm3 Hb3 => [|n Hrec] s' m' [p Dp Hn].
    Move: Hn; Rewrite leqn0; Move/eqP=> Hn Hm' _.
    Case: (rect_approx Dp) => [rr Hrrt Hrr]; Exists rr; LeftDone.
    Case Dmxy: p (matte_order0 Hn) Hrr => [mx my] Hbm' Hrrb.
    Move=> u Hu; Exists s'; Exists m'; Split; Try By Case Hm'.
    Apply sub_mem_approx with 1 := Hbm'; Auto.
  Rewrite: leq_eqVlt in Hn; Case/setU1P: Hn => [Dn | Hn];
    RightBy Apply Hrec; Exists p.
  Move=> [Hm't Hmm' Hm'r] [b Hbt Hbr].
  Case: (approx_point_exists (S s') t) => [p' Dp'].
  Step Epp': (halfg p') = p.
    By Apply approx_point_inj with 2 := Dp; Apply approx_halfg.
  Step Hm'p: (m' p).
    By Case: Hm't => [q Dq Hq]; Rewrite: (approx_point_inj Dp Dq).
  Step Hbp: (inset b p).
    By Case: Hbt => [q Dq Hq]; Rewrite: (approx_point_inj Dp Dq).
  Case: (!refine_matte_order m' b p'); Rewrite: ?Epp' ?Dn //.
  Move=> m'' [Hm'm'' Hm''m'] Hn; Apply: (Hrec (S s') m''); Try By Exists p'.
    Split; Try By Exists p'; RightBy Apply: Hm'm''; Rewrite Epp'.
      Move=> u; Move/(Hmm' ?).
      Case: (mem_approx_refine1_matte s' m' u) => [_ H]; Move/H {H}.
      Apply: sub_mem_approx u => [u]; Rewrite: mem_refine_matte; Auto.
    Move=> u [q Dq]; Move/(Hm''m' ?); Case/orP=> [Hu].
      By Apply Hbr; Exists (halfg q); Try Apply approx_halfg.
    By Apply Hm'r; Exists (halfg q); Try Apply approx_halfg.
  Exists (refine_rect b); LeftBy Apply: mem_approx_inset1.
  By Move=> u; Case (mem_approx_refine1_rect s' b u); Auto.
Step Hr2: (open r2).
  Move=> t [Hrt Hr1t]; Case/(Hr ?): Hrt => [rr Hrrt Hrrr].
  Case/approx_rect: Hrrt => [s2 [b2 Hb2t Hb2rr]].
  Case: (Hclassical (meet (mem_approx s2 b2) r1)).
    Move=> [u [Hb2u [s1 [m1 [Hu Hmm1 Hm1r]]]]]; Case: Hr1t.
    Step [s' [b' [Hb'u Hb't Hb'r] [m' [Hm'u Hmm' Hm'r] Hm'b']]] :
      (EX s' | (EX b' : grect | [rb' := (mem_approx s' b')]
                (and3 (rb' u) (mem_approx s' (inset b') t) (subregion rb' r))
             & (EX m' : matte | (r1p u s' m') & (refined_in m'::(set ?) b')))).
      Exists (addn s1 (S s2)); Exists (iter (S s1) refine_rect b2).
        Rewrite: -addSnnS; Split; Try By Apply mem_approx_inset.
          By Case (mem_approx_refine_rect (S s1) s2 b2 u); Auto.
        By Move=> v; Case (mem_approx_refine_rect (S s1) s2 b2 v); Auto.
      Exists (iter (S s2) refine_matte m1); Rewrite: 1?addnC.
        Split; (Try By Case (mem_approx_refine_matte (S s2) s1 m1 u); Auto);
          By Move=> v; Case (mem_approx_refine_matte (S s2) s1 m1 v); Auto.
      Rewrite: /iter; Apply refine_matte_refined.
    Clear: s1 m1 Hu Hmm1 Hm1r rr Hrrr s2 b2 Hb2t Hb2u Hb2rr.
    Step Hb'm': (has b' m').
      Case: Hb'u Hm'u => [p Dp Hp] [p' Dp' Hp']; Apply/hasP; Exists p; Auto.
      By Rewrite: (approx_point_inj Dp Dp').
    Move: Hb't => [p Dp Hb'p]. 
    Case: (refined_extends_in Hm'b' Hb'm' Hb'p) => [m'' Hm'm'' Hm''m' Hm''p].
    Exists s'; Exists m''; Split; Auto; Try By Exists p.
      Move=> v Hv; Apply sub_mem_approx with 1 := (mem_extension Hm'm''); Auto.
    Move=> v [q Dq]; Move/(Hm''m' ?).
    By Case/orP=> *; [Apply Hb'r | Apply Hm'r]; Exists q.
  Move: Hb2t => [p Dp Hp]; Case: (rect_approx Dp) => [rr' Hrr't Hrr'b2] Hb2r1.
  Exists rr'; Auto; Move=> u Hu; Step Hb2u: (mem_approx s2 b2 u).
    Apply: sub_mem_approx u {Hu}(Hrr'b2 ? Hu) => [[mx my]] Hu.
    Apply: (mem_sub_grect Hp); Case: {}p Hu => [mx' my'].
    Move/and4P=> [Hx0 Hx1 Hy0 Hy1].
    By Rewrite: /= Hx0 Hy0 leqz_dec decz_inc Hx1 leqz_dec decz_inc Hy1 !orbT.
  By Split; Auto; Move=> Hr1u; Case: Hb2r1; Exists u; Split.
By Case: (Cr ? ? Hrr12 Hr1r Hr2r Hr1 Hr2) => [t [Ht [_ []]]].
Qed.

Section DiscrMatte.

Variables sab : nat; ab : adjbox.
Hypothesis Hab : (i, j : nat)
  (regpair nr i j) -> (proper_discr_adj_at sab (ab i j) i j).

Definition ab_pair [i, j : nat] : bool :=
  (andb (regpair nr i j) (ab_adj ab i j)).
 
Definition ab_region [i, j : nat] : region :=
  (mem_approx sab (inset (ab i j))).

Definition proper_discr_matte_at [s : nat; m : matte; i, nj : nat] : Prop :=
  let rm = (mem_approx s m::(set ?)) in
  (and3 (rm (mr i i))
        (subregion rm (m0 (mr i i)))
        (j : nat) (ltn j nj) ->
          (and (ab_pair i j) -> (meet rm (ab_region i j))
               (ab_pair j i) -> (meet rm (ab_region j i)))).

Lemma refine_discr_matte : (s, s' : nat; m : matte; i, nj : nat)
  (proper_discr_matte_at s' m i nj) ->
    (proper_discr_matte_at (addn s s') (iter s refine_matte m) i nj).
Proof.
Move=> s s' m i nj [Hmi Hmri Hmb]; Split;
  Try By Move=> z; Case (mem_approx_refine_matte s s' m z); Auto.
  By Case (mem_approx_refine_matte s s' m (mr i i)); Auto.
Step Href: (r : region) (meet (mem_approx s' m) r) ->
  (meet (mem_approx (addn s s') (iter s refine_matte m)) r).
  Move=> r [z Hz]; Exists z; Rewrite: /intersect.
  By Case (mem_approx_refine_matte s s' m z); Case Hz; Split; Auto.
Move=> j Hj; Case (Hmb ? Hj); Split; Auto.
Qed.

Lemma exists_proper_discr_matte :
  (EX s | (EX cm | (i : nat) (ltn i nr) -> (proper_discr_matte_at s (cm i) i nr))).
Proof.
Step Habp: (i, j : nat) (ab_pair i j) ->
  let mij = [k](meet (m0 (mr k k)) (ab_region i j)) in (mij i) /\ (mij j).
  Move=> i j; Move/andP=> [Hij Habij]; Rewrite: /ab_adj ltnNge leqn0 in Habij.
  Move: (Hab Hij); Rewrite: /proper_discr_adj_at (negbE Habij).
  Move=> [Hmrij Harij]; Case: {}Hmrij => [pij Dpij Hpij].
  Move: (rect_approx Dpij) => [rr Hrrij Hrr].
  Step Hrrab: (subregion rr (ab_region i j)).
    Case: pij Hrr Hpij {Dpij} => [x y] Hrr Hpij u Hu.
    Apply: sub_mem_approx u {Hu}(Hrr ? Hu) => [[x' y']].
    Move/and4P=> [Hx'0 Hx'1 Hy'0 Hy'1]; Case/andP: Hpij; Case (ab i j).
    Move=> x0 x1 y0 y1; Move/and4P=> [_ Hx1 _ Hy1]; Move/and4P=> [Hx0 _ Hy0 _].
    Rewrite: -!decz_def in Hx0 Hy0; Rewrite: /inset /=.
    Rewrite: -leqz_dec2 in Hx'0; Rewrite: -leqz_inc2 in Hx'1.
    Rewrite: -leqz_dec2 in Hy'0; Rewrite: -leqz_inc2 in Hy'1.
    Apply/and4P; Split; EApply leqz_trans; EAuto.
  Step Hcij: (k : nat) let rk = (m0 (mr k k)) in
    (closure rk (mr i j)) -> (meet rk (ab_region i j)).
    Move=> k rz Hk; Case: (Hk rr); Auto.
      By Move=> t Ht; Exists rr; Try Move.
    Move=> t [Ht Hrrt]; Exists t; Split; Auto.
  Step Harij': (nonempty (ar i j)).
    Exists (mr i j); Apply Harij; Apply: (!sub_mem_approx R) Hmrij => [p].
    Case/andP=> [H _]; Apply: (mem_sub_grect H) {H}; Apply gtouch_refl.
  Case: (Har Hij) => [Haij _ _ _]; Case/andP: Hij => [Hi Hj].
  Case: Hmr => [_ H]; Case: {H}(H ? ? Hi Hj) => [_ Hapij].
  Case: (Hapij (Haij Harij')) => [_ [Hcli Hclj]]; Split; Auto.
Elim: {1 3}nr (leqnn nr) => [|i Hrec] Hi.
  By Exists (0); Exists [i : nat](point_matte Gb00).
Cut (EX s | (EX m | (proper_discr_matte_at s m i nr))).
  Move: {Hrex}(Hrec (ltnW Hi)) => [s1 [cm Hcm]] [s2 [m2 Hm2]]; Exists (addn s1 s2).
  Exists [i'](if (i' =d i) then (iter s1 refine_matte m2)
                           else (iter s2 refine_matte (cm i'))).
  Move=> i'; Rewrite: ltnS leq_eqVlt; Case: (i' =P i) => [Di' _ | _ Hi'].
    By Rewrite: Di'; Apply: refine_discr_matte.
  By Rewrite: addnC; Apply: refine_discr_matte; Auto.
Elim: {}nr {Hrec} => [|j [s [m [Hmi Hmri Hma]]]].
  Case: Hmr=> [H _]; Move: {H}(H ? Hi) => Hzi.
  Case: (map_open Hm0 Hzi) => [rr Hrri Hrrm0].
  Case: (approx_rect Hrri) => [s [b [p Dp Hbp] Hbrr]]; Exists s.
  Exists (point_matte p); Split; Try Done.
    By Exists p; RightBy Apply: setU11.
  Move=> z Hz; Apply Hrrm0; Apply Hbrr; Apply: sub_mem_approx z Hz.
  Move=> q /=; Case/setU1P=> // [[]]; Apply (mem_sub_grect Hbp); Apply gtouch_refl.
Step Hmm: (r1, r2, r3 : region) (subregion r1 r2) -> (meet r1 r3) -> (meet r2 r3).
  By Move=> r1 r2 r3 Hr12 [z [Hz1 Hz3]]; Exists z; Split; Auto. 
Case Hij: (ab_pair i j).
  Case: (Habp ? ? Hij) => [[z [Hzi Hzj]] _].
  Case: (connected_matte Hzi Hmri ((map_open Hm0) ?) ((map_connected Hm0) ?)).
  Move=> s' [m' [Hm'z Hmm' Hm'ri]]; Exists s'; Exists m'; Split; Auto.
  Move=> j'; Rewrite: ltnS leq_eqVlt; Case/setU1P=> [Dj' | Hj'].
    Rewrite Dj'; Split; LeftBy Exists z; Split; Auto.
    Case/andP: Hij; Case/andP=> [Hij _] _; Rewrite: /ab_pair /regpair.
    By Rewrite: ltn_neqAle leqNgt Hij andbF.
  Case: (Hma ? Hj'); Split; EAuto.
Case Hji: (ab_pair j i).
  Case: (Habp ? ? Hji) => [_ [z [Hzi Hzj]]].
  Case: (connected_matte Hzi Hmri ((map_open Hm0) ?) ((map_connected Hm0) ?)).
  Move=> s' [m' [Hm'z Hmm' Hm'ri]]; Exists s'; Exists m'; Split; Auto.
  Move=> j'; Rewrite: ltnS leq_eqVlt; Case/setU1P=> [Dj' | Hj'].
    By Rewrite: Dj' Hij; Split; RightBy Exists z; Split; Auto.
  Case: (Hma ? Hj'); Split; EAuto.
Exists s; Exists m; Split; Auto.
Move=> j'; Rewrite: ltnS leq_eqVlt; Case/setU1P=> [Dj' | Hj']; Auto.
By Rewrite: Dj' Hij Hji; Split.
Qed.

End DiscrMatte.

End DiscrAdj.

End AdjRepr.

Lemma discretize_to_hypermap :
  (EXT g : hypermap | (planar_bridgeless g)
                    & (four_colorable g) -> (map_colorable (4) m0)).
Proof.
Case: {}exists_map_repr => [nr [mr Hmr Emr]].
Case: (exists_proper_adj_repr Hmr) => [ar Har].
Case: (exists_proper_discr_adj Har) => [s1 [ab1 Hab1]].
Case: (exists_proper_discr_matte Hmr Har Hab1) => [s2 [cm2 Hcm2]].
Pose s := (addn s1 s2).
Pose ab := [i, j](iter s2 refine_rect (ab1 i j)).
Pose cm := [i](iter s1 refine_matte (cm2 i)).
Step Hab0 : (i, j : nat) (regpair nr i j) ->
  (proper_discr_adj_at mr ar s (ab i j) i j).
  By Move=> *; Rewrite: /s addnC; Apply: refine_discr_adj; Auto.
Step Hcm0 : (i : nat) (ltn i nr) ->
    (proper_discr_matte_at nr mr s ab s (cm i) i nr).
  Step Hrab: (r : region; i, j : nat)
     (meet r (ab_region s1 ab1 i j)) -> (meet r (ab_region s ab i j)).
    Move=> r i j [u [Hru Hu]]; Exists u; Split; Auto.
    By Rewrite: /ab_region /s addnC; Apply: mem_approx_inset.
  Step Eabp: (ab_pair nr ab) =2 (ab_pair nr ab1).
    By Move=> i j; Rewrite: /ab_pair /ab_adj !ltnNge !leqn0 /ab refine_garea0.
  Move=> i Hi; Apply: refine_discr_matte.
  Case: (Hcm2 ? Hi) => [Hcmi Hcmr Hcma]; Split; Auto.
  Move=> j Hj; Rewrite: !Eabp; Case (Hcma ? Hj); Split; Auto.
ClearBody s ab cm; Clear: s1 s2 ab1 cm2 Hab1 Hcm2.
Step Hab1: (i, j : nat) (regpair nr i j) ->
  (subregion (mem_approx s (ab i j)) (ar i j)).
  Move=> i j Hij; Move: (Hab0 ? ? Hij); Rewrite: /proper_discr_adj_at.
  Case Dab: ((garea (ab i j)) =d (0)); RightBy Case.
  Move=> _ z [p _]; Move: Dab; Rewrite: -size_enum_grect -mem_enum_grect.
  By Case (enum_grect (ab i j)).
Step Hab: (ab_proper nr ab).
  Move=> i1 j1 i2 j2 Hij1 Hij2 p Hab1p Hab2p.
  Case: (Har ? ? Hij1) => [_ _ _ H]; Apply: H {H}; Exists (scale_point R s p).
  By Split; Apply: Hab1 => //; Apply: mem_approx_scale.
Step Hcm : (cm_proper nr cm).
  Move=> i j Hij; Apply/hasP=> [[p Hpi Hpj]].
  Case/andP: Hij => [Hij Hj]; Def: Hi := (ltn_trans Hij Hj).
  Case: Hmr => [_ H]; Case: {H}(H ? ? Hij Hj); Case.
  Case: (Hcm0 ? Hi) (Hcm0 ? Hj) => [_ Hcmi _] [_ Hcmj _].
  By Apply (map_trans Hm0) with (scale_point R s p);
    [Apply Hcmi | Apply (map_sym Hm0); Apply Hcmj]; Apply: mem_approx_scale.
Step Habcm : (ab_cm_proper nr ab cm).
  Move=> i j Hij Habij.
  Case/andP: Hij {}Hij => [Hij Hj] Hijn; Def: Hi := (ltn_trans Hij Hj).
  Step Habi: (has (inset (ab i j)) (cm i)).
    Case: (Hcm0 ? Hi) => [_ _ H]; Case: {H}(H ? Hj); Case.
      By Rewrite: /ab_pair Hijn.
    Move=> z [[p Dp Hip] [p' Dp' Habp']] _; Apply/hasP; Exists p; Auto.
    By Rewrite: (approx_point_inj Dp Dp').
  Step Habj: (has (inset (ab i j)) (cm j)).
    Case: (Hcm0 ? Hj) => [_ _ H]; Case: {H}(H ? Hi); Clear; Case.
      By Rewrite: /ab_pair Hijn.
    Move=> z [[p Dp Hip] [p' Dp' Habp']]; Apply/hasP; Exists p; Auto.
    By Rewrite: (approx_point_inj Dp Dp').
  Split; Auto; Move=> k; Apply/andP/idP=> [[Hk] | Dk].
    Move/hasP=> [p Habp Hip]; Case: (Har ? ? Hijn) => [_ _ H _]; Apply: H{H} => //.
    Exists (scale_point R s p); Split.
      By Case: (Hcm0 ? Hk) => [_ Hcmk _]; Apply Hcmk; Apply: mem_approx_scale.
    By Apply Hab1; Auto; Apply: mem_approx_scale.
  Cut (ltn k nr) /\ (has (inset (ab i j)) (cm k)).
    Case; Move=> Hk; Move/hasP=> [p Hkp Habp]; Split; Auto.
    Apply/hasP; Exists p; Auto; Apply (mem_sub_grect Habp); Apply gtouch_refl.
  By Case/orP: Dk; Case/eqP; Split.
Exists (grid_map Hab Hcm Habcm); LeftBy Apply planar_bridgeless_grid_map.
Case/grid_map_coloring=> [k0 Ek0 Hk0].
Pose k := [z1, z2](EX i1 | (ltn i1 nr) /\ (m0 (mr i1 i1) z1) &
                    (EX i2 | (ltn i2 nr) /\ (m0 (mr i2 i2) z2) &
                       (k0 i1) = (k0 i2))).
Step Hm0k: (z1, z2 : point) (m0 z1 z2) ->
           (i1 : nat) (ltn i1 nr) /\ (m0 (mr i1 i1) z1) ->
           (i2 : nat) (ltn i2 nr) /\ (m0 (mr i2 i2) z2) ->
           i1 = i2.
  Case: Hmr => [_ Hmr] z1 z2 Hz12 i1 [Hi1 Hiz1] i2 [Hi2 Hiz2].
  Step Hm0i12: (m0 (mr i1 i1) (mr i2 i2)).
    By Apply: (map_trans Hm0 (map_trans Hm0 Hiz1 Hz12)); Apply (map_sym Hm0).
  Apply: eqP; Rewrite: eqn_leq; Apply/nandP; Case; Rewrite: -ltnNge.
    By Move=> Hi21; Case: (Hmr ? ? Hi21 Hi1); Case; Apply (map_sym Hm0).
  By Move=> Hi12; Case: (Hmr ? ? Hi12 Hi2); Case.
Exists k.
  Step Hpm0: (z1, z2 : point) (m0 z1 z2) -> (inmap m0 z1) /\ (inmap m0 z2).
    Move=> z1 z2 Hz12; Def: Hz21 := (map_sym Hm0 Hz12).
    Move: (map_trans Hm0); Rewrite: /inmap /subregion; Split; EAuto.
  Split.
   Split; Move=> z1 z2 [i1 Hiz1 [i2 Hiz2 Hi12]].
      By Exists i2; RightBy Exists i1.
    Move: {}Hiz2 => [_ Hz2] z3 [j2 Hjz2 [i3 Hiz3 Hi23]].
    Exists i1; Auto; Exists i3; Auto; Rewrite: ~Hi12 -~Hi23 ~{i1 i3 Hiz1 Hiz3}.
    By Congr k0; Case/(Hpm0 ? ?): Hz2 => *; EApply Hm0k; EAuto.
   By Move=> z [i [Hi Hiz] _]; Case/(Hpm0 ? ?): Hiz.
   Move=> z1 z2 Hz12; Case/(Hpm0 ? ?): {}Hz12.
    Move/(Emr ?)=> [i1 Hi1 Hiz1]; Move/(Emr ?)=> [i2 Hi2 Hiz2].
    Exists i1; LeftBy Split; RightBy Apply (map_sym Hm0).
    Exists i2; LeftBy Split; RightBy Apply (map_sym Hm0).
    By Congr k0; Apply (Hm0k ? ? Hz12); (Split; RightBy Apply (map_sym Hm0)).
  Move=> z1 z2 [i1 [Hi1 Hiz1] [i2 [Hi2 Hiz2] Hi12]] Hz12a.
  Apply: (map_trans Hm0) {}Hiz2; Apply (map_sym Hm0); Cut i1 = i2; LeftBy Case.
  Step Hi12a: (adjacent m0 (mr i1 i1) (mr i2 i2)).
    Step Hm0c: (z, z' : point) (m0 z z') ->
      (subregion (closure (m0 z')) (closure (m0 z))).
      Move=> z z' Hzz' t Ht r Hr Hrt.
      Case: (Ht r Hr Hrt) => [u [Hu Hur]]; Exists u; Split; Auto.
      By Apply: (map_trans Hm0) Hu.
    Move: Hz12a => [t [Ht [Ht1 Ht2]]]; Rewrite: /subregion in Hm0c.
    Exists t; Repeat Split; EAuto.
  Clear: z1 z2 Hiz1 Hiz2 Hz12a.
  Cut (i, j : nat) (ltn j nr) -> (k0 i) = (k0 j) ->
     (adjacent m0 (mr i i) (mr j j)) -> (leq j i).
    Move=> Heq; Apply: eqP; Rewrite: eqn_leq; Apply/andP; Split; Auto.
    By Apply Heq; Auto; Case: Hi12a => [z [Hz [Hz1 Hz2]]]; Exists z; Repeat Split.
  Clear: i1 i2 Hi1 Hi2 Hi12 Hi12a.
  Move=> i j Hj Ekij Haij; Rewrite: leqNgt; Apply/idP=> [Hij].
  Step Hijn: (regpair nr i j) By Rewrite: /regpair Hij.
  Move: (Hab0 ? ? Hijn); Rewrite: /proper_discr_adj_at -leqn0 leqNgt.
  Case Habij: (ltn (0) (garea (ab i j))); RightBy Case.
  By Case/eqP: (Hk0 ? ? Hijn Habij).
Pose ic := [c](index c (maps k0 (traject S (0) nr))).
Exists [c](mr (ic c) (ic c)).
Step EitS: (n : nat) (iter n S (0)) = n By Move=> n; Apply: eqP; Elim n.
Move=> z [i [Hi Hiz] _]; Exists (k0 i); LeftBy Apply: ltP; Auto.
Step Hk0i: (maps k0 (traject S (0) nr) (k0 i)).
  By Apply maps_f; Apply/trajectP; Exists i; Rewrite: ?EitS.
Pose j := (ic (k0 i)); Step Hj: (ltn j nr).
  By Rewrite: -index_mem size_maps size_traject in Hk0i.
Exists j; LeftBy Case: Hmr => [H _]; Split; Try Apply H.
Exists i; LeftBy Split.
Rewrite: -(sub_index (0) Hk0i) (sub_maps (0) (0)) ?size_traject ?sub_traject //.
By Rewrite EitS.
Qed.

End DiscretizeMap.

Unset Implicit Arguments.


