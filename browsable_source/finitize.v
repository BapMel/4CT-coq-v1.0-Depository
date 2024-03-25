(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require tacticext.
Require boolprop.
Require funs.
Require dataset.
Require natprop.
Require seq.
Require paths.
Require znat.
Require real.
Require realmap.
Require realprop.
Require grid.
Require approx.

Set Implicit Arguments.

Section FinitizeMap.

(* We use a special case of the compactness theorem for predicate logic to *)
(* extend the four color theorem from finite to arbitrary maps. We can     *)
(* dispense with the axiom of choice because of the local compactness of   *)
(* the plane. This is the only part of the development that is             *)
(* intrinsically classical.                                                *)

Variable R : real_model.

Syntactic Definition point := (point R).
Syntactic Definition region := (region R).
Syntactic Definition map := (map R).
Syntactic Definition rect := (rect R).
Syntactic Definition interval := (interval R).

Local Hclassical : excluded_middle := (reals_classic R).

Variable nc : nat.
Hypothesis Hfin : (m : map) (finite_simple_map m) -> (map_colorable nc m).

Variable m0 : map.
Hypothesis Hm0 : (simple_map m0).

(* We will deduce an enumeration of regions from a canonical enumeration of *)
(* of grid points.                                                          *)

Definition pairn [sn : nat * nat] : nat :=
  let (s, n) = sn in (pred (iter s double (S (double n)))).

Fixpoint unpairn_rec [s, r, n : nat] : nat * nat :=
  Cases r n of
    (S (S r')) (S n') => (unpairn_rec s r' n')
  | (1) (S n') => (unpairn_rec (S s) n' n')
  | _ _ => (s, n)
  end.

Definition unpairn [m : nat] : nat * nat := (unpairn_rec (0) m m).

Lemma pairn_unpair : (monic unpairn pairn).
Proof.
Move=> m; Symmetry; Transitivity (pred (iter (0) double (S (subn (double m) m)))).
  By Rewrite: double_addnn subn_addl.
Rewrite: /unpairn; Elim: m {1 4 5}m (0) (leqnn m) => [|n Hrec] [|[|r]] s //= Hr.
  Case: (unpairn_rec (S s) n n) {Hrec Hr}(Hrec ? (S s) (leqnn ?)) => [s' n'] [].
  By Rewrite: (double_addnn n) subn_addl -iter_f.
By Case: (unpairn_rec s r n) {Hrec Hr}(Hrec r s (leqW Hr)) => [s' n'] [].
Qed.

Lemma unpairn_pair : (monic pairn unpairn).
Proof.
Move=> sn; Move: (pairn_unpair (pairn sn)).
Case: sn (unpairn (pairn sn)) => [s n] [s' n'] /= Ess'.
Step Dss': (iter s' double (S (double n'))) = (iter s double (S (double n))).
  Step Em: (s1, m1 : nat) let m = (iter s1 double (S m1)) in (S (pred m)) = m.
    Move=> s1 m1 /=; Apply: (ltnSpred 2!(0)); Elim: s1=> //= [s1 Hrec].
    By Rewrite: -double0 ltn_double.
  By Rewrite: -Em Ess' Em.
Elim: s s' Dss' {Ess'} => [|s Hrec] [|s'] H;
  Move: {H}(congr odd H) (congr half H);
  Rewrite: /= ?odd_double ?half_double ?uphalf_double //; Clear; Auto.
By Move/(Hrec s'); Injection=> [] [].
Qed.

Definition injzn [m : znat] : nat :=
  Cases m of (Zpos n) => (double n) | (Zneg n) => (S (double n)) end.

Definition uninjzn [n : nat] : znat :=
  if (odd n) then (Zneg (half n)) else (Zpos (half n)).

Lemma uninjzn_inj : (monic injzn uninjzn).
Proof.
By Case=> *; Rewrite: /uninjzn /= odd_double ?half_double ?uphalf_double.
Qed.

Lemma injzn_uninj : (monic uninjzn injzn).
Proof. By Move=> n; Rewrite: -{2 n}odd_double_half /uninjzn; Case (odd n). Qed.

Definition std_point [i : nat] : point :=
  let (s, mxy) = (unpairn i) in let (mx, my) = (unpairn mxy) in
  (scale_point R s (Gpoint (uninjzn mx) (uninjzn my))).

Lemma has_std_point : (z : point) (inmap m0 z) -> (EX i | (m0 z (std_point i))).
Proof.
Move=> z Hz; Case: (map_open Hm0 Hz) => [rr Hrrz Hrrm].
Case: (approx_rect Hrrz) => [s [b [p Hp Hbp] Hbr]]; Case Dp: p => [mx my].
Exists (pairn (s, (pairn ((injzn mx), (injzn my))))); Apply: Hrrm; Apply: Hbr.
Rewrite: /std_point !unpairn_pair !uninjzn_inj -Dp.
Apply: (mem_approx_scale R s b p); Apply: (mem_sub_grect Hbp); Apply gtouch_refl.
Qed.

Definition in_partial [n : nat] : region :=
  [z](EX i | (ltn i n) & (m0 z (std_point i))).

Lemma leq_partial : (n1, n2 : nat) (leq n1 n2) ->
  (subregion (in_partial n1) (in_partial n2)).
Proof.
By Move=> n1 n2 Hn12 z [i Hi Hz]; Exists i; LeftBy Apply: leq_trans Hn12.
Qed.

Lemma partial_trans : (n : nat; z : point)
  (in_partial n z) -> (subregion (m0 z) (in_partial n)).
Proof.
Move=> n z1 [i Hi Hz1] z2 Hz12; Exists i; Auto.
By Apply: (map_trans Hm0) Hz1; Apply (map_sym Hm0). 
Qed.

Lemma proper_inmap_r : (m : map) (proper_map m) ->
  (z : point) (subregion (m z) (inmap m)).
Proof. By Move=> m [Sm Tm] z1 z2 Hz12; Apply: Tm {}Hz12; Apply Sm. Qed.

Lemma proper_inmap_l : (m : map) (proper_map m) ->
  (z : point) (subregion [t](m t z) (inmap m)).
Proof. By Move=> m Hm z1 z2; Move/(map_sym Hm 5!?); Apply: (!proper_inmap_r). Qed.

Definition partial_map [n : nat; m : map] : map :=
  [z1, z2](and3 (m z1 z2) (in_partial n z1) (in_partial n z2)).

Lemma leq_partial_map : (n1, n2 : nat) (leq n1 n2) ->
  (m : map) (covers (partial_map n1 m) (partial_map n2 m)).
Proof.
Move=> n1 n2; Move/leq_partial=> Hn12 m z1 z2 [Hz12 Hz1 Hz2]; Split; Auto.
Qed.

Lemma covers_partial_map : (n : nat; m : map) (covers (partial_map n m) m).
Proof. By Move=> n m z1 z2; Case. Qed.

Lemma proper_partial_map : (n : nat; m : map)
  (proper_map m) -> (proper_map (partial_map n m)).
Proof.
Move=> n m [Sm Tm]; Split; LeftBy Move=> z1 z2 [Hz12 Hz1 Hz2]; Split; Auto.
By Move=> z1 z2 [Hz12 Hz1 _] z3 [Hz23 _ Hz3]; Split; Auto; Apply: Tm Hz23.
Qed.

Lemma finite_partial_map : (n : nat) (finite_simple_map (partial_map n m0)).
Proof.
Move=> n; Split.
  Split; Try Exact (proper_partial_map n Hm0).
    Move=> z1 z2 [Hz12 Hz1 Hz2]; Case: (map_open Hm0 Hz12) => [rr Hrr2 Hrr].
    Exists rr; Auto; Move=> t Ht; Split; Auto; Apply: (partial_trans Hz1); Auto.
  Move=> z r1 r2 Hrz [z1 [Hr1z1 [Hzz1 Hz _]]] [z2 [Hr2z2 [Hzz2 _ _]]].
  Apply: ((map_connected Hm0) z); [Idtac | Exists z1 | Exists z2]; Try By Split.
  By Move=> t Ht; Apply Hrz; Split; Auto; Apply: (!partial_trans) Ht.
Exists n; Exists std_point; Move=> z [_ [i Hi Hzi] Hz].
Exists i; LeftBy Apply: ltP.
By Split; Auto; [Apply (map_sym Hm0) | Apply (partial_trans Hz)].
Qed.

Lemma size_partial_map : (n : nat; k : map)
  (proper_map k) -> (size_at_most nc k) -> (size_at_most nc (partial_map n k)).
Proof.
Move=> n m Hk [f Hf].
Step [f' Hf']: (EXT f' | (j : nat) (ltn j nc) ->
    (z : point) (in_partial n z) -> (m (f j) z) -> (partial_map n m (f' j) z)).
  Elim: {}nc => [|i [f' Hf']]; LeftBy Exists f.
  Case: (Hclassical (nonempty (intersect (m (f i)) (in_partial n)))).
    Move=> [zi [Hkzi Hzi]]; Exists [j]if j =d i then zi else (f' j).
    Move=> j; Rewrite: ltnS leq_eqVlt; Case: (j =P i) => //=; Auto.
    Case/esym=> [] _ z Hz Hiz; Split; Auto.
    By Apply: (map_trans Hk) Hiz; Apply (map_sym Hk).
  Move=> Hi; Exists f'.
  Move=> j; Rewrite: ltnS leq_eqVlt; Case: (j =P i) => //=; Auto.
  Case/esym=> [] _ z Hz Hiz; Case Hi; Exists z; Split; Auto.
Exists f'; Move=> z [Hkz Hz _]; Case: (Hf ? Hkz) => [i Hi Hiz]; Exists i; Auto.
By Apply: Hf' Hz Hiz; Apply/ltP.
Qed.

Record quasi_coloring [k : map] : Prop := QuasiColoring {
  qc_proper :> (proper_map k);
  qc_inmap : (subregion (inmap k) (inmap m0));
  qc_size : (size_at_most nc k);
  qc_adj : (z1, z2 : point) (k z1 z2) -> (adjacent m0 z1 z2) -> (m0 z1 z2)
  }.

Lemma  quasi_coloring_partial : (n : nat; k : map)
  (quasi_coloring k) -> (quasi_coloring (partial_map n k)).
Proof.
Move=> n m [Hk Hkm0 Hnck Hka]; Split.
 By Apply proper_partial_map.
 By Move=> z [Hz _ _]; Auto.
 By Apply size_partial_map.
By Move=> z1 z2 [Hkz12 _ _]; Apply: Hka.
Qed.

Definition partial_coloring [n : nat; k : map] : Prop :=
  (quasi_coloring k) /\ (covers (partial_map n m0) k).

Lemma exist_partial_coloring : (n : nat)
  (EXT k | (partial_coloring n k) & (subregion (inmap k) (in_partial n))).
Proof.
Move=> n; Case: (Hfin (finite_partial_map n)) => [k [Hk Hkn Hnk Hka] Hknc].
Exists k; RightBy Move=> z Hz; Case (Hkn ? Hz).
Do 2 (Split; Auto); LeftBy Move=> z Hz; Case (Hkn ? Hz).
Step Hb: (z, t : point) (in_partial n z) ->
  (closure (m0 z) t) -> (closure (partial_map n m0 z) t).
  Move=> z t Hz Hzt r Hr Hrt; Case: (Hzt r) => // [] u [Hzu Hru].
  By Exists u; Repeat Split; Auto; Apply: (!partial_trans) Hzu.
Move=> z1 z2 Hk12 [z [[f Hf] [Hzz1 Hzz2]]]; Case: (Hka ? ? Hk12) => //.
Case: (Hkn ? (proper_inmap_l Hk Hk12)) => [_ Hz1 _].
Case: (Hkn ? (proper_inmap_r Hk Hk12)) => [_ Hz2 _].
Exists z; Split; RightBy Split; Auto.
Exists f; Move=> t [[Ht Htn _] Htz]; Case (Hf t).
  Split; Auto; Move=> r Hr Hrz; Case: (Htz r) => // [] u [[Htu _ _] Hru].
  By Exists u; Split.
Move=> i Hi [Hit Hiz]; Step Hfi: (in_partial n (f i)).
  By Apply (partial_trans Htn); Apply (map_sym Hm0).
Exists i; Auto; Do 2 (Split; Auto).
Qed.

Lemma leq_partial_coloring : (n1, n2 : nat) (leq n1 n2) ->
  (k : map) (partial_coloring n2 k) -> (partial_coloring n1 k).
Proof.
Move=> n1 n2 Hn12 k [Hk Hkn]; Split; Auto.
By Move=> z1 z2 Hz12; Apply: Hkn; Apply (leq_partial_map Hn12).
Qed.

Definition partial_eq [n : nat; k, k' : map] : Prop :=
  (covers (partial_map n k) k') /\ (covers (partial_map n k') k).

Lemma partial_eq_sym : (n : nat; k, k' : map)
  (partial_eq n k k') -> (partial_eq n k' k).
Proof. By Move=> n k k'; Case; Split. Qed.

Lemma partial_eq_trans : (n : nat; k, k' : map)
  (partial_eq n k k') -> (k'' : map) (partial_eq n k' k'') -> (partial_eq n k k'').
Proof.
Move=> n k1 k2 [Hk12 Hk21] k3 [Hk23 Hk32].
By Split; Move=> z1 z2 [Hz12 Hz1 Hz2]; [Apply Hk23 | Apply Hk21];
  Split; Auto; [Apply Hk12 | Apply Hk32]; Split.
Qed.

Lemma partial_eq_partial : (n : nat; k : map) (partial_eq n k (partial_map n k)).
Proof. By Move=> n k; Split; Move=> z1 z2; RightBy Do 2 Case. Qed.

Lemma leq_partial_eq : (n1, n2 : nat) (leq n1 n2) ->
  (k, k' : map) (partial_eq n2 k k') -> (partial_eq n1 k k').
Proof.
Move=> n1 n2; Move/leq_partial_map=> Hn12 k k' [Hkk' Hk'k].
By Split; Move=> z1 z2 Hz12; [Apply: Hkk' | Apply: Hk'k]; Apply: Hn12.
Qed.

Definition extensible [n : nat; k : map] : Prop :=
  (and3 (quasi_coloring k) (subregion (inmap k) (in_partial n))
       (n' : nat) (EXT k' | (partial_coloring n' k') & (partial_eq n k k'))).

Lemma extensible_partial : (n : nat; k : map)
  (extensible n k) -> (partial_coloring n k).
Proof.
Move=> n k [Hk Ek Xk]; Case: {Xk}(Xk n) =>[k' [Hk' Hk'n] [Hkk' Hk'k]].
By Split; Auto; Move=> z1 z2 Hz12; Apply Hk'k; Case Hz12; Split; Auto; Apply Hk'n.
Qed.

Lemma leq_extensible : (n1, n2 : nat) (leq n1 n2) ->
  (k : map) (extensible n2 k) -> (extensible n1 (partial_map n1 k)).
Proof.
Move=> n1 n2; Move/leq_partial_eq=> Hn12 k [Hk Ek Xk].
Split; Try By First [Apply quasi_coloring_partial | Move=> z [_ Hz _]].
Move=> n; Case: (Xk n) => [k' Hk' Ek']; Exists k'; Auto.
Apply (partial_eq_trans (partial_eq_sym (partial_eq_partial n1 k))); Auto.
Qed.

Definition min_partial1 [i : nat; k : map] : Prop :=
  (j' : nat; k' : map)
    let zi = (std_point i) in let zj' = (std_point j') in
    (partial_eq i k k') -> (extensible (S i) k') -> (k' zj' zi) ->
    (EX j | (leq j j') & (k (std_point j) zi)).

Fixpoint min_partial [n : nat] : map -> Prop :=
  [k]if n is (S i) then (min_partial1 i k) /\ (min_partial i k) else True.

Definition exact_partial [n : nat; k : map] : Prop :=
  (min_partial n k) /\ (extensible n k).

Lemma exists_exact_partial : (n : nat) (EXT k | (exact_partial n k)).
Proof.
Pose ak := [k : map; i, j](k (std_point i) (std_point j)).
Pose inm0 := [j](inmap m0 (std_point j)).
Step Hinm0: (i, j : nat) (ltn j i) -> (inm0 j) -> (in_partial i (std_point j)).
  By Move=> i j; Exists j.
Pose akn := [i, i'; k, k'] (partial_eq i k k') /\ (partial_coloring i' k').
Pose akm := [i, i', j, j'; k, k'] (akn i i' k k') -> (ak k' i j') -> (leq j j').
Pose akx := [i, j; k](EX i' | (ltn i i') & (j' : ?; k' : ?) (akm i i' j j' k k')).
Elim=> /= [|i [k [Hkm [Hk Hkn Xk]]]].
  Exists [z1,z2 : point]False; Do 2 Split; Try By Move.
    By Split; [Split | Move | Exists std_point | Done].
  Move=> n; Case: (exist_partial_coloring n) => [k [Hk Hnk] Hkn].
  By Exists k; Split; Move=> // z1 z2; Case; Clear; Case.
Case: (Hclassical (akx i (S i) k)).
  Case: (Hclassical (inm0 i)) => [Hm0i].
    Move=> [n' Hin' Hn']; Case: (Xk n') => [k' Hk' Ekk']; Case/idP: (ltnn i).
    Apply: (Hn' ? k'); [By Split | Case: Hk' => [_ Hk']; Apply: Hk'].
    By Split; Try Exists i.
  Step Ei: (subregion (in_partial (S i)) (in_partial i)).
    Move=> z [j Hj Hz]; Rewrite: ltnS leq_eqVlt in Hj.
    Case/setU1P: Hj => [Dj | Hj]; RightBy Exists j.
    By Case: Hm0i; Apply: (proper_inmap_r Hm0 3!z); Rewrite: -Dj.
  Clear; Exists k; Split.
    Split; RightDone; Move=> j' k' _ [[Hk' Hm0k' _ _] _ _] Hj'i.
    Case Hm0i; Apply: Hm0k'; Exact (proper_inmap_r Hk' Hj'i).
  Split; Auto; LeftBy Move=> z Hz; Apply (leq_partial (leqnSn i)); Auto.
  Move=> n'; Case: (Xk n') => [k' Hk' [Ekk' Ek'k]]; Exists k'; Auto.
  Split; Move=> z1 z2 [Hz12 Hz1 Hz2]; [Apply: Ekk' | Apply: Ek'k]; Split; Auto.
Elim: {1 3}(S i) (ltnSn i) {Xk} => [|j Hrec] Hj HSj.
  By Case HSj; Exists (S i); LeftBy Apply leqnn.
Case: (Hclassical (akx i j k))=> [[n1 Hin1 Hn1]|]; RightBy Apply Hrec; Apply ltnW.
Clear Hrec; Pose extij := [n2](EXT k2 | (akn i n2 k k2) & (ak k2 i j)).
Step Hxn1: (n2 : nat) (leq n1 n2) -> (extij n2).
  Move=> n2 Hn12; Case: (Hclassical (extij n2)) => // [Nk2]; Case: HSj.
  Exists n2; [By Apply: leq_trans Hn12 | Move=> j' k' [Ekk' Hk'] Hk'j'].
  Rewrite: ltn_neqAle andbC (Hn1 j' k') //;
    RightBy Split; RightBy Apply (leq_partial_coloring Hn12).
  Apply/eqP=> [Dj']; Rewrite: -Dj' in Hk'j'.
  By Case Nk2; Exists k'; LeftBy Split.
Case: (Hxn1 ? (leqnn n1)) {HSj} => [k1 Hk1 Ek1i].
Case: Hk1 [j'](Hn1 j' ? Hk1) => [Ekk1 Hk1] Hk1i.
Step [Hm0i Hm0j]: (inm0 i) /\ (inm0 j).
  Case: Hk1 => [[Hk1 Hm0k1 _ _] _].
  By Move: (proper_inmap_l Hk1 Ek1i)(proper_inmap_r Hk1 Ek1i); Split; Apply: Hm0k1.
Pose k2 := (partial_map (S i) k1); Def: HSi := (ltnSn i); Def: HSi' := (leqnSn i).
Step Ek2i: (ak k2 i j) By Split; Auto.
Step Ekk2: (partial_eq i k k2).
  Exact (partial_eq_trans Ekk1 (leq_partial_eq HSi' (partial_eq_partial ? ?))).
Step Hk2: (quasi_coloring k2) By Apply: quasi_coloring_partial; Case Hk1.
Exists k2; Do 2 Split; Auto; Try By Move=> z; Case.
    Move=> j' k' Ek2k' Hk' Ek'i; Exists j; RightBy Apply (map_sym Hk2).
    Case: Hk' => [Hk' Hk'i Xk']; Case: (Xk' n1) => [k'' Hk'' Ek''].
    Apply: (Hn1 ? k'').
      Split; Auto; Apply: (partial_eq_trans Ekk2); Apply: (partial_eq_trans Ek2k').
      By Apply (leq_partial_eq HSi').
    Case: Ek'' => [H _]; Apply: H {H}; Split; Auto; LeftBy Apply (map_sym Hk').
    Apply Hk'i; Exact (proper_inmap_l Hk' Ek'i).
  Elim: {-2}i (leqnn i) Hkm => //= [i1 Hrec] Hi1 [Hki1 Hkm].
  Split; RightBy Apply: Hrec Hkm; Apply ltnW.
  Move=> j' k' Ek' Hk' Hk'j'.
  Step Ekk': (partial_eq i1 k k').
    By Apply: (!partial_eq_trans) Ek'; Apply (leq_partial_eq (ltnW Hi1)).
  Case: {Hki1}(Hki1 j' k' Ekk' Hk' Hk'j') => [j1 Hj1j' Ekj1].
  Exists j1; LeftDone; Case: Ekk2 => [H _]; Apply: H {H}.
  Step [Hkj' Hki1]: (in_partial i (std_point j1)) /\ (in_partial i (std_point i1)).
    By Move: (proper_inmap_l Hk Ekj1) (proper_inmap_r Hk Ekj1); Split; Apply Hkn.
  By Split.
Move=> n; Step [n' Hn1n' Hnn']: (EX n' | (leq n1 n') & (leq n n')).
  By Case (leqP n1 n); [Exists n | Exists n1]; Rewrite: ?leqnn // ltnW.
Case: (Hxn1 ? Hn1n') => [k' [Ekk' Hk'] Ek'i]; Exists k'.
  By Apply (leq_partial_coloring Hnn').
Apply: (partial_eq_trans (partial_eq_sym (partial_eq_partial ? ?))).
Case: (partial_eq_trans (partial_eq_sym Ekk1) Ekk') => [Hk1k' Hk'k1].
Move: {Hk'}(leq_partial_coloring Hn1n' Hk') => Hk'.
Pose kij := [k](and3 (partial_coloring (S i) k) (ak k i j)
                     (j' : nat)(ak k i j') -> (leq j j')).
Move/leq_partial_coloring: Hin1 => Hin1.
Step Hk1ij: (kij k1) By Split; Auto.
Step Hk'ij: (kij k') By Split; Auto; Move=> j'; Apply Hn1; Split.
Clear: Hkm Hk Hkn Hn1 Hxn1 Ekk1 k2 Ek2i Ekk2 Hk2 n n' Hn1n' Hnn' Ekk'.
Clear: k akn akm akx extij n1 Hin1 Hk1 Hk' Ek'i Ek1i Hk1i.
Cut (k1, k2 : map) (kij k1) -> (kij k2) ->
   (covers (partial_map i k1) k2) -> (covers (partial_map (S i) k1) k2).
  Split; Auto.
Clear: k1 k' Hk1k' Hk'k1 Hk1ij Hk'ij.
Move=> k k' [[Hk Hik] Eki Hki] [[Hk' Hik'] Ek'i _] Ekk'.  
Pose zi := (std_point i); Pose zj := (std_point j).
Pose a0i := [z](partial_map (S i) m0 zi z).
Step Vm0': (z : point) (in_partial (S i) z) -> (in_partial i z) \/ (a0i z).
  Move=> z Hz; Case: {}Hz => [j']; Rewrite: ltnS leq_eqVlt.
  Case/setU1P=> [Dj' | Hj']; RightBy Left; Exists j'.
  By Rewrite Dj'; Right; Split; Auto; [Apply: (map_sym Hm0) | Apply: Hinm0].
Step Hm0'i: (in_partial (S i) zi) By Exists i.
Step Hizi: (z : point) (in_partial i z) -> (k zi z) -> (k' zi z).
  Move=> z Hz Hziz; Apply: (map_trans Hk' Ek'i); Apply Ekk'; Split; Auto.
    By Apply: (map_trans Hk (map_sym Hk Eki)).
  Apply: Hinm0; Auto; Case: {}Hz => [j' Hj' Hzj']; Apply: leq_trans {}Hj'.
  Apply: Hki; Apply: (map_trans Hk Hziz); Apply Hik.
  Move: (proper_inmap_r Hm0 Hzj') (leq_partial HSi'); Split; Auto.
Step Ha0i: (z,z': ?) (a0i z) -> ((k zi z') -> (k' zi z')) -> (k z z') -> (k' z z').
  Move=> z z' Hz Hziz' Hzz'; Apply (map_trans Hk') with zi.
    By Apply (map_sym Hk'); Apply Hik'.
  By Apply Hziz'; Apply: (map_trans Hk) Hzz'; Apply Hik.
Move=> z1 z2 [Hz12 Hz1 Hz2]; Case: (Vm0' ? Hz1) => [Hz1'].
  Apply (map_sym Hk'); Move/(map_sym Hk 5!?): Hz12 => Hz12.
  By Case: (Vm0' ? Hz2) => [Hz2']; EAuto; Apply Ekk'; Split.
By Apply: Ha0i Hz12 => // [Hz12]; Case: (Vm0' ? Hz2) => [Hz2']; Auto; Apply Hik'.
Qed.

Lemma leq_exact_partial : (n1, n2 : nat) (leq n1 n2) ->
  (k1, k2 : map) (exact_partial n1 k1) -> (exact_partial n2 k2) -> (covers k1 k2).
Proof.
Move=> n1 n2 Hn12 k1 k2 [Mk1 Xk1] [Mk2 Xk2]; Cut (partial_eq n1 k1 k2).
  Move: Xk1 {Mk1 Xk2 Mk2} => [Hk1 Hk1n1 _] [Hk12 _] z1 z2 Hz12; Apply Hk12.
  Move: (proper_inmap_l Hk1 Hz12) (proper_inmap_r Hk1 Hz12); Split; Auto.
Step Mk21: (min_partial n1 k2) By Elim: (leP Hn12) Mk2 => //= [n _ H]; Case; Auto.
Elim: {-2}n1 (leqnn n1) Mk1 Mk21 {Mk2} => /= [|i Hrec] Hin1.
  By Split; Move=> z1 z2 [_ [j Hj _] _].
Move=> [Hk1i Mk1] [Hk2i Mk2]; Move: {Hn12}(leq_trans Hin1 Hn12) => Hin2.
Move: {Hrec Mk1 Mk2}(Hrec (ltnW Hin1) Mk1 Mk2) => Ek12.
Def: Ek21 := (partial_eq_sym Ek12).
Move: (partial_eq_partial (S i) k1) (partial_eq_partial (S i) k2).
Move: {Hin1}(leq_extensible Hin1 Xk1) {Hin2}(leq_extensible Hin2 Xk2).
Pose zi := (std_point i); Pose aSi := (partial_map (S i)).
Case: Xk1 Xk2 => [Hk1 _ _] [Hk2 _ _] Xk1 Xk2 Ek1 Ek2.
Apply: (partial_eq_trans Ek1 (partial_eq_trans ? (partial_eq_sym Ek2))).
Def: Ek12' := (partial_eq_trans Ek12 (leq_partial_eq (leqnSn i) Ek2)).
Def: Ek21' := (partial_eq_trans Ek21 (leq_partial_eq (leqnSn i) Ek1)).
Pose ak := [k : map; j1, j2](k (std_point j1) (std_point j2)).
Pose minki := [k, k'](j' : nat)(ak k' j' i) -> (EX j | (leq j j') & (ak k j i)).
Step Hminki : (k, k' : map) (partial_eq i k k') -> (extensible (S i) k') ->
         (quasi_coloring k) -> (min_partial1 i k) -> (minki (aSi k) k').
  Move=> k k' Ekk' Hk' Hk Hki j' Hj'i.
  Step [Hj' Hi]: (in_partial (S i) (std_point j')) /\ (in_partial (S i) zi).
    Move: Hk' => [Hk' Ek' _].
    By Move: (proper_inmap_l Hk' Hj'i) (proper_inmap_r Hk' Hj'i); Split; Apply Ek'.
  Step [j1 [Hj1 Hj1j' Hj1i]]: (EX j1 | (and3 (leq j1 i) (leq j1 j') (ak k' j1 i))).
    Case: (leqP j' i) => [Hij']; LeftBy Exists j'; Split; Try Apply leqnn.
    Move/extensible_partial: Hk' => [Hk' Hik'].
    Case: {}Hj' => [j1 Hj1 Hj1j']; Exists j1; Split; Auto.
      Apply ltnW; EApply leq_trans; EAuto.
    Apply: (map_trans Hk') Hj'i; Apply (map_sym Hk'); Apply Hik'; Split; Auto.
    By Exists j1; RightBy Exact (proper_inmap_r Hm0 Hj1j').
  Case: {Hki Ekk' Hk' Hj' Hj'i Hj1i}(Hki ? ? Ekk' Hk' Hj1i) => [j Hj Hji].
  Exists j; LeftBy EApply leq_trans; EAuto.
  Split; Auto; Exists j; LeftBy Apply leq_trans with (S j1).
  Apply (qc_inmap Hk); Exact (proper_inmap_l Hk Hji).
Step Hk1i': (minki (aSi k1) (aSi k2)) By Auto.
Step Hk2i': (minki (aSi k2) (aSi k1)) By Auto.
Move/extensible_partial: Xk2 Hk2i' {Hminki}; Move/extensible_partial: Xk1 Hk1i'.
Move: (partial_eq_trans (partial_eq_sym Ek12') (partial_eq_trans Ek12 Ek21')).
Move/aSi: k2 {n1 n2 Hk1i Hk2i Hk1 Hk2 Ek1 Ek2 Ek12' Ek21' Ek12 Ek21}; Move/aSi: k1.
Cut (k1, k2 : map) (partial_coloring (S i) k1) -> (minki k1 k2) -> 
                   (partial_coloring (S i) k2) -> (minki k2 k1) -> 
   (covers (partial_map i k1) k2) -> (covers (aSi k1) k2).
  By Move=> Xi k1 k2; Case; Split; Apply Xi.
Move=> k1 k2 [Hk1 Hik1] Hk21i [Hk2 Hik2] Hk12i Hk12.
Step Hk1zi: (z : point) (in_partial i z) -> (k1 z zi) -> (k2 z zi).
  Move=> z Hz Hzzi; Case: {}Hz => [j Hj]; Pose zj := (std_point j); Move=> Hzzj.
  Step Hzj: (in_partial i zj) By Exists j; RightBy Exact (proper_inmap_r Hm0 Hzzj).
  Step Hzj': (aSi m0 z zj) By Split; Auto; Apply (leq_partial (leqnSn i)).
  Move: {Hz Hzzj Hzzi}(map_trans Hk1 (map_sym Hk1 (Hik1 ? ? Hzj')) Hzzi) => Hzji.
  Apply: (map_trans Hk2 (Hik2 ? ? Hzj')) {Hzj'}.
  Step [j' [Hj' Hj'1 Hj'2]]: (EX j' | (and3 (ltn j' i) (ak k1 j' i) (ak k2 j' i))).
    Move: {Hzj}Hzji; Rewrite: ~/zj; Elim: {1 2}i j Hj => //= [i' Hrec] j0 Hi' Hj0.
    Case: (Hk12i ? Hj0) => [j1 Hj10 Hj1]; Case: (Hk21i ? Hj1) => [j2 Hj21 Hj2].
    Rewrite: leq_eqVlt in Hj21; Case/setU1P: Hj21 => [Dj2 | Hj21].
      By Rewrite: Dj2 in Hj2; Exists j1; Split; Auto; Apply: leq_trans Hi'.
    Step Hj2': (ltn j2 i').
      By Rewrite ltnS in Hi'; Apply: leq_trans (leq_trans Hj10 Hi').
    Case: (Hrec ? Hj2' Hj2) => [j' [Hj' Hj'1 Hj'2]].
    By Move: (ltnW Hj'); Exists j'; Split.
  Apply: (map_trans Hk2) Hj'2; Apply: Hk12; Split; Auto.
    By Apply: (map_trans Hk1) (map_sym Hk1 Hj'1).
  Exists j'; Auto; Move: Hk1 => [Hk1 Hm0k1 _ _]; Apply: Hm0k1.
  Exact (proper_inmap_l Hk1 Hj'1).
Step Vm0 : (z : point) (in_partial (S i) z) -> (in_partial i z) \/ (aSi m0 zi z).
  Move=> z Hz; Case: {}Hz => [j']; Rewrite: ltnS leq_eqVlt.
  Case/setU1P=> [Dj' | Hj']; RightBy Left; Exists j'.
  Rewrite Dj'; Move=> Hiz; Right; Split; Auto; LeftBy Apply: (map_sym Hm0).
  Exists i; [Apply leqnn | Exact (proper_inmap_r Hm0 Hiz)].
Move=> z1 z2 [Hz12 Hz1 Hz2]; Case/(Vm0 ?): Hz1 => [Hz1].
  Case/(Vm0 ?): Hz2 => [Hz2]; LeftBy Apply Hk12; Split.
  Apply: (map_trans Hk2) (Hik2 ? ? Hz2); Apply: Hk1zi => //.
  By Apply: (map_trans Hk1) (map_sym Hk1 (Hik1 ? ? Hz2)).
Apply (map_sym Hk2); Apply: (map_trans Hk2) (Hik2 ? ? Hz1).
Move: {z1 Hz12 Hz1}(map_sym Hk1 (map_trans Hk1 (Hik1 ? ? Hz1) Hz12)) => Hz2i.
By Case/(Vm0 ?): Hz2 => [Hz2]; Auto; Apply (map_sym Hk2); Apply Hik2.
Qed.

Definition limit_coloring : map :=
  [z1, z2](EXT k | (k z1 z2) & (EX n | (exact_partial n k))).

Lemma limit_coloring_coloring : (coloring m0 limit_coloring).
Proof.
Split.
 Split; Move=> z1 z2 [k Hz12 [n Hk]].
    By Exists k; [Case: Hk => [_ [Hk _ _]]; Apply (map_sym Hk) | Exists n].
  Move=> z3 [k3 Hz23 [n3 Hk3]].
  Step [k' [Hz12' Hz23' [n' Hk']]]:
    (EXT k' | (and3 (k' z1 z2) (k' z2 z3) (EX n' | (exact_partial n' k')))).
    Case: (leqP n n3) => [Hnn3].
      Exists k3; Split; Auto; RightBy Exists n3.
      By Apply: ((leq_exact_partial Hnn3) k k3).
    Exists k; Split; Auto; RightBy Exists n.
    By Apply: ((leq_exact_partial (ltnW Hnn3)) k3 k).
  Exists k'; RightBy Exists n'.
  By Case: Hk' => [_ [Hk' _ _]]; Apply (map_trans Hk' Hz12').
 By Move=> z [k Hz [n [_ [[_ Hk _ _] _ _]]]]; Auto.
 Move=> z1 z2 Hz12; Move: (has_std_point (proper_inmap_l Hm0 Hz12)) => [i1 Hiz1].
  Move: (has_std_point (proper_inmap_r Hm0 Hz12)) => [i2 Hiz2].
  Step [n Hni1 Hni2]: (EX n | (ltn i1 n) & (ltn i2 n)).
    By Case (leqP i1 i2); [Exists (S i2) | Exists (S i1)]; Rewrite: ?leqnn // ltnW.
  Case: (exists_exact_partial n) => [k Hk]; Exists k; RightBy Exists n.
  Move: Hk => [_]; Case/extensible_partial=> [Hk Hnk].
  By Apply: Hnk; Split; [Done | Exists i1 | Exists i2].
By Move=> z1 z2 [k Hz12 [n [_ [[_ _ _ Hka] _ _]]]]; Auto.
Qed.

Lemma size_limit_coloring : (size_at_most nc limit_coloring).
Proof.
Pose inmf := [n; k; f](i : nat) (ltn i n) -> (inmap k (f i)::point).
Pose injf := [n; k : map; f](i, j: nat) (ltn i j) -> (ltn j n) -> ~(k (f i) (f j)).
Pose minsize := [n; k](EXT f | (inmf n k f) & (injf n k f)).
Case: (Hclassical (minsize (S nc) limit_coloring)).
  Move=> [f Hf If].
  Step [k Hfk Hk]: (EXT k | (inmf (S nc) k f) & (EX n | (exact_partial n k))).
    Elim: {-2}(S nc) (ltnSn nc) => [|n Hrec] Hn.
      By Case: (exists_exact_partial (0)) => [k Hk]; Exists k; [Move | Exists (0)].
    Case: (Hrec (ltnW Hn)) => [k1 Hk1f [n1 Hk1]].
    Case: (Hf ? Hn) => [k2 Hk2f [n2 Hk2]]; Case: (ltnP n2 n1) => [Hn12].
      Exists k1; RightBy Exists n1.
      Move=> i; Rewrite: ltnS leq_eqVlt; Case/setU1P=> [Di | Hi]; Auto.
      By Rewrite Di; Apply: ((leq_exact_partial (ltnW Hn12)) k2 k1).
    Exists k2; RightBy Exists n2.
    Move=> i; Rewrite: ltnS leq_eqVlt; Case/setU1P; LeftBy Case/esym.
    By Move/(Hk1f ?); Apply: ((leq_exact_partial Hn12) k1 k2).
  Case: {}Hk {Hf} => [nk [_ [[Hk' _ [f' Hf'] _] _ _]]].
  Step [s Ls Ds]: (EX s | (size s) = (S nc) & (i : nat) (ltn i (S nc)) ->
                        let j = (sub (0) s i) in (ltn j nc) /\ (k (f' j) (f i))).
    Elim: (S nc) f Hfk {If} => [|n Hrec] f Hf; LeftBy Exists (seq0::natseq).
    Case: {Hrec}(Hrec [i](f (S i))); LeftBy Move=> i Hi; Apply: Hf.
    Move=> s Ls Hs; Case: (Hf' (f (0))); LeftBy Apply Hf.
    Move=> j Hjnc Hjf'; Exists (Seq j & s); LeftBy Rewrite: /= Ls.
    By Move=> [|i]; [Split; LeftBy Apply/ltP | Apply: Hs].
  Clear: Hfk Hf'; Step Us: (uniq s).
    Rewrite: -{s}take_size; Move: (leqnn (size s)).
    Elim: {-2}(size s) => [|n Hrec] Hn; LeftBy Rewrite: take0.
    Rewrite: (take_sub (0) Hn) uniq_add_last ~Hrec 1?ltnW // andbT.
    Apply/(subPx (0) ? ?); Rewrite: size_take Hn; Move=> [i Hi Ei].
    Rewrite: Ls in Hn; Case: (If ? ? Hi Hn); Exists k; Auto.
    Case: (Ds ? Hn) => [_]; Rewrite: -Ei sub_take //; Apply: (map_trans Hk').
    By Apply (map_sym Hk'); Case: (Ds ? (ltn_trans Hi Hn)).
  Step [s' Ls' Ds']: (EX s' | (size s') = nc & s' =1 [i](ltn i nc)).
    Exists (traject S (0) nc); LeftBy Rewrite size_traject.
    Step EitS: (i : nat) (iter i S (0)) = i By Elim=> //= *; Congr S.
    By Move=> i; Apply/trajectP/idP=> [[i' Hi' []] | ]; [Rewrite EitS | Exists i].
  Case/idP: (ltnn nc); Rewrite: -Ls -Ls'; Apply: uniq_leq_size => // [i].
  Rewrite: Ds'; Move/(subPx (0) ? ?)=> [j Hj []] {i}; Rewrite Ls in Hj.
  By Case: (Ds ? Hj).
Def: k := limit_coloring; Elim: {}nc => [|n Hrec] Hn.
  Exists [i : nat](std_point (0)); Move=> z Hz; Case Hn.
  By Exists [i : nat]z; Move=> i; Case.
Case: (Hclassical (minsize (S n) k)).
  Move{Hrec}=> [f Hf Ij]; Exists f; Move=> z Hz.
  Case (Hclassical (EX i | (lt i (S n)) & (k (f i) z))); Auto.
  Move=> Hfz; Case Hn; Exists [i](if (ltn i (S n)) then (f i) else z).
    Move=> i _; Case Hi: (ltn i (S n)); Auto.
  Move=> j i Hj Hi; Rewrite ltnS in Hi; Rewrite: (leq_trans Hj Hi).
  Case: (ltnP i (S n)); Auto; Rewrite: leq_eqVlt ltnNge Hi orbF; Move/eqP=> Di Hjz.
  By Case: Hfz; Exists j; LeftBy Apply: ltP; Rewrite Di.
Case/Hrec {Hrec Hn} => [f Hf]; Exists f; Move=> z; Move/(Hf z)=> [i Hi Hz].
By Exists i; LeftBy Right.
Qed.

Lemma compactness_extension : (map_colorable nc m0).
Proof. 
By Move: {}limit_coloring_coloring  {}size_limit_coloring; Exists limit_coloring.
Qed.

End FinitizeMap.

Unset Implicit Arguments.


