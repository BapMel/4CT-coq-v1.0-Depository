(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require tacticext.
Require boolprop.
Require funs.
Require dataset.
Require natprop.
Require seq.
Require paths.
Require finset.

Set Implicit Arguments.

(* Decidable connectivity in finite sets, with an application to the orbits *)
(* and inverses of injective functions.                                     *)

Section Connect.

Variables d : finSet; e : (rel d).

Fixpoint dfs [n : nat] : (seq d) -> d -> (seq d) :=
  [a; x]if n is (S n') then
    if (a x) then a else (foldl (dfs n') (Adds x a) (filter (e x) (enum d)))
  else a.

Definition connect : d -> (set d) := (dfs (card d) seq0).

Lemma subset_dfs : (n : nat; a, b : (seq d))
  (subset a (foldl (dfs n) a b)).
Proof.
Def: Hs := (!subset_refl d); Elim=> [|n Hrec] a b; LeftBy Elim: b.
Elim: b a => [|x b Hrecb] a //; Apply: (subset_trans ? (Hrecb ?)).
Simpl; Case (a x); LeftDone; Apply: (subset_trans ? (Hrec ? ?)).
By Apply/subsetP => [y Ht]; Apply/orP; Right.
Qed.

Inductive dfs_path [x, y : d; a : (seq d)] : Prop :=
  DfsPath : (p : (seq d))
    (path e x p) -> (last x p) = y -> (disjoint (Adds x p) a) -> (dfs_path x y a).

Lemma dfsP : (n : nat; x, y : d; a : (seq d))
            (leq (card d) (addn (card a) n)) -> (negb (a y)) ->
  (reflect (dfs_path x y a) (dfs n a x y)).
Proof.
Elim=> [|n Hrec] x y a Hn Hy.
  Case/idPn: (max_card (setU1 y a)).
  By Rewrite: -ltnNge cardU1 (negbE Hy) /= addSn addnC.
Simpl; Case Hx: (a x).
  Rewrite (negbE Hy); Right; Move=> [p Hp Ep Hpa].
  By Case/idP: (set0P Hpa x); Rewrite: /setI /= setU11.
Def Da': a' := (Adds x a); Case Hya': (a' y).
  Rewrite [b](subsetP (subset_dfs n ? b) ? Hya'); Left.
  Exists (Seq0 d); Repeat Split; RightBy Rewrite: disjoint_has /= Hx.
  By Rewrite: Da' /= in Hya'; Case/setU1P: Hya'; RightBy Rewrite (negbE Hy).
Step Hna': (leq (card d) (addn (card a') n)).
  By Rewrite: Da' /= cardU1 Hx /= add1n addSnnS.
Def Db: b := (filter (e x) (enum d)).
Cut (reflect (EX x' | (b x') & (dfs_path x' y a')) (foldl (dfs n) a' b y)).
  Move=> H; Apply (iffP H); Clear H Hrec.
    Move=> [x' Hx' [p Hp Ep Hpa]]; Rewrite: Db filter_enum in Hx'.
    Rewrite: Da' /= disjoint_sym disjointU1 in Hpa; Case/andP: Hpa => [Hpx Hpa].
    Exists (Adds x' p); Repeat Split; Rewrite: /= ?Hx' //.
    By Rewrite: disjointU1 Hx disjoint_sym.
  Move=> [p Hp Ep Hpa].
  Case/shortenP: Hp Ep => [[|y' p'] Hp' Up' Hp'p] /= Dy.
    By Rewrite: Da' Dy /= setU11 in Hya'.
  Simpl in Hp' Up'; Case/andP: Hp' => [Hxy' Hp']; Case/andP: Up' => [Hp'x' _].
  Exists y'; [By Rewrite: Db filter_enum | Exists p'; Auto].
  Rewrite: disjoint_sym Da' /= disjointU1 Hp'x' /= disjoint_sym.
  Apply: disjoint_trans Hpa; Apply/subsetP=> [z Hz]; Apply: setU1r; Auto.
Elim: b a' Hya' Hna' {a x Da' Db Hy Hn Hx} => [|x b Hrecb] a Hy Hn; Simpl.
  By Rewrite Hy; Right; Case.
Def: Ha := (subset_dfs n a (seq1 x)); Simpl in Ha.
Case Hdfs_y: (dfs n a x y).
  Rewrite (subsetP (subset_dfs n ? b) ? Hdfs_y); Left.
  Exists x; [Apply setU11 | Apply: (Hrec ?); Auto; Exact (negbI Hy)].
Def: Hca := (subset_leq_card Ha); Rewrite: -(leq_add2r n) in Hca.
Apply: (iffP (Hrecb ? Hdfs_y (leq_trans Hn Hca))) {Hrecb Hca}.
  Move=> [x' Hx' [p Hp Ep Hpa]]; Rewrite disjoint_sym in Hpa.
  Exists x'; [By Apply setU1r | Exists p; Try Split; Try Done].
  Rewrite disjoint_sym; Exact (disjoint_trans Ha Hpa).
Move=> [x' Hx' [p Hp Ep Hpa]].
Case Hpa': (disjoint (Adds x' p) (dfs n a x)).
  Case/orP: Hx' => [Dx' | Hx']; RightBy Exists x'; Auto; Exists p.
  Move: (set0P Hpa x') => Hax'; Rewrite: /setI /= setU11 /= in Hax'.
  Case/idP: (set0P Hpa' x'); Rewrite: /setI /= setU11 /=.
  Apply/(Hrec ? ? ? Hn (negbI Hax')).
  Exists (Seq0 d); Auto; LeftBy Apply: eqP.
  By Rewrite: disjoint_has /= (eqP Dx') Hax'.
Case/(Hrec ? ? ? Hn (negbI Hy)): Hdfs_y.
Case/set0Pn: Hpa' => [x'' H]; Case/andP: H => [Hpx'' Hdfs_x''].
Def: Hax'' := (set0P Hpa x''); Rewrite: /setI Hpx'' /= in Hax''.
Case/(Hrec ? ? ? Hn (negbI Hax'')): Hdfs_x'' => [q Hq Eq Hqa].
Case/splitPl: {p Hpa'}Hpx'' Hp Ep Hpa => [p1 p2 Ep1].
Rewrite: path_cat -cat_adds disjoint_cat last_cat Ep1.
Case/andP => [Hp1 Hp2] Ep2; Case/andP => [Hp1a Hp2a]; Exists (cat q p2).
    By Rewrite: path_cat Hq Eq.
  By Rewrite: last_cat Eq.
By Rewrite: -cat_adds disjoint_cat Hqa.
Qed.

Lemma connectPx : (x, y : d)
  (reflect (EX p | (path e x p) & (last x p) = y) (connect x y)).
Proof.
Move=> x y; Apply: (iffP (dfsP x 4!seq0 ? ?)); Trivial.
    Rewrite: /= card0; Exact (leqnn ?).
  By Move=> [p Hp Ep _]; Exists p.
By Move=> [p Hp Ep]; Exists p; Try Rewrite: disjoint_has has_sym.
Qed.

Syntactic Definition connectP := connectPx | 2.

Lemma connect_trans : (x1, x2: d) (connect x1 x2) ->
  (sub_set (connect x2) (connect x1)).
Proof.
Move=> x1 x2; Case/connectP => [p1 Hp1 Ep1] x3; Case/connectP => [p2 Hp2 Ep2].
By Apply/connectP; Exists (cat p1 p2); Rewrite: ?path_cat ?Hp1 ?last_cat Ep1.
Qed.

Lemma connect0 : (x : d) (connect x x).
Proof. By Move=> x; Apply/connectP; Exists (Seq0 d). Qed.

Lemma eq_connect0 : (x, y: d) x = y -> (connect x y).
Proof. Move=> x y []; Apply connect0. Qed.

Lemma connect1 : (x, y : d) (e x y) -> (connect x y).
Proof. By Move=> x y Hxy; Apply/connectP; Exists (seq1 y); Rewrite: /= ?Hxy. Qed.

Lemma path_connect : (x : d; p : (seq d)) (path e x p) ->
   (sub_set (Adds x p) (connect x)).
Proof.
Move=> x p Hp x' Hx'; Apply/connectP; Case/splitPl: p / Hx' Hp => [p p' Ep].
By Rewrite: path_cat; Case/andP; Exists p.
Qed.

Definition root [x : d] : d := if pick y in (connect x) then y else x.

Definition roots : (set d) := [x] (root x) =d x.

Definition n_comp [a : (set d)] : nat := (card (setI roots a)).

Lemma connect_root : (x : d) (connect x (root x)).
Proof.
By Move=> x; Rewrite: /root; Case: (pickP (connect x)); Rewrite: // connect0.
Qed.

Definition connect_sym : Prop := (x, y : d) (connect x y) = (connect y x).
Hypothesis He : connect_sym.

Lemma same_connect : (x, y : d) (connect x y) -> (connect x) =1 (connect y).
Proof.
By Move=> x y Hxy z; Apply/idP/idP; Apply: (!connect_trans); Rewrite: // He.
Qed.

Lemma same_connect_r : (x, y : d) (connect x y) ->
  (z : d) (connect z x) = (connect z y).
Proof. By Move=> x y Hxy z; Rewrite: !(He z); Apply same_connect. Qed.

Lemma rootPx : (x, y : d) (reflect (root x) = (root y) (connect x y)).
Proof.
Move=> x y; Apply introP; Move=> Hxy.
  Rewrite: /root -(eq_pick (same_connect Hxy)).
  By Case: (pickP (connect x)) => [H | Hx] //; Case/idP: (Hx y).
Intro Hr; Case/idP: Hxy; Apply: (connect_trans (connect_root x)).
Rewrite: Hr He; Apply connect_root.
Qed.

Lemma root_root : (x : d) (root (root x)) = (root x).
Proof. Symmetry; Apply: rootPx; Apply connect_root. Qed.

Lemma roots_root : (x : d) (roots (root x)).
Proof. Move=> *; Apply/eqP; Apply root_root. Qed.

Lemma eqd_root : (x, y : d) ((root x) =d (root y)) = (connect x y).
Proof. Move=> *; Exact (sameP eqP (rootPx ? ?)). Qed.

End Connect.

Syntactic Definition connectP := connectPx | 3.
Syntactic Definition rootP := [Hsym](rootPx Hsym ? ?).

Section EqConnect.

Variable d : finSet.

Lemma connect_sub : (e, e' : (rel d)) 
   (sub_rel e (connect e')) -> (sub_rel (connect e) (connect e')).
Proof.
Move=> e e' He x y; Case/connectP => [p Hp []] {y}.
Elim: p x Hp => [|y p Hrec] x; [Exact [_](connect0 e' x) | Simpl].
Case/andP => [Hx Hp]; Exact (connect_trans (He ? ? Hx) (Hrec ? Hp)).
Qed.

Lemma relU_sym : (e, e' : (rel d))
  (connect_sym e) -> (connect_sym e') -> (connect_sym (relU e e')).
Proof.
Move=> e e' He He'.
Cut (x, y : d) (connect (relU e e') x y) -> (connect (relU e e') y x).
  Move=> H x y; Apply/idP/idP; Auto.
Move=> x y; Case/connectP => [p Hp []] {y}.
Elim: p x Hp => [|y p Hrec] x /=; LeftBy Rewrite connect0.
Case/andP => [Hxp Hp]; Apply: (connect_trans (Hrec ? Hp)) {Hrec Hp}.
Case/orP: Hxp; Move/(!connect1 d ? ? ?); Rewrite: 1?He 1?He'; Move: y x;
 Apply: connect_sub => [x y Hy]; Apply connect1; Apply/orP; Auto.
Qed.

Lemma eq_connect : (e, e' : (rel d)) e =2 e' -> (connect e) =2 (connect e').
Proof.
By Move=> e e' Ee x y; Apply/connectP/connectP;
  Move=> [p Hp Ep]; Exists p; Move: Hp; Rewrite: // (eq_path Ee).
Qed.

Lemma eq_n_comp : (e, e' : (rel d))
  (connect e) =2 (connect e') -> (n_comp e) =1 (n_comp e').
Proof. 
Move=> e e' Hee' a; Apply: eq_card => [x].
By Rewrite: /setI /roots /root (eq_pick (Hee' x)).
Qed.

Lemma eq_n_comp_r : (a, a' : (set d))
  a =1 a' -> (e : (rel d)) (n_comp e a) = (n_comp e a').
Proof. By Move=> a a' Ha e; Apply: eq_card => [x]; Rewrite: /setI Ha. Qed.

Lemma n_compC : (a : (set d); e : (rel d))
  (n_comp e d) = (addn (n_comp e a) (n_comp e (setC a))).
Proof.
Move=> a e; Rewrite: /n_comp cardIC.
By Apply: eq_card => [x]; Rewrite: /setI andbT.
Qed.

End EqConnect.

Section Closure.

Variables d : finSet;  e : (rel d).
Hypothesis He : (connect_sym e).

Lemma same_connect_rev : (connect e) =2 (connect [x,y](e y x)).
Proof.
Cut (e' : (rel d)) (sub_rel (connect [x,y](e' y x)) [x,y](connect e' y x)).
  Move=> Hrev x y; Rewrite He; Apply/idP/idP => [Hyx | Hxy]; Apply: Hrev; Auto.
Move=> e' x y; Move/connectP => [p Hp []] {y}.
Elim: p x Hp => [|y p Hrec] x /=; LeftBy Rewrite connect0.
Move/andP => [Hyx Hp]; Exact (connect_trans (Hrec ? Hp) (connect1 Hyx)).
Qed.

Definition closed [a : (set d)] : Prop :=
  (x, y : d) (e x y) -> (a x) = (a y).

Lemma intro_closed : (a : (set d))
  ((x, y : d) (e x y) -> (a x) -> (a y)) -> (closed a).
Proof.
Move=> a Ha x y Hxy; Apply/idP/idP; LeftBy Apply: Ha.
Move/connectP: {Hxy}(etrans (He ? ?) (connect1 Hxy)) => [p Hp [ ]].
By Elim: p y Hp => [|z p Hrec] y //=; Move/andP => [Hxp Hp]; EAuto.
Qed.

Lemma closed_connect : (a : (set d))
  (closed a) -> (x, y : d) (connect e x y) -> (a x) = (a y).
Proof.
Move=> a Ha x y; Move/connectP => [p Hp []] {y}.
Elim: p x {y} Hp => [|y p Hrec] x //=; Move/andP => [Hxp Hp].
Rewrite: (Ha ? ? Hxp); Auto.
Qed.

Lemma connect_closed : (x : d) (closed (connect e x)).
Proof. By Move=> x y z Hyz; Apply (same_connect_r He); Apply connect1. Qed.

Lemma setC_closed : (a : (set d)) (closed a) -> (closed (setC a)).
Proof. By Move=> a Ha x y Hxy; Rewrite: /setC (Ha x y Hxy). Qed.

Definition closure [a : (set d)] : (set d) :=
   [x](negb (disjoint (connect e x) a)).

Lemma closure_closed : (a : (set d)) (closed (closure a)).
Proof.
Move=> a; Apply intro_closed; Move=> x y Hxy.
By Rewrite: /closure (eq_disjoint (same_connect He (connect1 Hxy))).
Qed.

Lemma subset_closure : (a : (set d)) (subset a (closure a)).
Proof.
Move=> a; Apply/subsetP=> [x Hx].
By Apply/set0Pn; Exists x; Rewrite: /setI connect0.
Qed.

Lemma n_comp_closure2 : (x, y : d)
  (n_comp e (closure (set2 x y))) = (S (negb (connect e x y))).
Proof.
Move=> x y; Rewrite: -(eqd_root He) -card2.
Apply: eq_card => [z]; Apply/idP/idP.
  Case/andP; Move=> Hrz; Case/set0Pn; Move=> z'.
  Move/andP => [Hzz' Hxyz']; Rewrite: -(eqP Hrz) (rootP He Hzz').
  By Case: (orP Hxyz'); Move/eqP=> Dz'; Rewrite: /set2 Dz' set11 ?orbT.
Case/orP; Case/eqP; Rewrite: /setI (roots_root He);
  Apply/set0Pn; [Exists x | Exists y];
  By Rewrite: /setI /set2 set11 ?orbT He connect_root.
Qed.

Lemma n_comp_connect : (x : d) (n_comp e (connect e x)) = (1).
Proof.
Move=> x; Rewrite: -(card1 (root e x)); Apply: eq_card => [y].
Apply/andP/eqP => [[Hy Hxy] | []].
  By Rewrite: (rootP He Hxy) (eqP Hy).
By Rewrite: (roots_root He) connect_root.
Qed.

End Closure.

Grammar constr constr0 : constr :=
  fun_connect ["(" "fconnect" constr9($f) constr9($x) constr9($p) ")"]
      -> [(connect (eqdf $f) $x $p)]
| fun_connect1 ["(" "fconnect" constr9($f) constr9($x) ")"]
      -> [(connect (eqdf $f) $x)]
| fun_connect0 ["(" "fconnect" constr9($f) ")"]
      -> [(connect (eqdf $f))]
| fun_root ["(" "froot" constr9($f) constr9($p) ")"]
      -> [(root (eqdf $f) $p)]
| fun_root0 ["(" "froot" constr9($f) ")"]
      -> [(root (eqdf $f))]
| fun_roots ["(" "froots" constr9($f) constr9($p) ")"]
      -> [(roots (eqdf $f) $p)]
| fun_roots0 ["(" "froots" constr9($f) ")"]
      -> [(roots (eqdf $f))]
| fun_card ["(" "fcard" constr9($f) constr9($p) ")"]
      -> [(n_comp (eqdf $f) $p)]
| fun_card0 ["(" "fcard" constr9($f) ")"]
      -> [(n_comp (eqdf $f))]
| fun_closed ["(" "fclosed" constr9($f) constr9($p) ")"]
      -> [(closed (eqdf $f) $p)]
| fun_closed0 ["(" "fclosed" constr9($f) ")"]
      -> [(closed (eqdf $f))]
| fun_closure ["(" "fclosure" constr9($f) constr9($p) ")"]
      -> [(closure (eqdf $f) $p)]
| fun_closure0 ["(" "fclosure" constr9($f) ")"]
      -> [(closure (eqdf $f))].

Syntax constr
  level 0:
    fun_connect_pp [ (connect (eqdf $f) $x $p) ] -> [(OPFORM fconnect $f $x $p)]
  | fun_connect1_pp [ (connect (eqdf $f) $x) ] ->   [(OPFORM fconnect $f $x)]
  | fun_connect0_pp [ (connect (eqdf $f)) ] ->      [(OPFORM fconnect $f)]
  | fun_root_pp [ (root (eqdf $f) $p) ] ->          [(OPFORM froot $f $p)]
  | fun_root0_pp [ (root (eqdf $f)) ] ->            [(OPFORM froot $f)]
  | fun_roots_pp [ (roots (eqdf $f) $p) ] ->        [(OPFORM froots $f $p)]
  | fun_roots0_pp [ (roots (eqdf $f)) ] ->          [(OPFORM froots $f)]
  | fun_card_pp [ (n_comp (eqdf $f) $p) ] ->        [(OPFORM fcard $f $p)]
  | fun_card0_pp [ (n_comp (eqdf $f)) ] ->          [(OPFORM fcard $f)]
  | fun_closed_pp [ (closed (eqdf $f) $p) ] ->      [(OPFORM fclosed $f $p)]
  | fun_closed0_pp [ (closed (eqdf $f)) ] ->        [(OPFORM fclosed $f)] 
  | fun_closure_pp [ (closure (eqdf $f) $p) ] ->    [(OPFORM fclosure $f $p)]
  | fun_closure0_pp [ (closure (eqdf $f)) ] ->      [(OPFORM fclosure $f)].

Section Orbit.

Variables d : finSet; f : d -> d.

Definition order [x : d] : nat := (card (fconnect f x)).

Definition orbit [x : d] : (seq d) := (traject f x (order x)).

Definition findex [x, y : d] : nat := (index y (orbit x)).

Definition finv [x : d] : d := (iter (pred (order x)) f x).

Lemma fconnect_iter : (n : nat; x : d) (fconnect f x (iter n f x)).
Proof.
Move=> n x; Apply/connectP.
Exists (traject f (f x) n); [Apply fpath_traject | Apply last_traject].
Qed.

Lemma fconnect1 : (x : d) (fconnect f x (f x)).
Proof. Exact (fconnect_iter (1)). Qed.

Lemma fconnect_finv : (x : d) (fconnect f x (finv x)).
Proof. Exact [x](fconnect_iter ? ?). Qed.

Lemma orderSpred : (x : d) (S (pred (order x))) = (order x). 
Proof.  By Move=> x; Rewrite: /order (cardD1 x) connect0. Qed.

Lemma size_orbit : (x : d) (size (orbit x)) = (order x).
Proof. Exact [x](size_traject ? ? ?). Qed.

Lemma looping_order : (x : d) (looping f x (order x)).
Proof.
Move=> x; Apply/idPn => [Ux]; Rewrite: -looping_uniq in Ux.
Case/idP: (ltnn (order x)).
Move: (card_uniqP Ux); Rewrite: size_traject; Case=> [].
Apply: subset_leq_card; Apply/subsetP.
Move=> z; Move/trajectP=> [i _ []]; Apply fconnect_iter.
Qed.

Lemma fconnect_orbit : (x : d) (fconnect f x) =1 (orbit x).
Proof.
Move=> x y; Symmetry; Apply/idP/idP.
  Move/trajectP=> [i _ []]; Apply fconnect_iter.
Move/connectP=> [q' Hq' []]; Move/fpathP: Hq' => [m []] {q'}.
Rewrite: last_traject; Apply: loopingP; Apply looping_order.
Qed.

Lemma uniq_orbit : (x : d) (uniq (orbit x)).
Proof.
Move=> x; Rewrite: /orbit -orderSpred looping_uniq.
Apply/trajectP => [[i Hi Ei]]; Pose n := (pred (order x)); Case/idP: (ltnn n).
Rewrite: {1}/n orderSpred /order -(size_traject f x n).
Apply: (leq_trans (subset_leq_card ?) (card_size ?)); Apply/subsetP => [z].
Rewrite fconnect_orbit; Move/trajectP=> [j Hj []] {z}; Apply/trajectP.
Rewrite: -orderSpred -/n ltnS leq_eqVlt in Hj.
By Case/setU1P: Hj => [Dj | Hj]; [Rewrite Dj; Exists i | Exists j].
Qed.

Lemma findex_max : (x, y : d) (fconnect f x y) -> (ltn (findex x y) (order x)).
Proof. By Move=> x y; Rewrite: fconnect_orbit -index_mem size_orbit. Qed.

Lemma findex_iter : (x : d; i : nat) (ltn i (order x)) ->
  (findex x (iter i f x)) = i.
Proof.
Move=> x i Hi; Rewrite: -(sub_traject f Hi); Rewrite: -size_orbit in Hi.
Exact (index_uniq x Hi (uniq_orbit x)).
Qed.

Lemma iter_findex : (x, y : d) (fconnect f x y) -> (iter (findex x y) f x) = y.
Proof.
Move=> x y; Rewrite: fconnect_orbit; Move=> Hy.
Def: Hi := Hy; Rewrite: -index_mem size_orbit in Hi.
By Rewrite: -(sub_traject f Hi) -/(orbit x) sub_index.
Qed.

Lemma findex0 : (x : d) (findex x x) = (0).
Proof. By Move=> x; Rewrite: /findex /orbit -orderSpred /= set11. Qed.

Lemma fconnect_invariant : (d' : dataSet; k : d -> d')
  (invariant f k) =1 d -> (x, y : d) (fconnect f x y) -> (k x) = (k y).
Proof.
Move=> d' k Hk x y; Case/iter_findex; Elim: {y}(findex x y) => //= [n Hrec].
Rewrite: ~Hrec; Exact (esym (eqP (Hk ?))).
Qed.

Section Loop.

Variable p : (seq d).
Hypotheses Hp : (fcycle f p); Up : (uniq p).
Variable x : d.
Hypothesis Hx : (p x).

(* The first lemma does not depend on Up : (uniq p) *)
Lemma fconnect_cycle : (fconnect f x) =1 p.
Proof.
Case/rot_to: Hx => [i q Dp] y; Rewrite: -(mem_rot i) Dp.
Def: Hp' := Hp; Rewrite: -(cycle_rot i) ~{i}Dp (cycle_path x) /= {1}/eqdf in Hp'.
Case/andP: Hp'; Move/eqP=> Eq Hq; Apply/idP/idP; RightBy Apply path_connect.
Move/connectP => [q' Hq' []] {y}; Case/fpathP: Hq' => [m []] {q'}.
Case/fpathP: Hq Eq => [n []]; Rewrite: !last_traject f_iter; Move=> Dx.
By Apply: (loopingPx f x (S n) ? m); Rewrite: /looping Dx /= setU11.
Qed.

Lemma order_cycle : (order x) = (size p). 
Proof. Rewrite: -(card_uniqP Up); Exact (eq_card fconnect_cycle). Qed.

Lemma orbit_rot_cycle : {i : nat | (orbit x) = (rot i p)}.
Proof.
Case/rot_to: Hx => [i q Dp]; Exists i; Rewrite: Dp.
Def: Hp' := Hp; Rewrite: -(cycle_rot i) Dp (cycle_path x) /= in Hp'.
Case/andP: Hp'; Move=> _; Move/fpathP=> [m Dq].
By Rewrite: /orbit order_cycle -(size_rot i) Dp /= -Dq size_traject.
Qed.

End Loop.

Hypothesis Hf : (injective f).

Lemma f_finv : (monic finv f).
Proof.
Move=> x; Move: (looping_order x) (uniq_orbit x).
Rewrite: /looping /orbit -orderSpred looping_uniq /= /looping.
Pose n := (pred (order x)); Case/setU1P; LeftDone.
Move/trajectP=> [i Hi Dnx]; Rewrite: iter_f -f_iter in Dnx.
By Case/trajectP=> []; Exists i; RightBy Apply Hf.
Qed.

Lemma finv_f : (monic f finv).
Proof. Exact (inj_monic_sym f_finv Hf). Qed.

Lemma isoF : (iso f).
Proof. Exists finv; [Exact finv_f | Exact f_finv]. Qed.

Lemma finv_iso : (iso finv).
Proof. Exists f; [Exact f_finv | Exact finv_f]. Qed.

Lemma finv_inj : (injective finv).
Proof. Exact (monic_inj f_finv). Qed.

Lemma fconnect_sym : (x, y : d) (fconnect f x y) = (fconnect f y x).
Proof.
Cut (x, y : d) (fconnect f x y) -> (fconnect f y x).
  Move=> *; Apply/idP/idP; Auto.
Move=> x y; Move/connectP => [p Hp []] {y}.
Elim: p x Hp => [|y p Hrec] x /=; LeftBy Rewrite: connect0.
Move/andP=> [Hx Hp]; Rewrite: -(finv_f x) (eqP Hx).
Apply: (connect_trans ? (fconnect_finv ?)); Auto.
Qed.

Lemma iter_order : (x : d) (iter (order x) f x) = x.
Proof. Move=> x; Rewrite: -orderSpred -f_iter; Exact (f_finv x). Qed.

Lemma iter_finv : (n : nat; x : d) (leq n (order x)) ->
  (iter n finv x) = (iter (subn (order x) n) f x).
Proof.
Move=> n x Hn; Pose m := (subn (order x) n).
Rewrite: -{1 x}iter_order -(leq_add_sub Hn) -/m /addn iter_plus.
Move: {m x Hn}(iter m f x) => x.
By Elim: n => // [n Hrec]; Rewrite: -iter_f /= finv_f.
Qed.

Lemma cycle_orbit : (x : d) (fcycle f (orbit x)).
Proof.
  Move=> x; Rewrite: /orbit -orderSpred (cycle_path x) /= last_traject -/(finv x).
By Rewrite: fpath_traject /eqdf f_finv set11.
Qed.

Lemma fpath_finv : (x : d; p : (seq d))
  (fpath finv x p) = (fpath f (last x p) (rev (belast x p))).
Proof.
Move=> x p; Elim: p x => [|y p Hrec] x //=.
Rewrite: rev_adds -cats1 path_cat -~Hrec andbC /= {2 4}/eqdf eqd_sym andbT.
BoolCongr; Rewrite: -(inj_eqd Hf) f_finv.
By Case: p => [|z p] //=; Rewrite: rev_adds last_add_last.
Qed. 

Lemma same_fconnect_finv : (fconnect finv) =2 (fconnect f).
Proof.
Move=> x y; Rewrite: (same_connect_rev fconnect_sym).
Apply: eq_connect => [] {x y} x y.
By Rewrite: /eqdf -(inj_eqd Hf) f_finv eqd_sym.
Qed.

Lemma fcard_finv : (fcard finv) =1 (fcard f).
Proof. Exact (eq_n_comp same_fconnect_finv). Qed.

Definition order_set [n : nat; x : d] : bool := (order x) =d n.

Lemma order_div_card : (n : nat; a : (set d))
  (subset a (order_set n)) -> (fclosed f a) -> (ltn (0) n) ->
  (m : nat) ((card a) =d (mult n m)) = ((fcard f a) =d m).
Proof.
Move=> n a Han Ha Hn; Rewrite: /n_comp; Pose b := (setI (froots f) a).
Step Hb: (x : d) (b x) -> (froot f x) = x /\ (order x) = n.
  Move=> x; Move/andP=> [Hrx Hax]; Split; Apply: eqP; Auto.
  Exact (subsetP Han ? Hax).
Step []: (card [x](b (froot f x))) = (card a).
  Apply: eq_card => [x]; Rewrite: /b /setI (roots_root fconnect_sym).
  By Rewrite: -(closed_connect Ha (connect_root ? x)).
Elim: {b}(card b) {1 3 4}b (set11 (card b)) Hb {a Ha Han} => [|m Hrec] b Em Hb.
  Rewrite: -(!eq_card d set0); RightBy Move=> x; Rewrite (set0P Em).
  By Case=> [|m]; Rewrite: card0 mult_sym -(ltnSpred Hn).
Case: (pickP b) => [x Hx | Hb0]; RightBy Rewrite: (eq_card Hb0) card0 in Em.
Case: (Hb ? Hx) => [Dx Hex].
Move=> [|m']; Rewrite: mult_sym /=; LeftBy Rewrite: (cardD1 x) Dx Hx.
Rewrite: (cardD1 x) Hx in Em; Rewrite: -/addn mult_sym.
Apply: (etrans ? (Hrec ? Em ? ?)); RightBy Move=> y; Case/andP; Auto.
Apply: (etrans (congr [p : nat](p =d ?) ?) (eqn_addl ? ? ?)). 
Rewrite: -(cardIC (fconnect f x)); Congr addn.
  Apply: etrans Hex; Apply: eq_card => [y]; Rewrite: /setI andbC.
  Case Hy: (fconnect f x y) => [|] //=.
  By Rewrite: -(rootP fconnect_sym Hy) Dx Hx.
Apply: eq_card => [y]; Rewrite: /setI /setD1 /setC andbC.
By Rewrite: -{2 x}Dx (eqd_root fconnect_sym).
Qed.

Lemma fclosed1 : (a : (set d)) (fclosed f a) -> (x : d) (a x) = (a (f x)).
Proof. Exact [a;Ha;x](Ha x ? (set11 ?)). Qed.
  
Lemma same_fconnect1 : (x : d) (fconnect f x) =1 (fconnect f (f x)).
Proof. Exact [x](same_connect fconnect_sym (fconnect1 x)). Qed.

Lemma same_fconnect1_r : (x, y : d) (fconnect f x y) = (fconnect f x (f y)).
Proof. By Move=> x y; Rewrite: /= !(fconnect_sym x) -same_fconnect1. Qed.

End Orbit.

Section FinMonic.

Variables d : finSet; f, f' : d -> d.
Hypothesis Ef : (monic f f').

Remark Hf : (injective f). Proof. Exact (monic_inj Ef). Qed.

Lemma finv_eq_monic : (finv f) =1 f'.
Proof. Exact (iso_monic_eq (isoF Hf) (finv_f Hf) Ef). Qed.

Lemma monicF_sym : (monic f' f).
Proof. Exact (eq_monic (f_finv Hf) finv_eq_monic (frefl f)). Qed.

Lemma monicF_smove : (x, y : d) (f' x) = y -> x = (f y).
Proof. Exact (monic_move monicF_sym). Qed.

Lemma monic2F_eqd : (x, y : d) ((f x) =d y) = (x =d (f' y)).
Proof. Exact (monic2_eqd Ef monicF_sym). Qed.

End FinMonic.

Section FconnectEq.

Variables d : finSet; f, f' : d -> d.
Hypothesis Eff' : f =1 f'.

Remark eq_eqdf : (eqdf f) =2 (eqdf f').
Proof. Move=> x y; Rewrite: /eqdf Eff'; Done. Qed.

Lemma eq_fconnect : (fconnect f) =2 (fconnect f').
Proof. Exact (eq_connect eq_eqdf). Qed.

Lemma eq_fcard : (fcard f) =1 (fcard f').
Proof. Exact (eq_n_comp eq_fconnect). Qed.

Lemma eq_finv : (finv f) =1 (finv f').
Proof.
Move=> x; Rewrite: /finv /order (eq_card (eq_fconnect x)).
Exact (eq_iter Eff' ? x).
Qed.

Hypothesis Hf : (injective f).

Lemma finv_inv : (finv (finv f)) =1 f.
Proof. Exact (finv_eq_monic (f_finv Hf)). Qed.

Lemma order_finv : (order (finv f)) =1 (order f).
Proof. Move=> x; Exact (eq_card (same_fconnect_finv Hf x)). Qed.

Lemma order_set_finv : (order_set (finv f)) =2 (order_set f).
Proof. By Move=> n x; Rewrite: /order_set order_finv. Qed.

End FconnectEq.

Section RelAdjunction.

Variables d, d' : finSet; h : d' -> d; e : (rel d); e' : (rel d').
Hypotheses He : (connect_sym e); He' : (connect_sym e').

Variable a : (set d).
Hypothesis Ha : (closed e a).

Record rel_adjunction : Set := RelAdjunction {
  rel_unit : (x : d) (a x) -> {x' : d' | (connect e x (h x'))};
  rel_functor : (x', y' : d') (a (h x')) ->
                   (connect e' x' y') = (connect e (h x') (h y'))
}.

Lemma intro_adjunction : (h' : (x : d) (a x) -> d')
  (Hee' : (x : d; Hx : (a x))
      (connect e x (h (h' x Hx)))
   /\ (y : d; Hy : (a y)) (e x y) -> (connect e' (h' x Hx) (h' y Hy)))
  (He'e : (x' : d'; Hx' : (a (h x')))
      (connect e' x' (h' (h x') Hx'))
   /\ (y' : d') (e' x' y') -> (connect e (h x') (h y')))
  rel_adjunction.
Proof.
Move=> h' Hee' He'e; Split.
  By Move=> y Hy; Exists (h' y Hy); Case (Hee' ? Hy).
Move=> x' z' Hx'; Apply/idP/idP.
  Move/connectP => [p Hp []] {z'}.
  Elim: p x' Hp Hx' => [|y' p Hrec] x' /=; LeftBy Rewrite: connect0.
  Move/andP=> [Hx' Hp] Hx.
  Case: (He'e ? Hx) => [_ H]; Move/(H ?): Hx' {H} => Hxp.
  Apply: (connect_trans Hxp (Hrec ? Hp ?)).
  By Rewrite: -(closed_connect Ha Hxp).
Case: (He'e ? Hx') => [Hx'x'' _] Hxz; Apply: (connect_trans Hx'x'').
Move/connectP: Hxz Hx' {Hx'x''} => [p Hp Hpz].
Elim: p {x'}(h x') Hp Hpz => [|y' p Hrec] x /=.
  By Move=> _ Dx; Rewrite Dx; Move=> Hz'; Rewrite He'; Case (He'e ? Hz').
Move/andP=> [Hx' Hp] Dz' Hy.
Move: {}Hy (Hee' ? Hy) => Hx [_ Hhxy]; Rewrite: (Ha Hx') in Hy.
Apply: (connect_trans ?) (Hrec ? Hp Dz' Hy); Auto.
Qed.

Lemma strict_adjunction :
  (Hh : (injective h); Hah : (subset a (codom h)); Hee' : (rel_base h e e' a))
  rel_adjunction.
Proof.
Move=> Hh Hha He'e.
Apply intro_adjunction with [x; Hx](iinv (subsetP Hha x Hx)).
  Move=> x Hx; Split; LeftBy Rewrite f_iinv; Apply connect0.
  By Move=> y Hy Hxy; Apply connect1; Rewrite: -He'e !f_iinv.
Move=> x' Hx'; Split; LeftBy Rewrite: (iinv_f Hh); Apply connect0.
By Move=> y' Hx'y'; Apply connect1; Rewrite He'e.
Qed.

Lemma adjunction_closed : rel_adjunction -> (closed e' (preimage h a)).
Proof.
Move=> [Hu He'e]; Apply (intro_closed He').
Move=> x' y'; Move/(connect1 2!e' 4!?)=> Hx'y' Hx'.
By Rewrite: He'e // in Hx'y'; Rewrite: /preimage -(closed_connect Ha Hx'y').
Qed.

Lemma adjunction_n_comp : rel_adjunction -> 
  (n_comp e a) = (n_comp e' (preimage h a)).
Proof.
Move=> [Hu He'e]; Apply: iso_eq_card; Def: Hac := (closed_connect Ha).
Step Hf1 : (w : (subd (setI (roots e) a)))
           let x' = let (x, Hw) = w in let (_, Hx) = (andP Hw) in
                    let (x', _) = (Hu x Hx) in x' in
           (setI (roots e') (preimage h a) (root e' x')).
  Move=> [x Hw]; Case: (andP Hw) => [_ Hx]; Case: (Hu x Hx) => [x' Hxx'].
  Move: (connect_root e' x'); Rewrite: /setI (roots_root He') /preimage /=.
  Rewrite: He'e /=; RightBy Rewrite: -(Hac ? ? Hxx').
  By Move=> Hx'rx'; Rewrite: -(Hac ? ? (connect_trans Hxx' Hx'rx')).
Step Hf2 : (w : (subd (setI (roots e') (preimage h a))))
           (setI (roots e) a (root e (h (subdE w)))).
  Move=> [x' Hw]; Case: (andP Hw); Rewrite: /preimage /=; Move=> _ Hx.
  By Rewrite: /setI (roots_root He) -(Hac ? ? (connect_root e (h x'))).
Red in Hf1; Exists [w](subdI 1!d' (Hf1 w)); Exists [w](subdI 1!d (Hf2 w)).
  Move=> [x Hw]; Apply: subdE_inj; Simpl.
  Case: (andP Hw) => [Hrx Hx]; Case: (Hu x Hx) => [x' Hx'].
  Rewrite: -(eqP Hrx); Apply: (esym (rootP He (connect_trans Hx' ?))).
  Rewrite: -He'e /preimage -?(Hac ? ? Hx') //; Apply connect_root.
Move=> w; Apply: subdE_inj; Simpl.
Case: (andP (Hf2 w)); Clear; Case/(Hu ?); Case: w => [x' Hw] y' /=.
Case: (andP Hw) => [Hrx' Hx'] Hrxy; Unfold roots in Hrx'.
Rewrite: -(eqP Hrx'); Apply: (rootP He').
Rewrite: He' He'e //; Exact (connect_trans (connect_root ? ?) Hrxy).
Qed.

End RelAdjunction.

Unset Implicit Arguments.


