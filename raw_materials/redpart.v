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
Require geometry.
Require part.
Require quiz.
Require quiztree.

Set Implicit Arguments.

(* Reducibility check for parts. We use a zipper structure to navigate the *)
(* part while searching for a reducible config. Once we detect a match for *)
(* the top arity range values, we walk the config quiz again to look for a *)
(* match for the other values (most of the time, though, the match spans   *)
(* only singleton ranges).                                                 *)
(*   We work here under the assumption that the map is plain and cubic,    *)
(* and that the quiz tree does not directly fit the map. We show that this *)
(* lifts to parts for which redpart returns true (for a fixed hub size).   *)

Section Redpart.

(* The function is only applied to the main quiz tree, but it is treated   *)
(* as a parameter here, to prevemt unwanted expansions.                    *)
Variables qt : quiz_tree; g : hypermap.

Hypothesis Hg : (plain_cubic_pentagonal g).
Local HgF :  (pentagonal g) := Hg.
Local De2 := (plain_eq Hg).
Local Dnf := (plain_eq' Hg).
Local Dn3 := (cubic_eq Hg).
Local Dn2 := (cubic_eq' Hg).
Remark Dfn : (n : nat; x : g)  n =d (arity x) -> x = (iter n face x).
Proof. By Move=> n x Dn; Rewrite: (eqP Dn) iter_face_arity. Qed.

Hypothesis Hqt : (y : g) (negb (qzt_fit y qt)).

Section RedpartRec.

(* The hub size must be in the qarity range.                               *)
Variable ahub : qarity.
Local nhub : nat := ahub.

Section Zpart.

(* A zipper part is a pair of a left and right part, with the left part  *)
(* reversed (not mirrored!), plus an index which identifies the dart     *)
(* represented by the part (there is also a nil index). These darts are  *)
(* the following:                                                        *)
(*  - the two node cycles that fall between the left and  right parts,   *)
(*    that is, that contain a dart from both the left spoke and right    *)
(*    spoke face. Their third dart is either the hub dart or a hat dart  *)
(*    the right part.                                                    *)
(*  - the (disjoint) qstepL and qstepR chains that run around the left   *)
(*    spoke face, counter-clockwise and clockwise, respectively, and end *)
(*    with hat darts (the left chain ends with the hat of the right part *)
(*    and conversely).                                                   *)
(* Note that this excludes the darts on the spoke face itself, which are *)
(* unreachable using quiz steps (they can only match the center triangle *)
(* and therefore don't occur in the recursive traversal).                *)
(*  We have to be careful with double steps, which may cross over a non  *)
(* existent dart in a corner case (the articulation has degree 6 and     *)
(* matches a spoke with range [5, 6])).                                  *)
(*  The two parts wrap around the hub exactly twice; the initial parts   *)
(* are available as parameters in this section, in case additional wrap  *)
(* around is needed.                                                     *)

Variable red_rec : part -> bool.

Hypothesis Hred_rec : (x : g; p : part)
  (arity x) = nhub -> (exact_fitp x p) -> (negb (red_rec p)).

Variables p0l, p0r : part; x0 : g.
Hypothesis Dp0l : p0l = (rev_part p0r).

Hypotheses Hp0r : (exact_fitp x0 p0r); Hx0n : (arity x0) = nhub.
Remark Ep0r : (size_part p0r) = nhub.
Proof. By Case/andP: {}Hp0r; Move/eqP; Rewrite: Hx0n. Qed.

Inductive zpart_loc : Set :=
  Znil   : zpart_loc
| Zhub   : zpart_loc  (* hub-side node cycle *)
| Zhubl  : zpart_loc
| Zhubr  : zpart_loc
| Zhat   : zpart_loc  (* hat-side node cycle *)
| Zhatl  : zpart_loc
| Zhatr  : zpart_loc
| Zfan0l : zpart_loc  (* the left step chain; Zfan0l is the last (hat) dart *)
| Zfan1l : zpart_loc
| Zfan2l : zpart_loc
| Zfan3l : zpart_loc
| Zfan0r : zpart_loc  (* the right step chain *)
| Zfan1r : zpart_loc
| Zfan2r : zpart_loc
| Zfan3r : zpart_loc.

Definition zmove_def [zi : zpart_loc; x : g] : g :=
  Cases zi of
    Znil   => x
  | Zhub   => x
  | Zhubl  => (node x)
  | Zhubr  => (node (node x))
  | Zhat   => (node (edge (node (node x))))
  | Zhatl  => (edge (node (node x)))
  | Zhatr  => (face (node (node x)))
  | Zfan0l => (face (edge (iter (2) [y](edge (node y)) (node x))))
  | Zfan1l => (face (edge (iter (3) [y](edge (node y)) (node x))))
  | Zfan2l => (face (edge (iter (4) [y](edge (node y)) (node x))))
  | Zfan3l => (face (edge (iter (5) [y](edge (node y)) (node x))))
  | Zfan0r => (edge (iter (2) face (node x)))
  | Zfan1r => (edge (iter (3) face (node x)))
  | Zfan2r => (edge (iter (4) face (node x)))
  | Zfan3r => (edge (iter (5) face (node x)))
  end.
Definition zmove : zpart_loc -> g -> g := (nosimpl zmove_def).

Inductive zpart : Set := Zpart : zpart_loc -> part -> part -> zpart.

Definition zvalid [pl, pr : part] : Prop := 
  (catrev_part pl pr) = (cat_part p0r p0r).

Definition zpvalid [zp : zpart] : Prop := let (_, pl, pr) = zp in (zvalid pl pr).

Lemma zvalid_init : (zvalid p0l p0r).
Proof. By Rewrite: /zvalid catrev_part_eq Dp0l rev_rev_part. Qed.

Definition shift_part [p1, p2 : part] : part := (cat_part (take_part (1) p1) p2).

Syntactic Definition p0ll := (drop_part (1) p0l).
Syntactic Definition p0lr := (shift_part p0l p0r).
Syntactic Definition p0rr := (drop_part (1) p0r).
Syntactic Definition p0rl := (shift_part p0r p0l).

Lemma zvalid_initl : (zvalid p0ll p0lr).
Proof.
Move: Ep0r; Rewrite: -size_rev_part -Dp0l -Hx0n -orderSpred /zvalid -zvalid_init.
By Case p0l.
Qed.

Lemma zvalid_initr : (zvalid p0rl p0rr).
Proof.
By Move: Ep0r; Rewrite: -Hx0n -orderSpred /zvalid -zvalid_init; Case p0r.
Qed.

Lemma zvalid_fit : (pl, pr : part) (zvalid pl pr) -> (fitp x0 (catrev_part pl pr)).
Proof.
Move=> pl pr Dplr; Rewrite: ~{pl pr}Dplr fitp_cat.
By Case/andP: {}Hp0r; Case/eqP; Rewrite: /= (iter_face_arity x0) andbb.
Qed.

(*
Lemma zpvalid_fit : (zp : zpart) (zpvalid zp) ->
  let (_, pl, pr) = zp in (fitp x0 (catrev_part pl pr)).
Proof. By Case=> *; Apply: zvalid_fit. Qed.
*)

Definition zproper [zp : zpart] : bool :=
  if zp is (Zpart Znil _ _) then false else true.

Definition zporg [zp : zpart] : g :=
  let (_, pl, _) = zp in (iter (size_part pl) face x0).

Definition zdart [zp : zpart] : g :=
  let (zi, _, _) = zp in (zmove zi (zporg zp)).

Definition zpfit [x : g; zp : zpart] : Prop :=
  (zproper zp) -> (zdart zp) = x.

Definition hub_range : prange :=
  Cases ahub of
    Qa5 => Pr55
  | Qa6 => Pr66
  | Qa7 => Pr77
  | Qa8 => Pr88
  | _   => Pr99
  end.

Definition zrange [zp : zpart] : prange :=
  Cases zp of
    (Zpart Znil _ _)    => Pr59
  | (Zpart Zhub _ _)    => hub_range
  | (Zpart Zhubl pl _)  => (get_spoke pl)
  | (Zpart Zhubr _ pr)  => (get_spoke pr)
  | (Zpart Zhatl pl _)  => (get_spoke pl)
  | (Zpart Zhat _ pr)   => (get_hat pr)
  | (Zpart Zhatr _ pr)  => (get_spoke pr)
  | (Zpart Zfan0l _ pr) => (get_hat pr)
  | (Zpart Zfan1l pl _) => (get_fan1l pl)
  | (Zpart Zfan2l pl _) => (get_fan2l pl)
  | (Zpart Zfan3l pl _) => (get_fan3l pl)
  | (Zpart Zfan0r pl _) => (get_hat pl)
  | (Zpart Zfan1r pl _) => (get_fan1r pl)
  | (Zpart Zfan2r pl _) => (get_fan2r pl)
  | (Zpart Zfan3r pl _) => (get_fan3r pl)
  end.

Lemma zrange_dart : (zp : zpart) (zpvalid zp) -> (zrange zp (arity (zdart zp))).
Proof.
Move=> [zi pl pr]; Move/zvalid_fit.
Case: zi; Rewrite: /= /zmove /= ?HgF //.
Move: (HgF x0); Rewrite: /zporg arity_iter_face Hx0n /nhub /hub_range;
  By Case ahub.
By Case Dpl: pl; Rewrite: /zporg ?HgF //= Dnf fitp_catrev; Case/and3P.
By Rewrite: fitp_catrev Dn2 arity_face;
   Case Dpr: pr; Rewrite: ?HgF //=; Case/and3P.
By Rewrite: fitp_catrev -Dnf !Dn2 arity_face;
   Case Dpr: pr; Rewrite: ?HgF //=; Case/and4P.
By Rewrite: -arity_face Enode;
  Case Dpl: pl; Rewrite: /zporg ?HgF //= Dnf fitp_catrev; Case/and3P.
By Rewrite: fitp_catrev Dn2 !arity_face;
   Case Dpr: pr; Rewrite: ?HgF //=; Case/and3P.
By Rewrite: fitp_catrev De2 -Dnf !Dn2 !arity_face;
   Case Dpr: pr; Rewrite: ?HgF //=; Case/and4P.
By Case: pl => [|s h|h f1|h f1 f2|h f1 f2 f3]; Try Move=> pl;
  Rewrite: ?HgF //= fitp_catrev /= Dnf arity_face;
  Case/and5P=> [_ Ds _ Hf1]; Try Case/andP=> [Hf2]; Try Case/andP=> [Hf3];
  Clear; Rewrite: (Dfn Ds) /= !Eface.
By Case: pl => [|s h|h f1|h f1 f2|h f1 f2 f3]; Try Move=> pl;
  Rewrite: ?HgF //= fitp_catrev /= Dnf arity_face;
  Case/and5P=> [_ Ds _ Hf1]; Case/andP=> [Hf2 _]; Rewrite: (Dfn Ds) /= !Eface.
By Case: pl => [|s h|h f1|h f1 f2|h f1 f2 f3]; Try Move=> pl;
  Rewrite: ?HgF //= fitp_catrev /= Dnf arity_face;
  Case/and5P=> [_ Ds _ Hf1 _]; Rewrite: (Dfn Ds) /= !Eface.
By Case Dpl: pl; Rewrite: /= ?HgF // fitp_catrev /zporg /= Dnf; Case/and4P.
By Case Dpl: pl; Rewrite: /= ?HgF // fitp_catrev /zporg /= Dnf; Case/and5P.
By Case Dpl: pl; Rewrite: /= ?HgF // fitp_catrev /zporg /= Dnf 3!andbA; Case/and3P.
By Case Dpl: pl; Rewrite: /= ?HgF // fitp_catrev /zporg /= Dnf 4!andbA; Case/and3P.
Qed.

Definition zshiftl [zi : zpart_loc; zp : zpart] : zpart :=
  Cases zp of
    (Zpart _ (Pcons _ _ Pnil) _)        => (Zpart zi p0l p0r)
  | (Zpart _ (Pcons6 _ _ Pnil) _)       => (Zpart zi p0l p0r)
  | (Zpart _ (Pcons7 _ _ _ Pnil) _)     => (Zpart zi p0l p0r)
  | (Zpart _ (Pcons8 _ _ _ _ Pnil) _)   => (Zpart zi p0l p0r)
  | (Zpart _ (Pcons s h pl) pr)         => (Zpart zi pl (Pcons s h pr))
  | (Zpart _ (Pcons6 h f1 pl) pr)       => (Zpart zi pl (Pcons6 h f1 pr))
  | (Zpart _ (Pcons7 h f1 f2 pl) pr)    => (Zpart zi pl (Pcons7 h f1 f2 pr))
  | (Zpart _ (Pcons8 h f1 f2 f3 pl) pr) => (Zpart zi pl (Pcons8 h f1 f2 f3 pr))
  | (Zpart _ Pnil _)                    => (Zpart zi p0ll p0lr)
  end.

Definition zshiftr [zi : zpart_loc; zp : zpart] : zpart :=
  Cases zp of
    (Zpart _ _ (Pcons _ _ Pnil))        => (Zpart zi p0l p0r)
  | (Zpart _ _ (Pcons6 _ _ Pnil))       => (Zpart zi p0l p0r)
  | (Zpart _ _ (Pcons7 _ _ _ Pnil))     => (Zpart zi p0l p0r)
  | (Zpart _ _ (Pcons8 _ _ _ _ Pnil))   => (Zpart zi p0l p0r)
  | (Zpart _ pl (Pcons s h pr))         => (Zpart zi (Pcons s h pl) pr)
  | (Zpart _ pl (Pcons6 h f1 pr))       => (Zpart zi (Pcons6 h f1 pl) pr)
  | (Zpart _ pl (Pcons7 h f1 f2 pr))    => (Zpart zi (Pcons7 h f1 f2 pl) pr)
  | (Zpart _ pl (Pcons8 h f1 f2 f3 pr)) => (Zpart zi (Pcons8 h f1 f2 f3 pl) pr)
  | (Zpart _ _ Pnil)                    => (Zpart zi p0rl p0rr)
  end.

Lemma zpvalid_shiftl : (zi : zpart_loc; zp : zpart)
  (zpvalid zp) -> (zpvalid (zshiftl zi zp)).
Proof.
Move=> zi [zi' pl pr] {zi'}/=; Move: {}zvalid_init {}zvalid_initl.
By Case: pl => //= [s h|h f1|h f1 f2|h f1 f2 f3]; Case.
Qed.

Lemma zproper_shiftl : (zi : zpart_loc; zp : zpart)
  (zproper (zshiftl zi zp)) = (if zi is Znil then false else true).
Proof. 
Move=> zi [zi' pl pr] {zi'}/=.
By Case: pl => //= [s h|h f1|h f1 f2|h f1 f2 f3]; Case.
Qed.

Lemma zpvalid_shiftr : (zi : zpart_loc; zp : zpart)
  (zpvalid zp) -> (zpvalid (zshiftr zi zp)).
Proof.
Move=> zi [zi' pl pr] {zi'}/=; Move: {}zvalid_init {}zvalid_initr.
By Case: pr => //= [s h|h f1|h f1 f2|h f1 f2 f3]; Case.
Qed.

Lemma zproper_shiftr : (zi : zpart_loc; zp : zpart)
  (zproper (zshiftr zi zp)) = (if zi is Znil then false else true).
Proof. 
Move=> zi [zi' pl pr] {zi'}/=.
By Case: pr => //= [s h|h f1|h f1 f2|h f1 f2 f3]; Case.
Qed.

Lemma zdart_shiftl : (zi : zpart_loc; zp : zpart)
  (zdart (zshiftl zi zp)) = (zmove zi (edge (node (zporg zp)))).
Proof.
Move=> zi [zi' [|s h pl|h f1 pl|h f1 f2 pl|h f1 f2 f3 pl] pr];
  Try By Case: pl => *; Rewrite: /= Eface // Dp0l size_rev_part;
         Case/andP: {}Hp0r; Case/eqP; Rewrite: /= iter_face_arity.
Rewrite: /zshiftl /zdart /zporg size_drop_part Dp0l size_rev_part subn1 /=.
By Rewrite: -{2 x0}iter_face_arity -orderSpred Ep0r -Hx0n /= Eface.
Qed.

Lemma zdart_shiftr : (zi : zpart_loc; zp : zpart)
  (zpvalid zp) -> (zdart (zshiftr zi zp)) = (zmove zi (face (zporg zp))).
Proof.
Move=> zi [zi' pl pr] Hzp.
Move: (congr size_part (etrans Hzp (esym zvalid_initr))).
Move: {Hzp}(congr size_part Hzp).
Rewrite: !catrev_part_eq !size_cat_part !size_rev_part size_drop_part subn1.
Rewrite: -{1 (size_part p0r)}size_rev_part -Dp0l addnC /addn Ep0r -Hx0n.
Case: pr => [|s h pr|h f1 pr|h f1 f2 pr|h f1 f2 f3 pr];
  Try By Case Dpr: pr; Rewrite: //= f_iter; Case/esym;
      Rewrite: iter_plus iter_face_arity.
Move=> _ Epl; Simpl in Epl; Rewrite: /zshiftr /zdart /zporg ~Epl.
By Rewrite: iter_plus -/(finv face x0) f_iter -iter_f (f_finv (Iface g)).
Qed.

Lemma zshiftl_eq : (zi, zi' : zpart_loc; pl, pr : part)
  (ltn (1) (size_part pl)) ->
    (zshiftl zi' (Zpart zi pl pr)) =
      (Zpart zi' (drop_part (1) pl) (shift_part pl pr)).
Proof. By Move=> zi zi'; Case=> // [s h|h f1|h f1 f2|h f1 f2 f3]; Case. Qed.

Lemma zshiftr_eq : (zi, zi' : zpart_loc; pl, pr : part)
  (ltn (1) (size_part pr)) ->
    (zshiftr zi' (Zpart zi pl pr)) =
       (Zpart zi' (shift_part pr pl) (drop_part (1) pr)).
Proof. By Move=> zi zi' pl; Case=> // [s h|h f1|h f1 f2|h f1 f2 f3]; Case. Qed.

Definition zfanL [pr : part] : zpart_loc :=
  Cases pr of
    (Pcons Pr55 _ _)   => Zfan0l
  | (Pcons6 _ _ _)     => Zfan1l
  | (Pcons7 _ _ _ _)   => Zfan2l
  | (Pcons8 _ _ _ _ _) => Zfan3l
  | _                  => Znil
  end.

Definition zfanR [pl : part] : zpart_loc :=
  Cases pl of
    (Pcons Pr55 _ _)   => Zfan0r
  | (Pcons6 _ _ _)     => Zfan1r
  | (Pcons7 _ _ _ _)   => Zfan2r
  | (Pcons8 _ _ _ _ _) => Zfan3r
  | _                  => Znil
  end.

Definition zstepL [zp : zpart] : zpart :=
  Cases zp of
    (Zpart Zhub    _  _) => (zshiftl Zhubl zp)
  | (Zpart Zhubl  pl pr) => (Zpart Zhat pl pr)
  | (Zpart Zhubr   _  _) => (zshiftr Zhubr zp)
  | (Zpart Zhat    _ pr) => (zshiftr (zfanL pr) zp)
  | (Zpart Zhatl  pl pr) => (Zpart (zfanR pl) pl pr)
  | (Zpart Zhatr  pl pr) => (Zpart Zhub pl pr)
  | (Zpart Zfan0l pl pr) => (Zpart Zhatr pl pr)
  | (Zpart Zfan1l pl pr) => (Zpart Zfan0l pl pr)
  | (Zpart Zfan2l pl pr) => (Zpart Zfan1l pl pr)
  | (Zpart Zfan3l pl pr) => (Zpart Zfan2l pl pr)
  | (Zpart _      pl pr) => (Zpart Znil pl pr)
  end.

Definition zstepR [zp : zpart] : zpart :=
  Cases zp of
    (Zpart Zhub    _  _) => (zshiftr Zhubr zp)
  | (Zpart Zhubl   _  _) => (zshiftl Zhubl zp)
  | (Zpart Zhubr  pl pr) => (Zpart Zhat pl pr)
  | (Zpart Zhat   pl pr) => (Zpart (zfanR pl) pl pr)
  | (Zpart Zhatl  pl pr) => (Zpart Zhub pl pr)
  | (Zpart Zhatr   _ pr) => (zshiftr (zfanL pr) zp)
  | (Zpart Zfan0r  _  _) => (zshiftl Zhatl zp)
  | (Zpart Zfan1r pl pr) => (Zpart Zfan0r pl pr)
  | (Zpart Zfan2r pl pr) => (Zpart Zfan1r pl pr)
  | (Zpart Zfan3r pl pr) => (Zpart Zfan2r pl pr)
  | (Zpart _      pl pr) => (Zpart Znil pl pr)
  end.

Lemma zproper_stepL : (zp : zpart) (zproper (zstepL zp)) -> (zproper zp).
Proof. By Do 2 Case. Qed.

Lemma zpvalid_stepL : (zp : zpart) (zpvalid zp) -> (zpvalid (zstepL zp)).
Proof.
By Move=> [zi pl pr]; Case: zi => //;
  First [Apply: (!zpvalid_shiftl) | Apply: (!zpvalid_shiftr)].
Qed.

Lemma zdart_stepL : (zp : zpart) (zpvalid zp) ->
  (zpfit (qstepL (zdart zp)) (zstepL zp)).
Proof.
Rewrite: /zstepL /qstepL; Move=> [zi pl pr]; Case Dzi: zi => // [] Hzp Hzpp;
  Rewrite: ?zdart_shiftr ?zdart_shiftl //= /zmove /= ?Dn3 //;
  Try By Rewrite: ?Dnf ?De2 // ?Dn2 ?De2 ?Enode //.
  Move/zvalid_fit: Hzp; Rewrite: fitp_catrev; Rewrite: zproper_shiftr in Hzpp.
  By Case: pr Hzpp => //= [s h|h f1|h f1 f2|h f1 f2 f3] pr; Try Case: s => //=;
    Clear; Move/and3P=> [_ Ds _]; Rewrite: Dnf {2 x0}lock (Dfn Ds) /= -lock;
    Rewrite: ?Eface !Dn2 !De2 -!Dnf Dn2 !Dnf.
Move/zvalid_fit: Hzp.
By Case: pl Hzpp => //= [s h|h f1|h f1 f2|h f1 f2 f3] pl; Try Case: s => //=;
  Clear; Rewrite: fitp_catrev /=; Move/and3P=> [_ Ds _];
  Rewrite: Dnf {1 x0}lock (Dfn Ds) /= ?Eface -lock Dnf.
Qed.

Lemma zproper_stepR : (zp : zpart) (zproper (zstepR zp)) -> (zproper zp).
Proof. By Do 2 Case. Qed.

Lemma zpvalid_stepR : (zp : zpart) (zpvalid zp) -> (zpvalid (zstepR zp)).
Proof.
By Move=> [zi pl pr]; Case: zi => //;
  First [Apply: (!zpvalid_shiftl) | Apply: (!zpvalid_shiftr)].
Qed.

Lemma zdart_stepR : (zp : zpart) (zpvalid zp) ->
  (zpfit (qstepR (zdart zp)) (zstepR zp)).
Proof.
Rewrite: /zstepR /qstepR; Move=> [zi pl pr]; Case Dzi: zi => // [] Hzp Hzpp;
  Rewrite: ?zdart_shiftr ?zdart_shiftl //= /zmove /= ?Dn3 ?De2 ?Dn3 ?Dnf //;
  Try (By Rewrite: Dn2 De2); Move/zvalid_fit: Hzp Hzpp.
By Case: pl => //= [s h|h f1|h f1 f2|h f1 f2 f3] pl; Try Case: s => //=;
  Rewrite: fitp_catrev /=; Move/and3P=> [_ Ds _] _;
  Rewrite: Dnf {1 x0}lock (Dfn Ds) /= ?Eface -lock Dnf.
Rewrite: fitp_catrev zproper_shiftr -Dnf !Dn2.
By Case: pr => //= [s h|h f1|h f1 f2|h f1 f2 f3] pr; Try Case: s => //=;
  Move/and3P=> [_ Ds _] _; Rewrite: Dnf {2 x0}lock (Dfn Ds) /= -lock ?Eface.
Qed.

Definition fitqa [r : prange; qa : qarity] : bool :=
  Cases r qa of
    Pr55 Qa5 => true
  | Pr56 Qa6 => true
  | Pr66 Qa6 => true
  | Pr57 Qa7 => true
  | Pr67 Qa7 => true
  | Pr77 Qa7 => true
  | Pr58 Qa8 => true
  | Pr68 Qa8 => true
  | Pr78 Qa8 => true
  | Pr88 Qa8 => true
  | _ _ => false
  end.

Lemma fitqa_proper : (zp : zpart; qa : qarity)
  (fitqa (zrange zp) qa) -> (zproper zp).
Proof. By Do 2 Case. Qed.

Definition popqa [r : prange] : prange :=
  Cases r of
    Pr56 => Pr55
  | Pr57 => Pr56
  | Pr58 => Pr57
  | Pr67 => Pr66
  | Pr68 => Pr67
  | Pr78 => Pr77
  | _ => Pr99
  end.

Definition topqa [r : prange] : qarity :=
  Cases r of
    Pr55 => Qa5
  | Pr56 => Qa6
  | Pr66 => Qa6
  | Pr57 => Qa7
  | Pr67 => Qa7
  | Pr77 => Qa7
  | Pr58 => Qa8
  | Pr68 => Qa8
  | Pr78 => Qa8
  | Pr88 => Qa8
  |    _ => Qa9
  end.

Lemma fitqa_topqa : (r : prange; qa : qarity)
  (fitqa r qa) = (andb (leq qa (8)) (qa::nat) =d ((topqa r)::nat)).
Proof. By Do 2 Case. Qed.

Lemma fitqa_popqa : (r : prange; qa : qarity) (fitqa r qa) ->
  (n : nat) (andb (r n) (orb (popqa r (9)) (negb (popqa r n)))) -> n = qa.
Proof. Do 2 Case=> //; Clear; Do 9 Case=> //. Qed.

Definition zpfit_top [zp : zpart] : Prop :=
  (arity (zdart zp)) = (topqa (zrange zp)).

(* Variants of the step functions that assume that (zpfit_top zp) holds. *)

Definition zfanLt [pr : part] : zpart_loc :=
  Cases pr of
    (Pcons Pr55 _ _)   => Zfan0l
  | (Pcons Pr56 _ _)   => Zfan1l
  | (Pcons Pr66 _ _)   => Zfan1l
  | (Pcons6 _ _ _)     => Zfan1l
  | (Pcons7 _ _ _ _)   => Zfan2l
  | (Pcons8 _ _ _ _ _) => Zfan3l
  | _                  => Znil
  end.

Definition zfanRt [pl : part] : zpart_loc :=
  Cases pl of
    (Pcons Pr55 _ _)   => Zfan0r
  | (Pcons Pr56 _ _)   => Zfan1r
  | (Pcons Pr66 _ _)   => Zfan1r
  | (Pcons6 _ _ _)     => Zfan1r
  | (Pcons7 _ _ _ _)   => Zfan2r
  | (Pcons8 _ _ _ _ _) => Zfan3r
  | _                  => Znil
  end.

Definition zstepLt [zp : zpart] : zpart :=
  Cases zp of
    (Zpart Zhub    _  _) => (zshiftl Zhubl zp)
  | (Zpart Zhubl  pl pr) => (Zpart Zhat pl pr)
  | (Zpart Zhubr   _  _) => (zshiftr Zhubr zp)
  | (Zpart Zhat    _ pr) => (zshiftr (zfanL pr) zp)
  | (Zpart Zhatl  pl pr) => (Zpart (zfanRt pl) pl pr)
  | (Zpart Zhatr  pl pr) => (Zpart Zhub pl pr)
  | (Zpart Zfan0l pl pr) => (Zpart Zhatr pl pr)
  | (Zpart Zfan1l pl pr) => (Zpart Zfan0l pl pr)
  | (Zpart Zfan2l pl pr) => (Zpart Zfan1l pl pr)
  | (Zpart Zfan3l pl pr) => (Zpart Zfan2l pl pr)
  | (Zpart _      pl pr) => (Zpart Znil pl pr)
  end.

Definition zstepRt [zp : zpart] : zpart :=
  Cases zp of
    (Zpart Zhub    _  _) => (zshiftr Zhubr zp)
  | (Zpart Zhubl   _  _) => (zshiftl Zhubl zp)
  | (Zpart Zhubr  pl pr) => (Zpart Zhat pl pr)
  | (Zpart Zhat   pl pr) => (Zpart (zfanR pl) pl pr)
  | (Zpart Zhatl  pl pr) => (Zpart Zhub pl pr)
  | (Zpart Zhatr   _ pr) => (zshiftr (zfanLt pr) zp)
  | (Zpart Zfan0r  _  _) => (zshiftl Zhatl zp)
  | (Zpart Zfan1r pl pr) => (Zpart Zfan0r pl pr)
  | (Zpart Zfan2r pl pr) => (Zpart Zfan1r pl pr)
  | (Zpart Zfan3r pl pr) => (Zpart Zfan2r pl pr)
  | (Zpart _      pl pr) => (Zpart Znil pl pr)
  end.

Lemma zproper_stepLt : (zp : zpart) (zproper (zstepLt zp)) -> (zproper zp).
Proof. By Do 2 Case. Qed.

Lemma zpvalid_stepLt : (zp : zpart) (zpvalid zp) -> (zpvalid (zstepLt zp)).
Proof.
By Move=> [zi pl pr]; Case: zi => //;
  First [Apply: (!zpvalid_shiftl) | Apply: (!zpvalid_shiftr)].
Qed.

Lemma zdart_stepLt : (zp : zpart) (zpfit_top zp) -> (zpvalid zp) ->
  (zpfit (qstepL (zdart zp)) (zstepLt zp)).
Proof.
Move=> [zi pl pr] Hzpt Hzp; Case: zi {Hzpt}(esym Hzpt) (zdart_stepL Hzp) Hzp => //.
Rewrite: /zpfit_top /= /zmove /= /qstepL -arity_face Enode.
Move=> H; Rewrite: ~{H}(Dfn (introT eqP H)).
By Case: pl => //; Case=> //= [] h pl _; Rewrite: /zpfit /= /zmove /= !Eface !Dnf.
Qed.

Lemma zproper_stepRt : (zp : zpart) (zproper (zstepRt zp)) -> (zproper zp).
Proof. By Do 2 Case. Qed.

Lemma zpvalid_stepRt : (zp : zpart) (zpvalid zp) -> (zpvalid (zstepRt zp)).
Proof.
By Move=> [zi pl pr]; Case: zi => //;
  First [Apply: (!zpvalid_shiftl) | Apply: (!zpvalid_shiftr)].
Qed.

Lemma zdart_stepRt : (zp : zpart)  (zpfit_top zp) -> (zpvalid zp) ->
  (zpfit (qstepR (zdart zp)) (zstepRt zp)).
Proof.
Move=> [zi pl pr] Hzpt Hzp; Case: zi Hzp {Hzpt}(esym Hzpt) (zdart_stepR Hzp) => //.
Move=> Hzp; Rewrite: /zpfit_top /zstepR /zstepRt /zpfit !zdart_shiftr //.
Rewrite: !zproper_shiftr; Case: pr Hzp => //= [s h pr] Hzp.
Rewrite: /zmove /= Dn2 !arity_face /qstepR.
Move=> H; Move: {H}(congr (iter (4) (comp edge node)) (Dfn (introT eqP H))).
By Rewrite: /comp /=; Case: s Hzp => //= [] _;
  Rewrite: !Eface; Case; Do 2 Clear; Rewrite: !De2 Dnf Dn2 De2.
Qed.

(* Updating a part. *)

Definition red_pcons [pc : prange -> part -> part; r : prange; pr : part] : bool :=
  let rpc = [r'](red_rec (take_part nhub (cat_part (pc r' pr) p0r))) in
  Cases r of
    Pr56 => (rpc Pr55)
  | Pr57 => (rpc Pr56)
  | Pr58 => (rpc Pr57)
  | Pr67 => (rpc Pr66)
  | Pr68 => (rpc Pr67)
  | Pr78 => (rpc Pr77)
  | _ => true
  end.

Lemma red_pcons_fit :
  (pc : prange -> part -> part; j : subpart_loc) (part_update pc j) ->
  (r : prange; pl, pr : part) (zvalid pl (pc r pr)) ->
  (qa : qarity) (fitqa r qa) -> (red_pcons pc r pr) ->
  (arity (j g (iter (size_part pl) face x0))) = qa.
Proof.
Move=> pc df Hpc r pl pr Hpl qa Hqa Hpcr; Apply: (fitqa_popqa Hqa).
Move: (zvalid_fit Hpl); Rewrite: fitp_catrev.
Case/andP; Pose y := (iter (size_part pl) face x0); Move=> _ Hypr.
Case: (Hpc r pr) => [Epr H]; Case/(H g y): Hypr {H} => [Hyr Hypr'].
Rewrite: Hyr; Apply/norP; Rewrite: negb_elim; Move=> [Hr Hyr'].
Pose p0r' := (cat_part (pc (popqa r) pr) p0r).
Case Hp0r': (exact_fitp y (take_part nhub p0r')).
  Step Ey: (arity y) = nhub By Rewrite: /y arity_iter_face.
  By Case/idP: (Hred_rec Ey Hp0r'); Rewrite: /p0r'; Case: {}r Hr Hpcr.
Def: Ep0r' := (cat_take_drop_part nhub p0r'); Case/andP: {}Hp0r => [_ Hx0p0r].
Case/andP: Hp0r'; Split.
  Rewrite: /y arity_iter_face eqd_sym Hx0n.
  Move: (introT eqP (congr size_part Ep0r')); Rewrite: size_cat_part {2 3}/p0r'.
  By Rewrite: size_drop_part size_cat_part Ep0r subn_addl addnC eqn_addl.
Step Hp0r' : (fitp y p0r');
  RightBy Rewrite: -Ep0r' fitp_cat in Hp0r'; Case/andP: Hp0r'.
Rewrite: /p0r' fitp_cat Hypr' // /y -iter_plus addnI addnC.
Case: (Hpc (popqa r) pr) => [Epr' _]; Rewrite: ~Epr' -~Epr.
Rewrite: -(size_rev_part pl) -size_cat_part -catrev_part_eq Hpl size_cat_part.
By Rewrite: Ep0r -Hx0n /addn iter_plus !iter_face_arity.
Qed.

Definition red_popr_spoke [pr : part] : bool :=
  if pr is (Pcons s h p) then (red_pcons [s'](Pcons s' h) s p) else true.

Lemma red_popr_spoke_fit : (pl, pr : part) (zvalid pl pr) ->
  (qa : qarity) (fitqa (get_spoke pr) qa) -> (red_popr_spoke pr) ->
  (arity (edge (iter (size_part pl) face x0))) = qa.
Proof.
By Move=> pl; Case=> // [s h pr|h f1 pr|h f1 f2 pr|h f1 f2 f3 pr];
  Try Apply: (red_pcons_fit (updatePs h)); Move/zvalid_fit;
  Rewrite: fitp_catrev /=; Case/and3P; Clear; Case/eqP; Clear; Case.
Qed.

Definition red_popr_hat [pr : part] : bool :=
  Cases pr of
    (Pcons s h p)         => (red_pcons [h'](Pcons s h') h p)
  | (Pcons6 h f1 p)       => (red_pcons [h'](Pcons6 h' f1) h p)
  | (Pcons7 h f1 f2 p)    => (red_pcons [h'](Pcons7 h' f1 f2) h p)
  | (Pcons8 h f1 f2 f3 p) => (red_pcons [h'](Pcons8 h' f1 f2 f3) h p)
  | _                     => true
  end.

Lemma red_popr_hat_fit : (pl, pr : part) (zvalid pl pr) ->
  (qa : qarity) (fitqa (get_hat pr) qa) -> (red_popr_hat pr) ->
  (arity (edge (iter (2) face (edge (iter (size_part pl) face x0))))) = qa.
Proof.
Move=> pl; Case=> // [s h pr|h f1 pr|h f1 f2 pr|h f1 f2 f3 pr].
  Apply: (red_pcons_fit (updatePh s)).
  Apply: (red_pcons_fit (updateP6h f1)).
  Apply: (red_pcons_fit (updateP7h f1 f2)).
  Apply: (red_pcons_fit (updateP8h f1 f2 f3)).
Qed.

Definition red_popl_spoke [pl, pr : part] : bool :=
  if pl is (Pcons s h _) then (red_pcons [s'](Pcons s' h) s pr) else true.

Lemma red_popl_spoke_fit : (pl, pr : part) (zvalid pl pr) ->
  (qa : qarity) (fitqa (get_spoke pl) qa) -> (red_popl_spoke pl pr) ->
  (arity (node (iter (size_part pl) face x0))) = qa.
Proof.
By Case=> // [s h pl|h f1 pl|h f1 f2 pl|h f1 f2 f3 pl] pr;
  Rewrite: /zvalid /= Dnf; Try Apply: (red_pcons_fit (updatePs h));
  Move/zvalid_fit; Rewrite: fitp_catrev /=;
  Case/and3P; Clear; Case/eqP; Clear; Case.
Qed.

Definition red_popl_hat [pl, pr : part] : bool :=
  Cases pl of
    (Pcons s h _)         => (red_pcons [r](Pcons s r) h pr)
  | (Pcons6 h f1 _)       => (red_pcons [r](Pcons6 r f1) h pr)
  | (Pcons7 h f1 f2 _)    => (red_pcons [r](Pcons7 r f1 f2) h pr)
  | (Pcons8 h f1 f2 f3 _) => (red_pcons [r](Pcons8 r f1 f2 f3) h pr)
  | _                     => true
  end.

Lemma red_popl_hat_fit : (pl, pr : part) (zvalid pl pr) ->
  (qa : qarity) (fitqa (get_hat pl) qa) -> (red_popl_hat pl pr) ->
  (arity (edge (iter (2) face (node (iter (size_part pl) face x0))))) = qa.
Proof.
Case=> //= [s h|h f1|h f1 f2|h f1 f2 f3] pl pr; Rewrite: Dnf /zvalid /=.
Apply: (red_pcons_fit (updatePh ?)).
Apply: (red_pcons_fit (updateP6h ?)).
Apply: (red_pcons_fit (updateP7h ? ?)).
Apply: (red_pcons_fit (updateP8h ? ? ?)).
Qed.

Definition red_popl_fan1l [pl, pr : part] : bool :=
  Cases pl of
    (Pcons6 h f1 _)       => (red_pcons [r](Pcons6 h r) f1 pr)
  | (Pcons7 h f1 f2 _)    => (red_pcons [r](Pcons7 h f1 r) f2 pr)
  | (Pcons8 h f1 f2 f3 _) => (red_pcons [r](Pcons8 h f1 f2 r) f3 pr)
  | _                     => true
  end.

Definition red_popl_fan2l [pl, pr : part] : bool :=
  Cases pl of
    (Pcons7 h f1 f2 _)    => (red_pcons [r](Pcons7 h r f2) f1 pr)
  | (Pcons8 h f1 f2 f3 _) => (red_pcons [r](Pcons8 h f1 r f3) f2 pr)
  | _                     => true
  end.

Definition red_popl_fan3l [pl, pr : part] : bool :=
  Cases pl of
    (Pcons8 h f1 f2 f3 _) => (red_pcons [r](Pcons8 h r f2 f3) f1 pr)
  | _                     => true
  end.

Definition red_popl_fan1r [pl, pr : part] : bool :=
  Cases pl of
    (Pcons6 h f1 _)       => (red_pcons [r](Pcons6 h r) f1 pr)
  | (Pcons7 h f1 f2 _)    => (red_pcons [r](Pcons7 h r f2) f1 pr)
  | (Pcons8 h f1 f2 f3 _) => (red_pcons [r](Pcons8 h r f2 f3) f1 pr)
  | _                     => true
  end.

Definition red_popl_fan2r [pl, pr : part] : bool :=
  Cases pl of
    (Pcons7 h f1 f2 _)    => (red_pcons [r](Pcons7 h f1 r) f2 pr)
  | (Pcons8 h f1 f2 f3 _) => (red_pcons [r](Pcons8 h f1 r f3) f2 pr)
  | _                     => true
  end.

Definition red_popl_fan3r [pl, pr : part] : bool :=
  Cases pl of
    (Pcons8 h f1 f2 f3 _) => (red_pcons [r](Pcons8 h f1 f2 r) f3 pr)
  | _                     => true
  end.

Lemma red_popl_fan1l_fit : (pl, pr : part) (zvalid pl pr) ->
  (qa : qarity) (fitqa (get_fan1l pl) qa) -> (red_popl_fan1l pl pr) ->
  (arity (zdart (Zpart Zfan1l pl pr))) = qa.
Proof.
Case=> // [h f1|h f1 f2|h f1 f2 f3] pl pr;
  Rewrite: /zvalid /= ; Move=> H; Move: (zvalid_fit H) H;
  Rewrite: fitp_catrev /=; Case/and3P=> [_ Dn _];
  Rewrite: /zmove /= Dnf (Dfn Dn) /= ?Eface arity_face.
Apply: (red_pcons_fit (updateP6f1 ?)).
Apply: (red_pcons_fit (updateP7f2 ? ?)).
Apply: (red_pcons_fit (updateP8f3 ? ? ?)).
Qed.

Lemma red_popl_fan2l_fit : (pl, pr : part) (zvalid pl pr) ->
  (qa : qarity) (fitqa (get_fan2l pl) qa) -> (red_popl_fan2l pl pr) ->
  (arity (zdart (Zpart Zfan2l pl pr))) = qa.
Proof.
Case=> // [h f1 f2|h f1 f2 f3] pl pr;
  Rewrite: /zvalid /= ; Move=> H; Move: (zvalid_fit H) H;
  Rewrite: fitp_catrev /=; Case/and3P=> [_ Dn _];
  Rewrite: /zmove /= Dnf (Dfn Dn) /= ?Eface arity_face.
Apply: (red_pcons_fit (updateP7f1 ? ?)).
Apply: (red_pcons_fit (updateP8f2 ? ? ?)).
Qed.

Lemma red_popl_fan3l_fit : (pl, pr : part) (zvalid pl pr) ->
  (qa : qarity) (fitqa (get_fan3l pl) qa) -> (red_popl_fan3l pl pr) ->
  (arity (zdart (Zpart Zfan3l pl pr))) = qa.
Proof.
Case=> // [h f1 f2 f3] pl pr;
  Rewrite: /zvalid /= ; Move=> H; Move: (zvalid_fit H) H;
  Rewrite: fitp_catrev /=; Case/and3P=> [_ Dn _];
  Rewrite: /zmove /= Dnf (Dfn Dn) /= ?Eface arity_face.
Apply: (red_pcons_fit (updateP8f1 ? ? ?)).
Qed.

Lemma red_popl_fan1r_fit : (pl, pr : part) (zvalid pl pr) ->
  (qa : qarity) (fitqa (get_fan1r pl) qa) -> (red_popl_fan1r pl pr) ->
  (arity (zdart (Zpart Zfan1r pl pr))) = qa.
Proof.
Case=> // [h f1|h f1 f2|h f1 f2 f3] pl pr; Rewrite: /zvalid /= /zmove /= Dnf. 
Apply: (red_pcons_fit (updateP6f1 ?)).
Apply: (red_pcons_fit (updateP7f1 ? ?)).
Apply: (red_pcons_fit (updateP8f1 ? ? ?)).
Qed.

Lemma red_popl_fan2r_fit : (pl, pr : part) (zvalid pl pr) ->
  (qa : qarity) (fitqa (get_fan2r pl) qa) -> (red_popl_fan2r pl pr) ->
  (arity (zdart (Zpart Zfan2r pl pr))) = qa.
Proof.
Case=> // [h f1 f2|h f1 f2 f3] pl pr; Rewrite: /zvalid /= /zmove /= Dnf. 
Apply: (red_pcons_fit (updateP7f2 ? ?)).
Apply: (red_pcons_fit (updateP8f2 ? ? ?)).
Qed.

Lemma red_popl_fan3r_fit : (pl, pr : part) (zvalid pl pr) ->
  (qa : qarity) (fitqa (get_fan3r pl) qa) -> (red_popl_fan3r pl pr) ->
  (arity (zdart (Zpart Zfan3r pl pr))) = qa.
Proof.
Case=> // [h f1 f2 f3] pl pr; Rewrite: /zvalid /= /zmove /= Dnf. 
Apply: (red_pcons_fit (updateP8f3 ? ? ?)).
Qed.

Definition red_pop [zp : zpart] : bool :=
  Cases zp of
    (Zpart Zhubl  pl pr) => (red_popl_spoke pl pr)
  | (Zpart Zhubr  pl pr) => (red_popr_spoke pr)
  | (Zpart Zhatl  pl pr) => (red_popl_spoke pl pr)
  | (Zpart Zhat   pl pr) => (red_popr_hat pr)
  | (Zpart Zhatr  pl pr) => (red_popr_spoke pr)
  | (Zpart Zfan0l pl pr) => (red_popr_hat pr)
  | (Zpart Zfan1l pl pr) => (red_popl_fan1l pl pr)
  | (Zpart Zfan2l pl pr) => (red_popl_fan2l pl pr)
  | (Zpart Zfan3l pl pr) => (red_popl_fan3l pl pr)
  | (Zpart Zfan0r pl pr) => (red_popl_hat pl pr)
  | (Zpart Zfan1r pl pr) => (red_popl_fan1r pl pr)
  | (Zpart Zfan2r pl pr) => (red_popl_fan2r pl pr)
  | (Zpart Zfan3r pl pr) => (red_popl_fan3r pl pr)
  | _ => true
  end.

Lemma red_pop_fit : (zp : zpart) (zpvalid zp) -> 
  (qa : qarity) (fitqa (zrange zp) qa) -> (red_pop zp) -> (arity (zdart zp)) = qa.
Proof.
Case; Case=> //= [] pl pr; Rewrite: /zmove /=; Try Apply: (!red_popl_spoke_fit).
By Move=> _; Rewrite: arity_iter_face Hx0n /hub_range /nhub; Case ahub; Case.
Rewrite: Dn2 arity_face; Apply: (!red_popr_spoke_fit).
Rewrite: -Dnf !Dn2 arity_face; Apply: (!red_popr_hat_fit).
Rewrite: -arity_face Enode; Apply: (!red_popl_spoke_fit).
Rewrite: Dn2 !arity_face; Apply: (!red_popr_spoke_fit).
Rewrite: De2 -Dnf !Dn2 !arity_face; Apply: (!red_popr_hat_fit).
Apply: (!red_popl_fan1l_fit).
Apply: (!red_popl_fan2l_fit).
Apply: (!red_popl_fan3l_fit).
Apply: (!red_popl_hat_fit).
Apply: (!red_popl_fan1r_fit).
Apply: (!red_popl_fan2r_fit).
Apply: (!red_popl_fan3r_fit).
Qed.

Fixpoint fitqzp [zp : zpart; q : question] : bool :=
  Cases q of
    Qask0 =>
    true
  | (Qask1 qa) =>
    (fitqa (zrange zp) qa)
  | (QaskL qa ql) =>
    if (fitqa (zrange zp) qa) then (fitqzp (zstepLt zp) ql) else false
  | (QaskR qa qr) =>
    if (fitqa (zrange zp) qa) then (fitqzp (zstepRt zp) qr) else false
  | (QaskLR qa ql qr) =>
    if (fitqa (zrange zp) qa) then
      if (fitqzp (zstepL zp) ql) then (fitqzp (zstepR zp) qr) else false
    else false
  | (QaskLL qa ql) =>
    let zpl = (zstepL zp) in
    if (fitqa (zrange zpl) qa) then (fitqzp (zstepL zpl) ql) else false
  | (QaskRR qa qr) =>
    let zpr = (zstepR zp) in
    if (fitqa (zrange zpr) qa) then (fitqzp (zstepR zpr) qr) else false
  end.

Fixpoint red_popqzp [zp : zpart; q : question] : bool :=
  Cases q of
    Qask0 =>
    true
  | (Qask1 _) =>
    (red_pop zp)
  | (QaskL qa ql) =>
    (andb (red_pop zp) (red_popqzp (zstepLt zp) ql))
  | (QaskR qa qr) =>
    (andb (red_pop zp) (red_popqzp (zstepRt zp) qr))
  | (QaskLR qa ql qr) =>
    (and3b (red_pop zp) (red_popqzp (zstepL zp) ql) (red_popqzp (zstepR zp) qr))
  | (QaskLL qa ql) =>
    let zpl = (zstepL zp) in (andb (red_pop zpl) (red_popqzp (zstepL zpl) ql))
  | (QaskRR qa qr) =>
    let zpr = (zstepR zp) in (andb (red_pop zpr) (red_popqzp (zstepR zpr) qr))
  end.

Lemma fitqzp_proper : (zp : zpart; q : question)
  (fitqzp zp q) -> Qask0 = q \/ (zproper zp).
Proof.
By Move=> zp q; Case Dq: q; Auto; Move=> Hzp; Right; Case: zp Hzp; Case.
Qed.

Lemma fitqzp_fit : (zp : zpart; q : question)
  (fitqzp zp q) -> (red_popqzp zp q) -> (zpvalid zp) -> (fitq (zdart zp) q).
Proof.
Move=> zp q; Elim: q zp => //=.
Move=> qa zp Hqa Hzpp Hzp.
  By Apply/eqP; Rewrite: /= (red_pop_fit Hzp Hqa Hzpp).
Move=> qa ql Hrec zp.
  Case Hqa: (fitqa (zrange zp) qa) => [] // Hql; Move/andP=> [Hzpp Hzppl] Hzp.
  Def: Dqa := (red_pop_fit Hzp Hqa Hzpp); Rewrite: /fitq /= eqseq_adds Dqa set11.
  Case: (fitqzp_proper Hql) => [[] | Hzp'] //.
  Rewrite: fitqa_topqa in Hqa; Case/andP: Hqa => [_ Eqa].
  Rewrite: ~{qa Eqa}(eqP Eqa) in Dqa.
  By Rewrite: -zdart_stepLt //; Apply: Hrec => //; Apply zpvalid_stepLt.
Move=> qa qr Hrec zp.
  Case Hqa: (fitqa (zrange zp) qa) => [] // Hqr; Move/andP=> [Hzpp Hzppr] Hzp.
  Def: Dqa := (red_pop_fit Hzp Hqa Hzpp); Rewrite: /fitq /= eqseq_adds Dqa set11.
  Case: (fitqzp_proper Hqr) => [[] | Hzp'] //.
  Rewrite: fitqa_topqa in Hqa; Case/andP: Hqa => [_ Eqa].
  Rewrite: ~{qa Eqa}(eqP Eqa) in Dqa.
  By Rewrite: -zdart_stepRt //; Apply: Hrec => //; Apply zpvalid_stepRt.
Move=> qa ql Hrecl qr Hrecr zp.
  Case Hqa: (fitqa (zrange zp) qa) => //.
  Case Hql: (fitqzp (zstepL zp) ql) => // [] Hqr.
  Move/and3P=> [Hzpp Hzppl Hzppr] Hzp.
  Rewrite: /fitq /= eqseq_adds fitq_cat (red_pop_fit Hzp Hqa Hzpp) set11 /=.
  Apply/andP; Split.
    Case: (fitqzp_proper Hql) => [[] | Hzpl] //.
    By Rewrite: -zdart_stepL //; Apply: Hrecl => //; Apply zpvalid_stepL.
  Case: (fitqzp_proper Hqr) => [[] | Hzpr] //.
  By Rewrite: -zdart_stepR //; Apply: Hrecr => //; Apply: zpvalid_stepR.
Move=> qa ql Hrec zp; Pose zpl := (zstepL zp).
  Case Hqa: (fitqa (zrange zpl) qa) => [] // Hql; Move/andP=> [Hzplp Hzpllp] Hzp.
  Rewrite: /fitq /= eqseq_adds -arity_face Enode.
  Rewrite: -zdart_stepL // -/zpl; RightBy Case: {}zpl Hqa; Case.
  Move/zpvalid_stepL: Hzp => Hzpl; Rewrite: (red_pop_fit Hzpl Hqa Hzplp) set11.
  Case: (fitqzp_proper Hql) => [[] | Hzpll] //.
  By Rewrite: -zdart_stepL //; Apply: Hrec => //; Apply zpvalid_stepL.
Move=> qa ql Hrec zp; Pose zpr := (zstepR zp).
  Case Hqa: (fitqa (zrange zpr) qa) => [] // Hqr; Move/andP=> [Hzprp Hzprrp] Hzp.
  Rewrite: /fitq /= eqseq_adds.
  Rewrite: -zdart_stepR // -/zpr; RightBy Case: {}zpr Hqa; Case.
  Move/zpvalid_stepR: Hzp => Hzpr; Rewrite: (red_pop_fit Hzpr Hqa Hzprp) set11.
  Case: (fitqzp_proper Hqr) => [[] | Hzprr] //.
  By Rewrite: -zdart_stepR //; Apply: Hrec => //; Apply zpvalid_stepR.
Qed.

Section RedQztLeaf.

Variables zp1, zp2, zp3 : zpart.

Fixpoint red_qzt_leaf [qtl : quiz_tree] : bool :=
  Cases qtl of
    (QztLeaf q1 q2 q3 qtl') =>
      if (fitqzp zp3 q3) then
        if (fitqzp zp2 q2) then
          if (fitqzp zp1 q1) then
             (and3b (red_popqzp zp1 q1) (red_popqzp zp2 q2) (red_popqzp zp3 q3))
          else (red_qzt_leaf qtl')
        else (red_qzt_leaf qtl')
      else (red_qzt_leaf qtl')
  | _ => false
  end.

Lemma red_qzt_leaf_fit : (qtl : quiz_tree) (red_qzt_leaf qtl) -> 
       (qzt_proper qtl)
  /\   (x : g)
         (zpfit (qstepR x) zp1)               -> (zpvalid zp1) ->
         (zpfit (qstepR (node x)) zp2)        -> (zpvalid zp2) ->
         (zpfit (qstepR (node (node x))) zp3) -> (zpvalid zp3) ->
       ~ (negb (qzt_fitl x qtl)).
Proof.
Move=> qtl Hqtl; Split; LeftBy Case: qtl Hqtl.
Move=> x Hxzp1 Hzp1 Hxzp2 Hzp2 Hxzp3 Hzp3; Case/idP.
Elim: qtl Hqtl => //= [q1 q2 q3 qtl Hrec].
Case Hqtl: (red_qzt_leaf qtl); LeftBy Rewrite: Hrec ?orbT.
Case Hq3: (fitqzp zp3 q3) => //; Case Hq2: (fitqzp zp2 q2) => //.
Case Hq1: (fitqzp zp1 q1) => //; Move/and3P=> [Hzp1p Hzp2p Hzp3p].
Apply/orP; Left; Apply/and3P; Split.
    Case: (fitqzp_proper Hq1) => [[] | Hzp1'] //; Rewrite: -Hxzp1 //.
    By Apply: fitqzp_fit.
  Case: (fitqzp_proper Hq2) => [[] | Hzp2'] //; Rewrite: -Hxzp2 //.
  By Apply: fitqzp_fit.
Case: (fitqzp_proper Hq3) => [[] | Hzp3'] //; Rewrite: -Hxzp3 //.
By Apply: fitqzp_fit.
Qed.

End RedQztLeaf.

Definition qzt_getr [r : prange; qt : quiz_tree] : quiz_tree :=
  if qt is (QztNode qt5 qt6 qt7 qt8) then
      Cases r of
      Pr55 => qt5
    | Pr56 => qt6
    | Pr66 => qt6
    | Pr57 => qt7
    | Pr67 => qt7
    | Pr77 => qt7
    | Pr58 => qt8
    | Pr68 => qt8
    | Pr78 => qt8
    | Pr88 => qt8
    |    _ => QztNil
    end
  else QztNil.

Lemma qzt_getr_fit : (r : prange; qt' : quiz_tree) (qzt_proper (qzt_getr r qt')) ->
  let qa = (topqa r) in
  (and3 (fitqa r qa) (qzt_get1 qa qt') = (qzt_getr r qt') (qzt_proper qt')).
Proof.
By Move=> r; Case=> // [qt5 qt6 qt7 qt8]; Case: r => //; Split.
Qed.

Lemma redpart_no_qzt_fitl : (y : g; qa1, qa2, qa3 : qarity)
  (arity y) = qa1 -> (arity (node y)) = qa2 -> (arity (node (node y))) = qa3 ->
  (negb (qzt_fitl y (qzt_get3 qa1 qa2 qa3 qt))).
Proof.
Move=> y qa1 qa2 qa3 Dqa1 Dqa2 Dqa3; Move: (Hqt y).
By Rewrite: /qzt_fit /qzt_fita Dqa1 Dqa2 Dqa3 !qarity_of_qarity !set11.
Qed.

Fixpoint red_zpart_rec [zp : zpart; d : nat] : bool :=
  if d is (S d') then 
    let zp' = (zshiftr Zhub zp) in
    let (_, pl, pr) = zp in
    let s = (get_spoke pr) in
    let sqt = (qzt_getr s (qzt_truncate qt)) in
    if if (qzt_proper sqt) then
      let (_, pl', pr') = zp' in
      let sl = (get_spoke pl) in
      if (red_qzt_leaf (Zpart Zhubr pl' pr') (zshiftl Zhubl zp) (Zpart Zhat pl pr)
            (qzt_getr s (qzt_getr sl (qzt_get1 ahub qt))))
        then (andb (red_popr_spoke pr) (red_popl_spoke pl pr)) else
      if (red_qzt_leaf (Zpart (zfanLt pr) pl' pr') zp (Zpart (zfanRt pl) pl pr)
         (qzt_getr (get_hat pr) (qzt_getr sl sqt)))
         then (and3b (red_popr_hat pr) (red_popl_spoke pl pr) (red_popr_spoke pr))
      else let zpnil = (Zpart Znil pl' pr') in Cases pr of
        (Pcons Pr55 h _) =>
        if (red_qzt_leaf (Zpart Zhatr pl' pr') (Zpart Zhatl pl pr) zpnil
              (qzt_getr (get_hat pr') (qzt_getr h sqt)))
          then (andb (red_popr_hat pr') (red_popr_hat pr)) else false
      | (Pcons6 h f1 _) =>
         if (red_qzt_leaf (Zpart Zfan0l pl' pr') (Zpart Zhatl pl pr) zpnil
               (qzt_getr f1 (qzt_getr h sqt)))
           then (andb (red_popl_fan1r pl' pr') (red_popr_hat pr)) else
         if (red_qzt_leaf (Zpart Zhatr pl' pr') (Zpart Zfan0r pl' pr') zpnil
               (qzt_getr (get_hat pr') (qzt_getr f1 sqt)))
           then (andb (red_popr_hat pr') (red_popl_fan1r pl' pr')) else false
      | (Pcons7 h f1 f2 _) =>
         if (red_qzt_leaf (Zpart Zfan1l pl' pr') (Zpart Zhatl pl pr) zpnil
               (qzt_getr f1 (qzt_getr h sqt)))
           then (andb (red_popl_fan1r pl' pr') (red_popr_hat pr)) else
         if (red_qzt_leaf (Zpart Zfan0l pl' pr') (Zpart Zfan0r pl' pr') zpnil
               (qzt_getr f2 (qzt_getr f1 sqt)))
           then (andb (red_popl_fan2r pl' pr') (red_popl_fan1r pl' pr')) else
         if (red_qzt_leaf (Zpart Zhatr pl' pr') (Zpart Zfan1r pl' pr') zpnil
               (qzt_getr (get_hat pr') (qzt_getr f2 sqt)))
           then (andb (red_popr_hat pr') (red_popl_fan2r pl' pr')) else false
      | (Pcons8 h f1 f2 f3 _) =>
         if (red_qzt_leaf (Zpart Zfan2l pl' pr') (Zpart Zhatl pl pr) zpnil
               (qzt_getr f1 (qzt_getr h sqt)))
           then (andb (red_popl_fan1r pl' pr') (red_popr_hat pr)) else
         if (red_qzt_leaf (Zpart Zfan1l pl' pr') (Zpart Zfan0r pl' pr') zpnil
               (qzt_getr f2 (qzt_getr f1 sqt)))
           then (andb (red_popl_fan2r pl' pr') (red_popl_fan1r pl' pr')) else
         if (red_qzt_leaf (Zpart Zfan0l pl' pr') (Zpart Zfan1r pl' pr') zpnil
               (qzt_getr f3 (qzt_getr f2 sqt)))
           then (andb (red_popl_fan3r pl' pr') (red_popl_fan2r pl' pr')) else
         if (red_qzt_leaf (Zpart Zhatr pl' pr') (Zpart Zfan2r pl' pr') zpnil
               (qzt_getr (get_hat pr') (qzt_getr f3 sqt)))
           then (andb (red_popr_hat pr') (red_popl_fan3r pl' pr')) else false
      | _ => false
      end else false
      then true
    else (red_zpart_rec zp' d')
  else false.

Definition red_zpart : bool := (red_zpart_rec (Zpart Zhub p0ll p0lr) nhub).

Lemma not_red_zpart : (negb red_zpart).
Proof.
Apply negbI; Rewrite: /red_zpart.
Step Hp0l: (ltn (1) (size_part p0l)).
  By Do 3 Apply ltnW; Rewrite: Dp0l size_rev_part Ep0r -Hx0n.
Step Hpl: (ltn (0) (size_part p0ll)) By Rewrite: size_drop_part -ltn_lt0sub.
Step Hpr: (ltn nhub (size_part p0lr)).
  By Rewrite: -add1n /shift_part size_cat_part Ep0r leq_add2r; Case: {}p0l Hp0l.
Elim: {}nhub {}p0ll {}p0lr Hpl Hpr zvalid_initl => // [d Hrec] pl pr Hpl Hpr Hzp.
Pose pl' := (shift_part pr pl); Pose pr' := (drop_part (1) pr).
Pose zp := [zi](Zpart zi pl pr); Pose zp' := [zi](Zpart zi pl' pr').
Rewrite: -/(zp Zhub) {zp}lock /= -{1 (locked zp)}lock {1}/zp.
Step Dzp': (zi, zi' : zpart_loc) (zshiftr zi' (zp zi)) = (zp' zi').
  By Move=> *; Rewrite: /zp zshiftr_eq //; Apply: leq_trans Hpr.
Step Hzp': (zpvalid (zp' Zhub)) By Rewrite: -(Dzp' Zhub); Apply: zpvalid_shiftr.
Rewrite: -lock Dzp' {1}/zp'; Move: (frefl zp) (frefl zp'); Rewrite: {1}/zp {1}/zp'.
Move=> H H'; Rewrite: !~H !~H'; Pose x := (iter (size_part pl) face x0).
Step Ezp: (zi : zpart_loc) (zdart (zp zi)) = (zmove_def zi x) By Done.
Step Ezp': (zi : zpart_loc) (zdart (zp' zi)) = (zmove_def zi (face x)).
  By Move=> *; Rewrite: -(Dzp' Zhub) zdart_shiftr //.
Def: Ezp'' := Ezp'; Rewrite: /zp' in Ezp''.
Def: Dx' := (Ezp' Zhub); Rewrite: /= /zmove /= in Dx'.
Step Hpl': (ltn (0) (size_part pl')).
  By Apply: (leq_trans Hpl); Rewrite: /pl' /shift_part size_cat_part leq_addl.
Step Hpr': (ltn d (size_part pr')) By Move: Hpr; Rewrite: /pr'; Case pr.
Apply cases_of_if; RightBy Clear; Rewrite: /zp'; EAuto.
Case Hsqt: (qzt_proper (qzt_getr (get_spoke pr) (qzt_truncate qt))) => //.
Case: (qzt_getr_fit Hsqt) Hsqt => [Hs [] _]; Move/qzt_get1_truncate; Case/esym.
Case; Apply cases_of_if; [Case/red_qzt_leaf_fit | Clear].
  Case/qzt_getr_fit=> [_ []]; Case/qzt_getr_fit=> [Hsl [] _].
  Move=> Hssl; Apply/andP=> [[Hsp Hslp]].
  Case: {Hssl}(Hssl (zdart (zp Zhub))) => //; Rewrite: /zpfit.
    By Clear; Rewrite: Ezp' Ezp /qstepR /= Dnf.
    By Clear; Rewrite: zdart_shiftl.
    By Apply zpvalid_shiftl.
  Apply: redpart_no_qzt_fitl.
      By Rewrite: Ezp /= /x arity_iter_face.
    By Rewrite: -(red_popl_spoke_fit Hzp).
  By Rewrite: -(red_popr_spoke_fit Hzp) // Dn2 arity_face.
Apply cases_of_if; [Case/red_qzt_leaf_fit | Clear].
  Case/qzt_getr_fit=> [Hh []]; Case/qzt_getr_fit=> [Hsl [] _].
  Move=> Hhssl; Apply/and3P=> [[Hhp Hslp Hsp]].
  Def: Ds := (red_popr_spoke_fit Hzp Hs Hsp).
  Def: Dsl := (red_popl_spoke_fit Hzp Hsl Hslp); Rewrite: -/x in Ds Dsl.
  Case: {Hhssl}(Hhssl (zdart (zp Zhatr))) => //; Rewrite: /zpfit.
        Rewrite: -(Dzp' Zhatr); Apply: (!zdart_stepRt (zp Zhatr)) => //.
        By Rewrite: /zpfit_top Ezp /= Dn2 !arity_face.
      By Rewrite: !Ezp /qstepR /= Eface Dn3.
    Rewrite: (Ezp Zhatr) /= Dnf; Apply: (!zdart_stepLt (zp Zhatl)) => //.
    By Rewrite: /zpfit_top Ezp /= -arity_face Enode.
  Apply: redpart_no_qzt_fitl.
      By Rewrite: Ezp /= Dn2 !arity_face.
    By Rewrite: Ezp /= Dnf -arity_face Enode.
  By Rewrite: Ezp /= !Dn2 arity_face -(red_popr_hat_fit Hzp).
Move: (erefl (topqa (get_spoke pr))) {Hs}(red_popr_spoke_fit Hzp Hs).
Case Dpr: {1 3 4 5}pr => //= [s h p|h f1 p|h f1 f2 p|h f1 f2 f3 p] [];
  Try Case: s Dpr => //= [] Dpr;
  Move=> H; Move: {H}(introT eqP (H (erefl ?))) => Ds;
  Rewrite: -/x eqd_sym in Ds; Move/Dfn: {}Ds => Es; Simpl in Es.
Apply cases_of_if; [Case/red_qzt_leaf_fit | Done].
  Case/qzt_getr_fit=> [Hhr []]; Case/qzt_getr_fit=> [Hh [] _].
  Move=> Hhhr; Apply/andP=> [[Hhr' Hh']].
  Case: {Hhhr}(Hhhr (iter (3) face (edge x))); Rewrite: /zpfit //.
      By Clear; Rewrite: Ezp' /= /qstepR Dnf {1 (edge x)}Es !Dnf -Dn2 Dnf.
    By Clear; Rewrite: Ezp /qstepR /= Dnf De2 Dnf Dn2.
  Apply: redpart_no_qzt_fitl.
      By Rewrite: /= !arity_face (eqP Ds).
    By Rewrite: /= Dnf -(red_popr_hat_fit Hzp) // Dpr.
  Rewrite: -(red_popr_hat_fit Hzp') //= Dx' -!Dn2 !Dnf Es Dnf -Dn2.
  By Symmetry; Rewrite: Dnf -2!arity_face Enode -!Dn2 Dnf.
Apply cases_of_if; [Case/red_qzt_leaf_fit | Clear].
  Case/qzt_getr_fit=> [Hf1 []]; Case/qzt_getr_fit=> [Hh [] _].
  Move=> Hhf1; Apply/andP=> [[Hf1' Hh']].
  Case: {Hhf1}(Hhf1 (iter (3) face (edge x))); Rewrite: /zpfit //.
    By Clear; Rewrite: Ezp' /qstepR /= De2 Dnf {1 (edge x)}Es Eface Dnf -Dn2 Dnf.
    By Clear; Rewrite: Ezp /qstepR /= Eface Dnf Dn2.
  Apply: redpart_no_qzt_fitl.
      By Rewrite: /= !arity_face -(eqP Ds).
    By Rewrite: /= Dnf -(red_popr_hat_fit Hzp) // Dpr.
  Rewrite: -(red_popl_fan1r_fit Hzp') // ?Ezp'' /pl' ?Dpr //=.
  By Rewrite: Dn2 arity_face Dnf.  
Apply cases_of_if; [Case/red_qzt_leaf_fit | Done].
  Case/qzt_getr_fit=> [Hhr []]; Case/qzt_getr_fit=> [Hf1 [] _].
  Move=> Hf1hr; Apply/andP=> [[Hhr' Hf1']].
  Case: {Hf1hr}(Hf1hr (iter (4) face (edge x))); Rewrite: /zpfit //.
    By Clear; Rewrite: Ezp' /qstepR /= Dnf {1 (edge x)}Es Dnf -Dn2 Dnf.
    By Clear; Rewrite: Ezp' /qstepR /= Dnf Eface Dnf.
  Apply: redpart_no_qzt_fitl; Rewrite: -?zdart_node //=.
      By Rewrite: /= !arity_face -(eqP Ds).
    By Rewrite: -(red_popl_fan1r_fit Hzp') // ?Ezp'' /pl' ?Dpr //= !Dnf.
  Rewrite: -(red_popr_hat_fit Hzp') //= Dx' -!Dn2 !Dnf Es Dnf -Dn2.
  By Symmetry; Rewrite: Dnf -2!arity_face Enode -!Dn2 Dnf.
Apply cases_of_if; [Case/red_qzt_leaf_fit | Clear].
  Case/qzt_getr_fit=> [Hf1 []]; Case/qzt_getr_fit=> [Hh [] _].
  Move=> Hhf1; Apply/andP=> [[Hf1' Hh']].
  Case: {Hhf1}(Hhf1 (iter (3) face (edge x))); Rewrite: /zpfit //.
    By Clear; Rewrite: Ezp' /qstepR /= De2 Dnf {1 (edge x)}Es !Eface Dnf -Dn2 Dnf.
    By Clear; Rewrite: Ezp /qstepR /= Eface Dnf Dn2.
  Apply: redpart_no_qzt_fitl.
      By Rewrite: /= !arity_face -(eqP Ds).
    By Rewrite: /= Dnf -(red_popr_hat_fit Hzp) // Dpr.
  Rewrite: -(red_popl_fan1r_fit Hzp') // ?Ezp'' /pl' ?Dpr //=.
  By Rewrite: Dn2 arity_face Dnf.  
Apply cases_of_if; [Case/red_qzt_leaf_fit | Clear].
  Case/qzt_getr_fit=> [Hf2 []]; Case/qzt_getr_fit=> [Hf1 [] _].
  Move=> Hf1f2; Apply/andP=> [[Hf2' Hf1']].
  Case: {Hf1f2}(Hf1f2 (iter (4) face (edge x))); Rewrite: /zpfit //.
    By Clear; Rewrite: Ezp' /qstepR /= Dnf {1 (edge x)}Es !Eface -Dn2 Dnf.
    By Clear; Rewrite: Ezp' /qstepR /= Dnf Eface Dnf.
  Apply: redpart_no_qzt_fitl; Rewrite: -?zdart_node //=.
      By Rewrite: /= !arity_face -(eqP Ds).
    By Rewrite: -(red_popl_fan1r_fit Hzp') // ?Ezp'' /pl' ?Dpr //= !Dnf.
  Rewrite: -(red_popl_fan2r_fit Hzp') // ?Ezp'' /pl' ?Dpr //= Dn2 !Dnf.
  By Rewrite arity_face.
Apply cases_of_if; [Case/red_qzt_leaf_fit | Done].
  Case/qzt_getr_fit=> [Hhr []]; Case/qzt_getr_fit=> [Hf2 [] _].
  Move=> Hf2hr; Apply/andP=> [[Hhr' Hf2']].
  Case: {Hf2hr}(Hf2hr (iter (5) face (edge x))); Rewrite: /zpfit //.
    By Clear; Rewrite: Ezp' /qstepR /= Dnf {1 (edge x)}Es Dnf -Dn2 Dnf.
    By Clear; Rewrite: Ezp' /qstepR /= Dnf Eface Dnf.
  Apply: redpart_no_qzt_fitl; Rewrite: -?zdart_node //=.
      By Rewrite: /= !arity_face -(eqP Ds).
    By Rewrite: -(red_popl_fan2r_fit Hzp') // ?Ezp'' /pl' ?Dpr //= !Dnf.
  Rewrite: -(red_popr_hat_fit Hzp') //= Dx' -!Dn2 !Dnf Es Dnf -Dn2.
  By Symmetry; Rewrite: Dnf -2!arity_face Enode -!Dn2 Dnf.
Apply cases_of_if; [Case/red_qzt_leaf_fit | Clear].
  Case/qzt_getr_fit=> [Hf1 []]; Case/qzt_getr_fit=> [Hh [] _].
  Move=> Hhf1; Apply/andP=> [[Hf1' Hh']].
  Case: {Hhf1}(Hhf1 (iter (3) face (edge x))); Rewrite: /zpfit //.
    By Clear; Rewrite: Ezp' /qstepR /= De2 Dnf {1 (edge x)}Es !Eface Dnf -Dn2 Dnf.
    By Clear; Rewrite: Ezp /qstepR /= Eface Dnf Dn2.
  Apply: redpart_no_qzt_fitl.
      By Rewrite: /= !arity_face -(eqP Ds).
    By Rewrite: /= Dnf -(red_popr_hat_fit Hzp) // Dpr.
  Rewrite: -(red_popl_fan1r_fit Hzp') // ?Ezp'' /pl' ?Dpr //=.
  By Rewrite: Dn2 arity_face Dnf.  
Apply cases_of_if; [Case/red_qzt_leaf_fit | Clear].
  Case/qzt_getr_fit=> [Hf2 []]; Case/qzt_getr_fit=> [Hf1 [] _].
  Move=> Hf1f2; Apply/andP=> [[Hf2' Hf1']].
  Case: {Hf1f2}(Hf1f2 (iter (4) face (edge x))); Rewrite: /zpfit //.
    By Clear; Rewrite: Ezp' /qstepR /= Dnf {1 (edge x)}Es !Eface -Dn2 Dnf.
    By Clear; Rewrite: Ezp' /qstepR /= Dnf Eface Dnf.
  Apply: redpart_no_qzt_fitl; Rewrite: -?zdart_node //=.
      By Rewrite: /= !arity_face -(eqP Ds).
    By Rewrite: -(red_popl_fan1r_fit Hzp') // ?Ezp'' /pl' ?Dpr //= !Dnf.
  Rewrite: -(red_popl_fan2r_fit Hzp') // ?Ezp'' /pl' ?Dpr //= Dn2 !Dnf.
  By Rewrite arity_face.
Apply cases_of_if; [Case/red_qzt_leaf_fit | Clear].
  Case/qzt_getr_fit=> [Hf3 []]; Case/qzt_getr_fit=> [Hf2 [] _].
  Move=> Hf2f3; Apply/andP=> [[Hf3' Hf2']].
  Case: {Hf2f3}(Hf2f3 (iter (5) face (edge x))); Rewrite: /zpfit //.
    By Clear; Rewrite: Ezp' /qstepR /= Dnf {1 (edge x)}Es !Eface -Dn2 Dnf.
    By Clear; Rewrite: Ezp' /qstepR /= Dnf Eface Dnf.
  Apply: redpart_no_qzt_fitl; Rewrite: -?zdart_node //=.
      By Rewrite: /= !arity_face -(eqP Ds).
    By Rewrite: -(red_popl_fan2r_fit Hzp') // ?Ezp'' /pl' ?Dpr //= !Dnf.
  Rewrite: -(red_popl_fan3r_fit Hzp') // ?Ezp'' /pl' ?Dpr //= Dn2 !Dnf.
  By Rewrite arity_face.
Apply cases_of_if; [Case/red_qzt_leaf_fit | Done].
  Case/qzt_getr_fit=> [Hhr []]; Case/qzt_getr_fit=> [Hf3 [] _].
  Move=> Hf2hr; Apply/andP=> [[Hhr' Hf2']].
  Case: {Hf2hr}(Hf2hr (iter (6) face (edge x))); Rewrite: /zpfit //.
    By Clear; Rewrite: Ezp' /qstepR /= Dnf {1 (edge x)}Es Dnf -Dn2 Dnf.
    By Clear; Rewrite: Ezp' /qstepR /= Dnf Eface Dnf.
  Apply: redpart_no_qzt_fitl; Rewrite: -?zdart_node //=.
      By Rewrite: /= !arity_face -(eqP Ds).
    By Rewrite: -(red_popl_fan3r_fit Hzp') // ?Ezp'' /pl' ?Dpr //= !Dnf.
  Rewrite: -(red_popr_hat_fit Hzp') //= Dx' -!Dn2 !Dnf Es Dnf -Dn2.
  By Symmetry; Rewrite: Dnf -2!arity_face Enode -!Dn2 Dnf.
Qed.

End Zpart.

Fixpoint redpart_rec [d : nat] : part -> bool :=
  [p]if d is (S d') then (red_zpart (redpart_rec d') (rev_part p) p) else false.

End RedpartRec.

(* The bound is mostly to keep Coq from unfolding the recursion too soon. *)
(* There's a logic to it, though : each time we recurse, we pop one       *)
(* prange, there are at most 4 open ranges per sector, and the worst case *)
(* would require a configuration where all but one face is octogonal.     *)
Definition redpart_depth [p : part] := (mult (size_part p) (12)).

Definition redpart [p : part] : bool :=
  let nhub = (size_part p) in let ahub = (qarity_of_nat nhub) in
  (andb nhub =d (ahub :: nat) (redpart_rec ahub (redpart_depth p) p)).

Lemma no_fit_redpart : (p : part) (redpart p) -> (x : g) (negb (exact_fitp x p)).
Proof.
Move=> p; Case/andP; Def: ahub := (qarity_of_nat (size_part p)).
Move/eqP=> Ep Hp x; Apply/idP=> [Hxp]; Case/idPn: Hp; Rewrite: /redpart.
Case: (andP Hxp) Hxp Ep; Case/eqP; Clear.
Elim: (redpart_depth p) x {1 3}p => //= *; EApply not_red_zpart; EAuto.
Qed.

End Redpart.

Unset Implicit Arguments.
