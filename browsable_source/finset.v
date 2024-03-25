(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require tacticext.
Require boolprop.
Require funs.
Require dataset.
Require natprop.
Require seq.

Set Implicit Arguments.

(*   A small theory of data sets of finite cardinal, based on sequences.     *)
(* A finite data set is a data set plus a duplicate-free sequence of all its *)
(* elements. This is equivalent to requiring only a list, and we do give a   *)
(* construction of a finSet from a list, but it is preferable to specify the *)
(* structure of the dataset in general.                                      *)

Record finSet : Type := FinSet {
   element :> dataSet;
   enum : (seq element);
   count_set1_enum : (x : element) (count (set1 x) enum) = (1)
}.

Section SeqFinSet.

Variable d : dataSet; e : (seq d).

Local d' : dataSet := (subData e).

Fixpoint subd_enum [s : (seq d)] : (seq d') :=
  if s is (Adds x s') then
    let s'' = (subd_enum s') in
    if (subdIopt e x) is (Some u) then
      if (s'' u) then s'' else (Adds u s'')
    else s''
  else seq0.

Lemma subd_enumP : (u : d') (count (set1 u) (subd_enum e)) = (1).
Proof.
Move=> [x Hx]; Rewrite: /eqd /= -{(1)}(congr nat_of_bool Hx).
Elim: {1 5 6}e [y; H : (e y)]H => [|y s Hrec] //=.
Case: (subdIoptP e y) => [u _ Du | Hy] Hs;
  RightBy Case: (negP Hy); Apply Hs; Rewrite: setU11.
Def: Hs' := [z; Hz](Hs z (setU1r ? Hz)).
Rewrite: [a](fun_if [s](!count d' a s)) /= (Hrec Hs') /eqd /= Du eqd_sym /setU1. 
Case: (y =P x) => [Dy | _]; RightBy Rewrite: /= add0n if_same.
By Rewrite: -has_set1 has_count /eqd /= Du Dy (Hrec Hs'); Case (s x).
Qed.

Definition SeqFinSet := (FinSet subd_enumP).

End SeqFinSet.

Lemma boolEnumP : (b : boolData) (count (set1 b) (seq2 true false)) = (1).
Proof. By Move=> [|]. Qed.

Canonical Structure boolEnum := (FinSet boolEnumP).

Section FiniteSet.

Variable d : finSet.

Lemma mem_enum : (enum d) =1 d.
Proof. By Move=> x; Rewrite: -has_set1 has_count count_set1_enum. Qed.

Lemma filter_enum : (a : (set d)) (filter a (enum d)) =1 a.
Proof. By Move=> a x; Rewrite: mem_filter /setI andbC mem_enum. Qed.

Lemma uniq_enum : (uniq (enum d)).
Proof.
Step Hs: (x : d) (leq (count (set1 x) (enum d)) (1)).
  By Move=> x; Rewrite: count_set1_enum.
Elim: (enum d) Hs => [|x s Hrec] Hs //=; Apply/andP; Split.
  Rewrite: -has_set1 has_count -ltnNge /=.
  By Apply: leq_trans (Hs x); Rewrite: /= set11 leqnn.
By Apply: Hrec => [y]; Apply: leq_trans (Hs y); Rewrite: /= leq_addl.
Qed.

Section Pick.

Variable a : (set d).

Inductive pick_spec : (option d) -> Set :=
  Pick : (x : d) (a x) -> (pick_spec (Some d x))
| Nopick : a =1 set0 -> (pick_spec (None d)).

Definition pick : (option d) :=
  if (filter a (enum d)) is (Adds x _) then (Some ? x) else (None ?).

Lemma pickP : (pick_spec pick).
Proof.
Rewrite: /pick; Case: (filter a (enum d)) (!filter_enum a) => [|x s] Ha.
  Right; Exact [x](esym (Ha x)).
By Left; Rewrite: -Ha /= setU11.
Qed.

End Pick.

Lemma eq_pick : (a, b : (set d)) a =1 b -> (pick a) = (pick b).
Proof. Move=> a *; Symmetry; Rewrite: /pick -(eq_filter 2!a); Auto. Qed.

Opaque pick.

Section Cardinal.

Definition card [a : (set d)] : nat := (count a (enum d)).

Lemma eq_card : (a, b : (set d)) a =1 b -> (card a) = (card b).
Proof. Exact [a, b; Eab](eq_count Eab ?). Qed.

Lemma card0 : (card set0) = (0). Proof. Exact (count_set0 ?). Qed.

Lemma cardA : (card d) = (size (enum d)). Proof. Exact (count_setA ?). Qed.

Lemma card1 : (x : d) (card (set1 x)) = (1).
Proof. Exact [x](count_set1_enum x). Qed.

Lemma cardUI : (a, b : (set d))
  (addn (card (setU a b)) (card (setI a b))) = (addn (card a) (card b)).
Proof. Exact [a, b](count_setUI a b ?). Qed.

Lemma cardIC : (b, a : (set d))
  (addn (card (setI a b)) (card (setI a (setC b)))) = (card a).
Proof.
By Move=> b a; Apply: (etrans ? (add0n ?)); Rewrite: -cardUI addnC -card0;
  Congr addn; Apply: eq_card => [x]; Rewrite: /setI /setU /setC;
  Case (a x); Case (b x).
Qed.

Lemma cardC : (a : (set d)) (addn (card a) (card (setC a))) = (card d).
Proof. Exact [a](etrans (count_setC a ?) (esym cardA)). Qed.

Lemma cardU1 : (x : d; a : (set d))
  (card (setU1 x a)) = (addn (negb (a x)) (card a)).
Proof.
Move=> x a; Apply: (addn_injr (etrans (cardUI ? ?) (esym ?))).
Rewrite: addnC addnA; Congr addn; Rewrite: -(eq_card 1!(filter a (seq1 x))).
  Simpl; Case: (a x); RightBy Rewrite: /= card0 card1.
  By Rewrite: addnC; Apply: eq_card => [y]; Apply: mem_seq1.
By Move=> y; Rewrite: mem_filter /setI mem_seq1 andbC.
Qed.

Lemma card2 : (x, y : d) (card (set2 x y)) = (S (negb x =d y)).
Proof.
By Move=> x y; Apply: (etrans (cardU1 ? ?)); Rewrite: card1 addn1 eqd_sym.
Qed.

Lemma cardC1 : (x : d) (card (setC1 x)) = (pred (card d)).
Proof. By Move=> x; Rewrite: -(cardC (set1 x)) card1. Qed.

Lemma cardD1 : (x : d; a : (set d))
  (card a) = (addn (a x) (card (setD1 a x))).
Proof.
Move=> x a; Rewrite addnC; Apply: (addn_injr (etrans (cardC a) ?)).
Rewrite: -addnA (negb_intro (a x)) -{(negb (a x))}/(setC a x) -cardU1.
Apply: (esym (etrans (congr (addn ?) ?) (cardC ?))).
By Apply: eq_card => [y]; Rewrite: /setC /setU1 /setD1 negb_andb negb_elim.
Qed.

Lemma max_card : (a : (set d)) (leq (card a) (card d)).
Proof. Move=> a; Rewrite: -(cardC a); Exact (leq_addr ? ?). Qed.

Lemma card_size : (s : (seq d)) (leq (card s) (size s)).
Proof.
Elim=> [|x s Hrec] /=; LeftBy Rewrite card0.
By Rewrite: cardU1; Case (s x); LeftBy Exact (leqW Hrec).
Qed.

Lemma card_uniqPx : (s : (seq d)) (reflect (card s) = (size s) (uniq s)).
Proof.
Move=> s; Elim: s => [|x s Hrec]; LeftBy Left; Exact card0.
Rewrite: /= cardU1 /addn; Case (s x); Simpl.
  By Right; Move=> H; Move: (card_size s); Rewrite: H ltnn.
By Apply: (iffP Hrec); [Move=> [] | Injection=> []].
Qed.

End Cardinal.

Definition set0b [a : (set d)] : bool := (card a) =d (0).
Definition disjoint [a, b : (set d)] : bool := (set0b (setI a b)).
Definition subset [a, b : (set d)] : bool := (disjoint a (setC b)).

Lemma card0_eq : (a : (set d)) (card a) = (0) -> a =1 set0.
Proof. By Move=> a Ha x; Apply/idP => [Hx]; Rewrite: (cardD1 x) Hx in Ha. Qed.

Lemma eq_card0 : (a : (set d)) a =1 set0 -> (card a) = (0).
Proof. By Move=> a Da; Rewrite: (eq_card Da) card0. Qed.

Lemma set0Px : (a : (set d)) (reflect a =1 set0 (set0b a)).
Proof. Exact [a](iffP eqP (!card0_eq?) (!eq_card0?)). Qed.

Lemma set0Pnx : (a : (set d)) (reflect (EX x | (a x)) (negb (set0b a))).
Proof.
Move=> a; Case: (set0Px a) => [Ha | Hna]; Constructor.
  By Move=> [x Hx]; Case/idP: (Ha x).
By Case: (pickP a) => [x Hx| Ha]; [Exists x | Case (Hna Ha)].
Qed.

Lemma subsetPx : (a, b : (set d))
  (reflect (sub_set a b) (subset a b)).
Proof.
Move=> a b; Unfold subset disjoint setI setC.
Apply: (iffP (set0Px ?)).
  By Move=> Hab x Ha; Apply negbEf; Rewrite: -(Hab x) Ha.
By Move=> Hab x; Case Ha: (a x); Rewrite: ?(Hab ? Ha).
Qed.

Lemma subset_leq_card : (a, b : (set d))
  (subset a b) -> (leq (card a) (card b)).
Proof.
Move=> a b; Move/(set0Px ?) => Hab.
Rewrite: -(leq_add2l (card (setC b))) 2!(addnC (card (setC b))).
Rewrite: -cardUI (eq_card Hab) card0 addn0 cardC; Apply max_card.
Qed.

Lemma subset_refl : (a : (set d)) (subset a a).
Proof. Exact [a](introT (subsetPx a a) [_;H]H). Qed.

Lemma eq_subset : (a, a' : (set d)) a =1 a' -> (subset a) =1 (subset a').
Proof.
By Move=> a a' Eaa' b; Congr eqn; Apply: eq_card => [x]; Rewrite: /setI Eaa'.
Qed.

Lemma eq_subset_r : (b, b' : (set d))
  b =1 b' -> (a : (set d)) (subset a b) = (subset a b').
Proof.
Move=> b b' Ebb' a; Congr eqn; Apply: eq_card => [x].
By Rewrite: /setI /setC Ebb'.
Qed.

Lemma subset_setA : (a : (set d)) (subset a d).
Proof. By Move=> a; Apply/(subsetPx ? ?). Qed.

Lemma subsetA : (a : (set d)) (subset d a) -> (x : d) (a x).
Proof. By Move=> a Ha x; Apply: (subsetPx ? ? Ha x). Qed.

Lemma subset_eqPx : (a, b : (set d))
  (reflect a =1 b (andb (subset a b) (subset b a))).
Proof.
Move=> a b; Apply: (iffP andP) => [[Hab Hba] x | Eab].
  By Apply/idP/idP; Apply: subsetPx.
By Rewrite: (eq_subset_r Eab) (eq_subset Eab) subset_refl.
Qed.

Lemma subset_cardP : (a, b : (set d))
  (card a) = (card b) -> (reflect a =1 b (subset a b)).
Proof.
Move=> a b Ecab; Case Hab: (subset a b) (subset_eqPx a b); Simpl; Auto.
Case: (subsetPx b a) => [H | []] // x Hbx; Apply/idPn => [Hax].
Case/idP: (ltnn (card a)); Rewrite: {1 card}lock Ecab (cardD1 x) Hbx -lock /setD1.
Apply: subset_leq_card; Apply/(subsetPx ? ?) => [y Hy]; Rewrite: andbC.
By Rewrite: (subsetPx ? ? Hab ? Hy); Apply/eqP => [Dx]; Rewrite: Dx Hy in Hax.
Qed.

Lemma subset_trans : (a, b, c : (set d))
  (subset a b) -> (subset b c) -> (subset a c).
Proof.
Move=> a b c Hab Hbc; Apply/(subsetPx ? ?) => [x Hx].
Exact (subsetPx b c Hbc x (subsetPx a b Hab x Hx)).
Qed.

Lemma subset_all : (s : (seq d); a : (set d)) (subset s a) = (all a s).
Proof. By Move=> s a; Exact (sameP (subsetPx ? ?) allP). Qed.

Lemma disjoint_sym: (a, b: (set d)) (disjoint a b) = (disjoint b a).
Proof. By Move=> a b; Congr eqn; Apply: eq_card => [x]; Apply: andbC. Qed.

Lemma eq_disjoint : (a, a' : (set d)) a =1 a' -> (disjoint a) =1 (disjoint a').
Proof. By Move=> a a' Ea b; Congr eqn; Apply: eq_card => [x]; Congr andb. Qed.

Lemma disjoint_subset : (a, b : (set d)) (disjoint a b) = (subset a (setC b)).
Proof.
Move=> a b; Unfold subset; Rewrite: 2!(disjoint_sym a).
By Apply: eq_disjoint => [x]; Rewrite: /setC negb_elim.
Qed.

Lemma disjoint_trans : (a, b, c : (set d))
  (subset a b) -> (disjoint b c) -> (disjoint a c).
Proof. Move=> a b c; Rewrite: 2!disjoint_subset; Apply subset_trans. Qed.

Lemma disjoint0 : (a : (set d)) (disjoint set0 a).
Proof. By Move=> a; Apply/(set0Px ?). Qed.

Lemma disjoint1 : (x : d; a : (set d)) (disjoint (set1 x) a) = (negb (a x)).
Proof.
Move=> x a; Apply negb_sym; Apply: (sameP ? (set0Pnx ?)).
Unfold setI; Apply introP; Move=> Hx; LeftBy Exists x; Rewrite eqd_refl.
By Move=> [y H]; Case/andP: H => [Dx Hy]; Case: (negP Hx); Rewrite (eqP Dx).
Qed.

Lemma disjointU : (a, a', b : (set d))
  (disjoint (setU a a') b) = (andb (disjoint a b) (disjoint a' b)).
Proof.
Move=> a a' b; Rewrite: /disjoint; Case: (set0Px (setI a b)) => [Hb | Hb] /=.
  Congr eqn; Apply: eq_card => [x]; Move: {Hb}(Hb x); Rewrite: /setI /setU.
  By Case (b x); [Rewrite andbT; Move=> Hx; Rewrite: Hx | Rewrite: !andbF].
Apply/(set0Px ?) => [Ha]; Case: Hb; Move=> x; Apply/nandP.
Case/nandP: {Ha}(Ha x); Auto; Case/norP; Auto.
Qed.

Lemma disjointU1 : (x : d; a, b : (set d))
  (disjoint (setU1 x a) b) = (andb (negb (b x)) (disjoint a b)).
Proof.
By Move=> x a b; Rewrite: -(!eq_disjoint (setU (set1 x) a)) ?disjointU ?disjoint1.
Qed.

Lemma disjoint_has : (s : (seq d); a : (set d))
  (disjoint s a) = (negb (has a s)).
Proof.
Move=> s a; Rewrite: has_count -(eq_count (filter_enum a)) -has_count has_sym.
By Rewrite: has_count count_filter -filter_setI -count_filter -leqNgt leqn0.
Qed.

(* should be subsumed by the use of disjoint_has. *)

Lemma disjoint_cat : (s1, s2 : (seq d); s3 : (set d))
  (disjoint (cat s1 s2) s3) = (andb (disjoint s1 s3) (disjoint s2 s3)).
Proof. Move=> *; Rewrite: -disjointU; Exact (eq_disjoint (mem_cat ? ?) ?). Qed.

End FiniteSet.

Syntactic Definition card_uniqP := card_uniqPx | 1.
Syntactic Definition subsetP := subsetPx | 2.
Syntactic Definition set0P := set0Px | 1.
Syntactic Definition set0Pn := set0Pnx | 1.
Syntactic Definition subset_eqP := subset_eqPx | 2.

Grammar constr constr1 : constr :=
  if_pick ["if" "pick" tactic:identarg($var) "in" constr($dom)
               "then" constr($pick) "else" constr($nopick)] ->
  [if (pick $dom) is (Some $var) then $pick else $nopick].

(* Overridden at the end of file to fix module name. *)

Syntax constr level 1:
  pp_Top_pick
    [<<(CASES $_(TOMATCH (APPLIST <<pick>> $dom))
         (EQN $pick (PATTCONSTRUCT <<Some>> $var))
         (EQN $nopick (PATTCONSTRUCT <<None>>)))>>]
  -> [ [<hov 0> [<hov 0> "if pick " $var " in" [1 4] $dom:E]
                [1 2] "then " $pick:E [1 2] "else " $nopick:E] ].

Section FunImage.

Variables d : finSet; d' : dataSet; f : d -> d'.

Definition codom : (set d') := [x'](negb (set0b (preimage f (set1 x')))).

Remark Hiinv : (x' : d') (codom x') -> {x : d | x' =d (f x)}.
Proof.
Move=> x' Hx'; Case: (pickP [x] x' =d (f x)) => [x Dx | Hnx']; LeftBy Exists x.
By Rewrite: /codom /preimage (introT set0P Hnx') in Hx'.
Qed.

Definition iinv [x' : d'; Hx' : (codom x')] : d :=
  let (x, _) = (Hiinv Hx') in x.

Lemma codom_f : (x : d) (codom (f x)).
Proof. Move=> x; Apply/set0Pn; Exists x; Exact (set11 ?). Qed.

Lemma f_iinv : (x' : d'; Hx' : (codom x')) (f (iinv Hx')) = x'.
Proof. By Move=> x' Hx'; Unfold iinv; Case (Hiinv Hx'); Move=> x; Case/eqP. Qed.

Hypothesis Hf : (injective f).

Lemma iinv_f : (x : d; Hfx : (codom (f x))) (iinv Hfx) = x.
Proof. Move=> x Hfx; Apply Hf; Apply f_iinv. Qed.

Lemma preimage_iinv : (a' : (set d'); x' : d'; Hx' : (codom x'))
   (preimage f a' (iinv Hx')) = (a' x').
Proof. By Move=> *; Rewrite: /preimage f_iinv. Qed.

Section Image.

Variable a : (set d).

Definition image : (set d') := [x'](negb (disjoint (preimage f (set1 x')) a)).

(* This first lemma does not depend on Hf : (injective f). *)
Lemma image_codom : (x' : d') (image x') -> (codom x').
Proof.
Move=> x'; Case/set0Pn => [] x; Case/andP; Move/eqP => Dx _; Rewrite Dx.
Apply codom_f.
Qed.

Lemma image_f : (x : d) (image (f x)) = (a x).
Proof.
Move=> x; Apply/set0Pn/idP => [[y Hy] | Hx].
  By Case/andP: Hy => [Dx Hy]; Rewrite (Hf (eqP Dx)).
By Exists x; Rewrite: /setI /preimage eqd_refl.
Qed.

Lemma image_iinv : (x' : d'; Hx' : (codom x')) (image x') = (a (iinv Hx')).
Proof. By Move=> x' Hx'; Rewrite: -image_f f_iinv. Qed.

Lemma pre_image : (preimage f image) =1 a.
Proof. By Move=> x; Rewrite: /preimage image_f. Qed.

End Image.

Lemma image_pre : (a' : (set d'))
  (image (preimage f a')) =1 (setI a' codom).
Proof.
Move=> a' x'; Rewrite: /setI andbC; Case Hx': (codom x'); Simpl.
  By Rewrite: -(f_iinv Hx') image_f /preimage f_iinv.
Apply/idPn => [Hax']; Case/idPn: Hx'; Exact (image_codom Hax').
Qed.

Fixpoint preimage_seq [s : (seq d')] : (seq d) :=
  if s is (Adds x s') then
    (if pick y in (preimage f (set1 x)) then (Adds y) else id (preimage_seq s'))
  else seq0.

Lemma maps_preimage : (s : (seq d')) (sub_set s codom) ->
  (maps f (preimage_seq s)) = s.
Proof.
Elim=> [|x s Hrec] //=; Case: (pickP (preimage f (set1 x))) => [y Dy | Hs'] Hs.
  By Rewrite: /= (eqP Dy) (Hrec [z; Hz](Hs z (setU1r ? Hz))).
By Case/set0P: (Hs x (setU11 ? ?)).
Qed.

End FunImage.

Section Ordinal.

Variable n : nat.

Local ordp : (set natData) := [m](ltn m n).

Definition ordData := (subData ordp).

Fixpoint iota [m: nat] : (seq ordData) :=
  if m is (S m') then
    if (subdIopt ordp m') is (Some u) then (add_last (iota m') u) else (iota m')
  else seq0.

Lemma iota_ltn : (m : nat; u : ordData) (iota m u) = (ltn (subdE u) m).
Proof.
Move=> m u; Elim: m => [|m Hrec] //=; Rewrite: /= ltnS leq_eqVlt -Hrec.
Case: (subdIoptP ordp m) => [v Hm Dv | Hm].
  By Rewrite: /= mem_add_last /= /setU1 eqd_sym /eqd /= Dv.
By Case: ((subdE u) =P m) => [Dm | _]; LeftBy Case (negP Hm); Case Dm; Case u.
Qed.

Lemma iotaP : (u : ordData) (count (set1 u) (iota n)) = (1).
Proof.
Move=> [p Hp]; Rewrite: /eqd /= -/(true :: nat) -~Hp {3}/ordp. 
Elim: {1 3 4}n (leqnn n) => [|m Hrec] Hm //=; Rewrite: ltnS.
Case: (subdIoptP ordp m) => [v _ Dv | Hm']; RightBy Rewrite: /ordp Hm in Hm'.
Rewrite: -cats1 count_cat (Hrec (ltnW Hm)) /seq1 /= Dv.
By Rewrite: ltn_neqAle leq_eqVlt; Case (p =d m).
Qed.

Definition ordinal : finSet := (FinSet iotaP).

Lemma ordinal_ltn : (x : ordinal) (ltn (subdE x) n).
Proof. By Case. Qed.

Lemma card_ordinal : (card ordinal) = n.
Proof.
Rewrite: cardA /=; Elim: {-2}n (leqnn n) => [|m Hrec] Hm //=.
Case: (subdIoptP ordp m) => [v _ _ | Hm']; RightBy Rewrite: /ordp Hm in Hm'.
Exact (etrans (size_add_last ? v) (congr S (Hrec (ltnW Hm)))).
Qed.

Definition make_ord : (m : nat) (ltn m n) -> ordinal := (subdI 2!ordp).

End Ordinal.

Section SubFinSet.

Variables d : finSet; a : (set d).

Fixpoint fsub_enum [s : (seq d)] : (seq (subData a)) :=
  if s is (Adds x s') then
    (if (subdIopt a x) is (Some u) then (Adds u) else id (fsub_enum s'))
  else seq0.

Lemma fsub_enumP : (u : (subData a))
  (count (set1 u) (fsub_enum (enum d))) = (1).
Proof.
Move=> [x Hx]; Rewrite: /eqd /= -(count_set1_enum x).
Elim: (enum d) => [|y s Hrec] //=; Rewrite: -~Hrec.
Case: (subdIoptP a y) => [u Hy Du | Hy]; LeftBy Rewrite: /= Du.
By Case: (x =P y) => [Dx | _] //; Rewrite: -Dx Hx in Hy.
Qed.

Definition subFin := (FinSet fsub_enumP).

Lemma card_sub_dom : (!card subFin (subData a)) = (card a).
Proof.
Apply: (etrans (cardA ?)); Rewrite: /card /=.
Elim: (enum d) => [|x s Hrec] //=.
By Case: (subdIoptP a x) => [u Hx _ | Hx]; Rewrite: ?Hx //= -Hrec ?(negbE Hx).
Qed.

End SubFinSet.

Section ProdFinSet.

Variables d1, d2 : finSet.

Syntactic Definition pd := (prodData d1 d2).

Definition fprod_enum : (seq pd) :=
  (foldr [x1](cat (maps (proddI 2!d2 x1) (enum d2))) seq0 (enum d1)).

Lemma fprod_enumP : (u : pd) (count (set1 u) fprod_enum) = (1).
Proof.
Move=> [x1 x2]; Rewrite: -{(1)}/((d1 x1)::nat) -mem_enum /fprod_enum.
Elim: (enum d1) (uniq_enum d1) => [|y1 s1 Hrec] //=; Case/andP => [Hy1 Hs1].
Rewrite: count_cat ~{Hrec Hs1}(Hrec Hs1).
Rewrite: count_filter filter_maps size_maps /= /setU1 -count_filter.
Case Hx1: (y1 =d x1); Rewrite: /= /comp.
  Rewrite: (eqP Hx1) in Hy1; Rewrite: (negbE Hy1) (eqP Hx1) /= addn0 -(card1 x2).
  By Apply: eq_count => [y2]; Rewrite: {1}/eqd /= set11.
Rewrite: addnC -{2 ((s1 x1)::nat)}addn0 -(card0 d2); Congr addn.
By Apply: eq_count => [y]; Rewrite: eqd_sym /eqd /= Hx1.
Qed.

Definition prodFin := (FinSet fprod_enumP).

Lemma card_prod_dom : (!card prodFin pd) = (mult (card d1) (card d2)).
Proof.
Apply: (etrans (cardA ?)); Rewrite: /= /fprod_enum !cardA.
By Elim: (enum d1) => [|x1 s1 Hrec] //=; Rewrite: size_cat ~Hrec size_maps.
Qed.

End ProdFinSet.

Section SumFinSet.

Variables I : finSet; d : I -> finSet.

Definition sumfin_subdom [i : I] : dataSet := (d i).
Local fsd : dataSet := (sumData sumfin_subdom).

Fixpoint fsum_enum [si : (seq I)] : (seq fsd) :=
  if si is (Adds i si') then
    (cat (maps [x](sumdI 2!sumfin_subdom x) (enum (d i))) (fsum_enum si'))
  else seq0.

Lemma fsum_enumP : (u : fsd) (count (set1 u) (fsum_enum (enum I))) = (1).
Proof.
Move=> [i x]; Rewrite: -{(1)}/((I i)::nat) -mem_enum.
Elim: (enum I) (uniq_enum I) => [|j s Hrec] //=; Case/andP => [Hj Hs].
Rewrite: count_cat ~{Hrec Hs}(Hrec Hs).
Rewrite: count_filter filter_maps size_maps /= /setU1 -count_filter.
Case Hi: (j =d i); Rewrite: /= /comp.
  Rewrite: (eqP Hi) in Hj; Rewrite: (negbE Hj) (eqP Hi) /= addn0 -(card1 x).
  Apply: eq_count => [y]; Exact (sumd_eqdr x y).
Rewrite: addnC -{2 ((s i)::nat)}addn0 -(card0 (d j)); Congr addn.
Apply: eq_count => [y]; Rewrite eqd_sym.
Apply/idP => [Hy]; Case/idP: Hi; Exact (sumd_eqdl Hy).
Qed.

Definition sumFin := (FinSet fsum_enumP).

Lemma card_sum_dom :
  (!card sumFin fsd) = (foldr [i](addn (card (d i))) (0) (enum I)).
Proof.
Apply: (etrans (cardA ?)); Simpl; Elim: (enum I) => [|i s Hrec] //=.
By Rewrite: /= -Hrec size_cat size_maps Hrec cardA.
Qed.

End SumFinSet.

Section IsoCard.

Lemma monic_card_leq : (d, d' : finSet; f : d -> d'; g : d' -> d)
  (monic f g) -> (leq (card d) (card d')).
Proof.
Move=> d d' f g Hfg; Rewrite: (cardA d') -(size_maps g).
Apply: (leq_trans (subset_leq_card ?) (card_size ?)).
Apply/subsetP=> [x _]; Apply/mapsP; Exists (f x); By Rewrite: ?mem_enum.
Qed.

Lemma iso_eq_card_dom : (d, d' : finSet)
  (EX f : d -> d'| (iso f)) -> (card d) = (card d').
Proof.
Move=> d d' [f [g Hfg Hgf]]; Apply: eqP.
By Rewrite: eqn_leq (monic_card_leq Hfg) (monic_card_leq Hgf).
Qed.

Lemma eq_datum_card : (d, d' : finSet)
  (datum d) == (datum d') -> (card d) = (card d').
Proof.
Move=> d [[d' eqd' eqd'P] ed' Hed'] Hdd'; Simpl in Hdd'.
Case: d' / Hdd' eqd' eqd'P ed' Hed' => [] eqd' eqd'P ed' Hed'.
By Apply iso_eq_card_dom; Do 2 Exists [x:d]x.
Qed.

Lemma iso_eq_card : (d, d' : finSet; a : (set d); a' : (set d'))
  (EX f : (subd a) -> (subd a') | (iso f)) -> (card a) = (card a').
Proof.
Move=> d d' a a' Haa'; Rewrite: -(card_sub_dom a) -(card_sub_dom a').
By Apply: iso_eq_card_dom.
Qed.

Definition eq_dom_size [d1, d2 : finSet] : Prop :=
  (size (enum d1)) = (size (enum d2)).

Definition assoc_findom : (d1, d2 : finSet) (eq_dom_size d1 d2) -> d1 -> d2.
Move=> d1 d2 E12 x1; Cut (d2 :: Set).
  Move=> y2; Exact (sub y2 (enum d2) (index x1 (enum d1))).
Abstract By Move: E12; Rewrite: /eq_dom_size; Case: (enum d2) => //;
            Case: (enum d1) (mem_enum x1).
Defined.

Lemma assoc_findom_monic : (d1, d2 : finSet)
  (E12 : (eq_dom_size d1 d2); E21 : (eq_dom_size d2 d1))
  (monic (assoc_findom E12) (assoc_findom E21)).
Proof.
Rewrite: /eq_dom_size; Move=> d1 d2 E12 E21 x.
Pose y := (assoc_findom E12 x); Rewrite: /assoc_findom {2}/y /assoc_findom.
By Rewrite: index_uniq ?sub_index ?uniq_enum ?E21 ?index_mem ?mem_enum.
Qed.

Lemma eq_card_iso_dom : (d1, d2 : finSet; Ed : (card d1) = (card d2))
  {f : d1 -> d2 & {g : d2 -> d1 | (monic f g) & (monic g f)}}.
Proof.
Move=> d d'; Rewrite: !cardA; Move=> E12; Def: E21 := (esym E12).
Exists (assoc_findom E12); Exists (assoc_findom E21); Apply assoc_findom_monic.
Qed.

Lemma eq_card_iso : (d, d' : finSet; a : (set d); a' : (set d'))
  (Haa' : (card a) = (card a')) [da := (subd a); da' := (subd a')]
  {f : da -> da' & {g : da' -> da | (monic f g) & (monic g f)}}.
Proof.
Move=> d d' a a' Haa'; Apply: (!eq_card_iso_dom (subFin a) (subFin a')).
By Rewrite: /= !card_sub_dom.
Qed.

End IsoCard.

Section CardFunImage.

Variables d, d' : finSet; f : d -> d'.

Lemma leq_image_card : (a : (set d)) (leq (card (image f a)) (card a)).
Proof.
Move=> a; Pose p := (filter a (enum d)).
Step Up: (uniq p) By Apply: uniq_filter; Apply uniq_enum.
Rewrite: -(eq_card (filter_enum a)) (card_uniqP Up) -(size_maps f).
Apply: (leq_trans (subset_leq_card ?) (card_size ?)); Apply/subsetP => [u].
Case/set0Pn; Move=> x; Case/andP; Move/eqP => Du Hx.
By Apply/mapsP; Exists x; LeftBy Rewrite: /p filter_enum.
Qed.

Hypothesis Hf : (injective f).

Lemma card_image : (a : (set d)) (card (image f a)) = (card a).
Proof.
Move=> a; Apply iso_eq_card.
Step Hf1 : (w : (subd (image f a))) (a (iinv (image_codom (subd_mem w)))).
  By Move=> [x' Hx']; Rewrite: -image_iinv.
Step Hf2 : (w : (subd a))(image f a (f (subdE w))).
  By Move=> [x Hx]; Rewrite image_f.
Exists [w](subdI 1!d (Hf1 w)); Exists [w](subdI 1!d' (Hf2 w)).
  By Move=> [x Hx]; Apply: subdE_inj; Rewrite: /= f_iinv.
By Move=> [x Hx]; Apply: subdE_inj; Rewrite: /= iinv_f.
Qed.

Lemma card_codom : (card (codom f)) = (card d).
Proof.
Apply: etrans (card_image d); Apply: eq_card => [x']; Apply/idPn/idP.
  By Move=> Hx; Rewrite: -(f_iinv Hx) image_f.
Exact (image_codom 5!?).
Qed.

Lemma card_preimage : (a' : (set d'))
  (card (preimage f a')) = (card (setI (codom f) a')).
Proof.
Move => a'; Apply: (etrans (esym (card_image ?)) (eq_card ?)) => [x'].
By Rewrite: (image_pre Hf) /setI andbC.
Qed.

End CardFunImage.

(* Finite sets directly from lists; cute, but not too useful. *)

Section ListFinSet.

Variables d : Set; deq : d -> d -> bool; dlist : (list d).

Hypothesis Hd : (x : d)
 (fold_right [y](if (deq x y) then (cons y) else [l]l) (nil d) dlist)
    = (cons x (nil d)).

Remark deqP : (reflect_eq deq).
Proof.
Move=> x y; Apply introP.
  Move=> Hxy; Elim: (dlist) (Hd y) (Hd x) => [|z s Hrec] //=.
  Case: (deq y z) => [|] Hsy.
    By Injection: Hsy => _ Dz; Rewrite: Dz Hxy; Injection=>*.
  Case (deq x z); Auto; Elim: s Hsy {Hrec} => [|z' s Hrec] //=.
  Case: (deq y z') => [|] Hsy; RightBy Case (deq x z'); Auto.
  By Injection: Hsy => _ Dz'; Rewrite: Dz' Hxy.
Move=> Hxy Dy; Case/negP: Hxy; Case: {y}Dy.
Elim: (dlist) (Hd x) => [|z s Hrec] //=.
By Case Hxz: (deq x z); Auto; Injection=> _ Dz; Rewrite Dz in Hxz.
Qed.

Definition explicitListData : dataSet := (DataSet deqP).

Remark count_set1_dlist : (x : explicitListData)
  (count (set1 x) (!seq_of_list explicitListData dlist)) = (1).
Proof.
Move=> x; Apply: etrans  (congr (!length ?) (Hd x)).
By Elim: (dlist) => [|y s Hrec] //=; Rewrite: Hrec {1}/eqd /=; Case (deq x y).
Qed.

Definition listFset := (FinSet count_set1_dlist).

End ListFinSet.
 
Unset Implicit Arguments.


