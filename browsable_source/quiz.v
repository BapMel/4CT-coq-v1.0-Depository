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
Require coloring.

Set Implicit Arguments.

(* A quiz is a pair of binary trees that covers the inner regions of a    *)
(* configuration and store their arity. The embedding lemmas allow us to  *)
(* use questions to actually test for an isomorphic embedding of the      *)
(* configuration in a minimal uncolorable cubic map.                      *)

(* We are only interested in arities between 5 and 11 (in fact 9, 10, and 11 *)
(* only occur at the hub).                                                   *)

Inductive qarity : Set :=
  Qa5 : qarity
| Qa6 : qarity
| Qa7 : qarity
| Qa8 : qarity
| Qa9 : qarity
| Qa10 : qarity
| Qa11 : qarity.

Definition nat_of_qarity [qa : qarity] : nat :=
  Cases qa of
    Qa5 => (5)
  | Qa6 => (6)
  | Qa7 => (7)
  | Qa8 => (8)
  | Qa9 => (9)
  | Qa10 => (10)
  | Qa11 => (11)
  end.

Coercion nat_of_qarity : qarity >-> nat.

Definition qarity_of_nat [n : nat] : qarity :=
  Cases n of
    (5) => Qa5
  | (6) => Qa6
  | (7) => Qa7
  | (8) => Qa8
  | (9) => Qa9
  | (10) => Qa10
  | _   => Qa11
  end.

Lemma qarity_of_qarity : (qa : qarity) (qarity_of_nat qa) = qa.
Proof. By Case. Qed.

(* There's only pretty printing for quizzes, because they are never entered *)
(* as data.                                                                 *)

Syntax constr level 0 :
  pp_qa5  [(Pretty $_ Qa5)]  -> ["5"]
| pp_qa6  [(Pretty $_ Qa6)]  -> ["6"]
| pp_qa7  [(Pretty $_ Qa7)]  -> ["7"]
| pp_qa8  [(Pretty $_ Qa8)]  -> ["8"]
| pp_qa9  [(Pretty $_ Qa9)]  -> ["9"]
| pp_qa10 [(Pretty $_ Qa10)] -> ["10"]
| pp_qa11 [(Pretty $_ Qa11)] -> ["11"].

Lemma qarityDataP : (comparable qarity).
Proof. Rewrite: /comparable; Decide Equality. Qed.

(* We specialize the question tree constructor according to the presence    *)
(* of left and right branches. We also need skewed left and right branches, *)
(* for configurations whose interior has an articulation.                   *)

Inductive question : Set :=
  Qask0  : question
| Qask1  : qarity -> question
| QaskL  : qarity -> question -> question
| QaskR  : qarity -> question -> question
| QaskLR : qarity -> question -> question -> question
| QaskLL : qarity -> question -> question
| QaskRR : qarity -> question -> question.

Syntax constr level 0 :
  pp_qu0  [(Pretty $_ Qask0)]  -> ["*"]
| pp_qu1  [(Pretty $_ (Qask1 $qa))]  -> [<<(Pretty qarity $qa)>>].

Syntax constr level 9 :
  pp_quL  [(Pretty $_ (QaskL $qa $ql))] ->
  [<<(Pretty qarity $qa)>> "-L->" <<(Pretty question $ql)>>:E]
| pp_quR  [(Pretty $_ (QaskR $qa $qr))] ->
  [<<(Pretty qarity $qa)>> "-R->" <<(Pretty question $qr)>>:E]
| pp_quLL  [(Pretty $_ (QaskLL $qa $ql))] ->
  ["-L->" <<(Pretty qarity $qa)>> "-L->" <<(Pretty question $ql)>>:E]
| pp_quRR  [(Pretty $_ (QaskRR $qa $qr))] ->
  ["-R->" <<(Pretty qarity $qa)>> "-R->" <<(Pretty question $qr)>>:E]
| pp_quLR  [(Pretty $_ (QaskLR $qa $ql $qr))] ->
  ["["<<(Pretty qarity $qa)>> " " [<hv 0>
         "-L->" <<(Pretty question $ql)>>:E [1 0]
         "-R->" <<(Pretty question $qr)>>:E "]"]].

Lemma questionDataP : (comparable question).
Proof. Rewrite: /comparable; Decide Equality; Apply qarityDataP. Qed.
Definition questionData : dataSet := Eval Compute in (compareData questionDataP).
Canonical Structure questionData.

Definition isQaskR [q : question] : bool :=
  if q is (QaskR _ _) then true else false.

Fixpoint flatq [q : question] : natseq :=
  Cases q of
     Qask0            => seq0
  | (Qask1 qa)        => (seq1 qa::nat)
  | (QaskL qa ql)     => (Adds qa::nat (flatq ql))
  | (QaskR qa qr)     => (Adds qa::nat (flatq qr))
  | (QaskLR qa ql qr) => (Adds qa::nat (cat (flatq ql) (flatq qr)))
  | (QaskLL qa qll)   => (Adds qa::nat (flatq qll))
  | (QaskRR qa qrr)   => (Adds qa::nat (flatq qrr))
  end.

(* Mirror image questions. *)

Fixpoint flipq [q : question] : question :=
  Cases q of
    (QaskL qa ql)     => (QaskR qa (flipq ql))
  | (QaskR qa qr)     => (QaskL qa (flipq qr))
  | (QaskLR qa ql qr) => (QaskLR qa (flipq qr) (flipq ql))
  | (QaskLL qa qll)   => (QaskRR qa (flipq qll))
  | (QaskRR qa qrr)   => (QaskLL qa (flipq qrr))
  | _ => q
  end.
  
Definition qstepL [g : hypermap; x : g] : g := (node (edge (node x))).
Definition qstepR [g : hypermap; x : g] : g := (node (edge x)).

Inductive quiz : Set := Quiz : (q0, q1 : question) quiz.

Definition isQuizR [qz : quiz] : bool :=
  let (q0, q1) = qz in (andb (isQaskR q0) (isQaskR q1)).

Definition flatqz [qz : quiz] : (seq natData) :=
  let (q0, q1) = qz in (cat (flatq q0) (flatq q1)).

Definition flipqz [qz : quiz] : quiz :=
  if qz is (Quiz (QaskR qa0 q01) (QaskR qa1 q10)) then
    (Quiz (QaskR qa0 (flipq q10)) (QaskR qa1 (flipq q01)))
  else qz.

Syntax constr level 10 :
  pp_quiz [(Pretty $_ (Quiz $q0 $q1))] ->
  ["Quiz " [<hv 0> <<(Pretty question $q0)>> [2 0] <<(Pretty question $q1)>>]].

Section FitQuiz.

Variable g : hypermap.

Fixpoint walkq [x : g; q : question] : (seq g) :=
  Cases q of
     Qask0            => seq0
  | (Qask1 qa)        => (seq1 x)
  | (QaskL qa ql)     => (Adds x (walkq (qstepL x) ql))
  | (QaskR qa qr)     => (Adds x (walkq (qstepR x) qr))
  | (QaskLR qa ql qr) =>
       (Adds x (cat (walkq (qstepL x) ql) (walkq (qstepR x) qr)))
  | (QaskLL qa qll)   =>
       let xl = (qstepL x) in (Adds (edge (node xl)) (walkq (qstepL xl) qll))
  | (QaskRR qa qrr)   => let xr = (qstepR x) in (Adds xr (walkq (qstepR xr) qrr))
  end.

Definition fitq [x : g; q : question] : bool :=
  ((flatq q)::(seq ?)) =d (maps arity (walkq x q)).

Lemma size_walkq : (x : g; q : question) (size (walkq x q)) = (size (flatq q)).
Proof. Move=> x q; Elim: q x => //= *; Rewrite: ?size_cat; Congr S; Auto. Qed.

Lemma fitq_cat : (x : g; q : question; s : (seq natData); s' : (seq g))
  ((cat (flatq q) s) =d (maps arity (cat (walkq x q) s')))
     = (andb (fitq x q) s =d (maps arity s')).
Proof.
Move=> x q s s'; Rewrite: /fitq; Move: (introT eqP (size_walkq x q)).
Elim: {q x}(walkq x q) (flatq q) => [|x s1 Hrec] [|n s2] //= Es12.
Rewrite: !eqseq_adds -andbA; Congr andb; Auto.
Qed.

Lemma size_flipq : (q : question) (size (flatq (flipq q))) = (size (flatq q)).
Proof. Elim=> //= *; Rewrite: ?size_cat 1?addnC; Congr S; Auto. Qed.

Definition walkqz [x : g; qz : quiz] : (seq g) :=
  let (q0, q1) = qz in (cat (walkq x q0) (walkq (edge x) q1)). 

Lemma size_walkqz : (x : g; qz : quiz) (size (walkqz x qz)) = (size (flatqz qz)).
Proof. By Move=> x [q0 q1]; Rewrite: /= ?size_cat ?size_walkq. Qed.

Definition fitqz [x : g; qz : quiz] : bool :=
  (flatqz qz) =d (maps arity (walkqz x qz)).

End FitQuiz.

Lemma fitqz_flip : (g : hypermap; x : g; qz : quiz)
     (plain_cubic g) -> (isQuizR qz) ->
  (fitqz x (flipqz qz)) = (!fitqz (mirror g) (face x) qz).
Proof.
Move=> g x [q0 q1] [HgE HgN]; Case: q0 => //=; Case: q1 => //=.
Move=> qa1 q10 qa0 q01 _; Def Dh: h : g -> (mirror g) := [y]y.
Rewrite: -(congr [f](f (face x)) Dh); Move: x.
Step De2: (x : g) (edge (edge x)) = x By Apply plain_eq.
Step Dn3: (x : g) (node (node (node x))) = x By Apply cubic_eq.
Step Hh1: (x : g) (arity (h x)) = (arity x) By Move=> *; Rewrite: Dh arity_mirror.
Step HhL: (x : g) (qstepL (h x)) = (h (qstepR x)).
  Move=> x; Rewrite: Dh /= /comp (f_finv (Inode g)) -{1 x}De2 -{1 (edge x)}Dn3.
  By Rewrite: Enode (finv_f (Inode g)).
Step HhR: (x : g) (qstepR (h x)) = (h (qstepL x)).
  Move=> x; Apply: (etrans ? (HhL ?)).
  By Rewrite: Dh /qstepL /qstepR /= (finv_f (Inode g)).
Step HhE: (x : g) (edge (h (face x))) = (h (face (edge x))).
  By Move=> *; Rewrite: Dh /= -{1 x}De2 /comp Eedge.
Step EaEN : (g' : hypermap; x : g') (arity (edge (node x))) = (arity x).
  By Move=> *; Rewrite: -arity_face Enode.
Move: (mirror g) h {Dh} Hh1 HhL HhR HhE => g' h Hh1 HhL HhR HhE.
Step Eqs1: (n, n' : nat; s, s' : (seq natData))
  ((Adds n s) =d (Adds n' s')) = (andb n =d n' s =d s') By Done.
Step Hq: (q : question; x : g) (fitq x (flipq q)) = (fitq (h x) q).
  Rewrite: /fitq; Elim=> //= *; Rewrite: ?HhL ?HhR ?EaEN Hh1 //;
    Rewrite: ?Eqs1 ?fitq_cat /fitq; Try Congr andb; Auto.
  By Rewrite andbC; Congr andb.
Move=> x; Rewrite: /fitqz /= !Eqs1 !fitq_cat /= !Eqs1 HhE !Hh1 !arity_face !HhR.
Congr andb; Rewrite: ![n](andbC (qa1::nat) =d n) !andbA; Congr andb; Rewrite andbC.
Congr andb; Apply: (etrans (Hq ? ?) (congr [y](fitq (h y) ?) ?)).
  By Rewrite: /qstepL -{2 x}De2 Eedge.
By Rewrite: /qstepL Eedge.
Qed.

Section QuizEmbedding.

Variables gm, gc : hypermap; rc : (seq gc).

Syntactic Definition ac := (kernel rc).
Syntactic Definition bc := (setC rc).
Local Hacbc := (subsetP (kernel_off_ring rc)).
Local HacF := (kernelF rc).

Hypotheses Hgm : (plain_cubic gm); Hgc: (plain_quasicubic rc).
Local De2m := (plain_eq Hgm).
Local Dn3m := (cubic_eq Hgm).
Local De2c := (plain_eq Hgc).
Local Dn3c := (quasicubic_eq Hgc).

(* Adds the (disjoint) domain covered by the question to a previously covered *)
(* domain. The empty set is returned if the question is invalid (wrong arity, *)
(* cover overlap).                                                            *)
 
Variables x0m : gm; x0c : gc; qz : quiz.
Local s0c : (seq gc) := (walkqz x0c qz).
Local s0m : (seq gm) := (walkqz x0m qz).

Definition valid_quiz : Prop :=
  (and4 (isQuizR qz) (fitqz x0c qz) (simple s0c) (fband s0c) =1 ac).

Hypotheses Hqzc : valid_quiz; Hqzm : (fitqz x0m qz).

Definition embedqz [x : gc] : gm :=
  let i = (find (cface x) s0c) in
  let j = (findex face (sub x0c s0c i) x) in
  (iter j face (sub x0m s0m i)).

Syntactic Definition h := embedqz.
Syntactic Definition hc := (edge_central h).
Local HhcE := (edge_central_edge h Hgc Hgm).

Remark Dhx0: (h x0c) = x0m.
Proof.
Rewrite: /embedqz /s0c /s0m; Case: {}Hqzc => [H _ _ _]; Case: {}qz H => [q0 q1].
By Case q0; Rewrite: //= connect0 /= findex0.
Qed.

Remark Dhs0 : (i : nat) (h (sub x0c s0c i)) = (sub x0m s0m i).
Proof.
Move=> i; Case Hi: (leq (size s0c) i).
  By Rewrite: !sub_default ?Dhx0 //; Move: Hi; Rewrite: /s0c /s0m !size_walkqz.
Rewrite: leqNgt in Hi; Move/idP: Hi => Hi.
Pose x := (sub x0c s0c i); Rewrite: /embedqz.
Replace (find (cface x) s0c) with i; LeftBy Rewrite: -/x findex0.
Case: {}Hqzc => [_ _ Uq _]; Move: Uq.
Rewrite: -(cat_take_drop i s0c) (drop_sub x0c Hi) -/x.
Rewrite: /simple maps_cat uniq_cat /=; Move/and3P=> [_ Uq _].
Rewrite: find_cat /= connect0 (size_takel (ltnW Hi)) addn0.
Case: (hasPx (cface x) (take i s0c)) => // [[y Hy Hxy]].
Case/norP: Uq; Case/mapsP; Exists y; LeftDone.
Exact (esym (rootP (Sface?) Hxy)).
Qed.

Remark Dhex0: (h (edge x0c)) = (edge x0m).
Proof.
Case: (Hqzc) => [H _ _ _]; Move: (Dhs0) H; Rewrite: /s0c /s0m; Case qz.
Move=> /= q0 q1 H; Move: {H}(H (size (flatq q0))).
By Rewrite: !sub_cat !size_walkq /= ltnn subnn andbC; Case q1.
Qed.

Lemma embedqz_arity : (x : gc) (ac x) -> (arity (h x)) = (arity x).
Proof.
Case: (Hqzc) => [_ Haqc _ Dac] x; Rewrite: -~Dac /embedqz; Move=> Hx.
Pose i := (find (cface x) s0c); Pose y := (sub x0c s0c i).
Pose j := (findex (!face?) y x).
Step Hi: (ltn i (size s0c)) By Rewrite: /i -has_find.
Step Hy: (s0c y) By Exact (mem_sub ? Hi).
Step Hxy : (cface x y) By Apply: (sub_find ? ?).
Unfold fitqz in Haqc Hqzm.
Rewrite: (arity_cface Hxy) /y -(sub_maps x0c (0)) // -(eqP Haqc) (eqP Hqzm).
Rewrite: (sub_maps x0m (0)); RightBy Move: Hi; Rewrite: /s0c !size_walkqz.
By Elim j; Move=> *; Rewrite: /= ?arity_face.
Qed.

Lemma embedqz_face : (x : gc) (ac x) -> (h (face x)) = (face (h x)).
Proof.
Case: (Hqzc) => [_ _ _ Dac] x; Rewrite: -Dac; Move=> Hx.
Pose i := (find (cface x) s0c); Rewrite: /embedqz -(eq_find (cface1 x)) -/i.
Pose yc := (sub x0c s0c i).
Step Hxyc: (cface yc x) By Rewrite: Sface /yc /i sub_find.
Rewrite: -Dhs0 -/yc -{1 x}(iter_findex Hxyc).
Move: (findex face yc x) (!findex_max ? face yc x) => j Hj.
Rewrite: leq_eqVlt in Hj; Case/orP: {Hj}(Hj Hxyc) => [Dj | Hj].
  Rewrite: -{j}/(pred (S j)) (eqP Dj) -/(finv face yc) (f_finv (Iface gc)).
  Rewrite: findex0 /= -/(arity yc) -embedqz_arity.
    By Rewrite: -/(finv face (h yc)) (f_finv (Iface gm)).
  By Rewrite: -Dac (closed_connect (fbandF s0c) Hxyc).
By Rewrite: f_iter findex_iter.
Qed.

Lemma embedqz_central : (sub_set s0c hc).
Proof.
Step Hq : (x : gc; q : question) (ac x) -> (ac (edge x)) -> (hc x) ->
          let s = (walkq (node x) q) in
          (all ac s) -> (maps h s) =d (walkq (node (h x)) q) ->
          (all hc s).
  Move=> x q; Elim: q x => //= [_].
   Move=> x HxF _ HxE _; Case/andP; Move/eqP=> Dhnx _.
    Rewrite: /edge_central Dhnx -{2 x}Enode embedqz_face ?Eface ?set11 //.
    By Rewrite: (fclosed1 HacF) Enode.
   Move=> q Hrec x HxF HexF HxE; Move/andP=> [HnxF HsF].
    Rewrite: eqseq_adds; Case/andP; Move/eqP=> Dhnx Hs.
    Step HenxF: (ac (edge (node x))) By Rewrite: (fclosed1 HacF) Enode.
    Step HennxF: (ac (edge (node (node x)))) By Rewrite: (fclosed1 HacF) Enode.
    Step HnxE: (hc (node x)).
      By Rewrite: /edge_central Dhnx -{2 x}Enode embedqz_face ?Eface ?set11.
    Step HennxE: (hc (edge (node (node x)))).
      Rewrite: /edge_central De2c -{1 (node (node x))}Enode (Dn3c (Hacbc HxF)).
      Rewrite: (embedqz_face HexF) (eqP HxE) -{1 (h x)}Dn3m Enode.
      Rewrite: -{(h (edge (node (node x))))}Eface -embedqz_face //.
      By Rewrite: De2m Enode Dhnx set11.
    Rewrite: HnxE /= /qstepL Hrec //.
      Rewrite: De2c -{(node (node x))}Enode (Dn3c (Hacbc HxF)).
      By Rewrite: -(fclosed1 HacF).
    By Rewrite: -{(h (edge (node (node x))))}Eface -embedqz_face // Enode Dhnx.
   Move=> q Hrec x HxF HexF HxE; Move/andP=> [HnxF HsF].
    Rewrite: eqseq_adds; Case/andP; Move/eqP=> Dhnx Hs.
    Step HenxF: (ac (edge (node x))) By Rewrite: (fclosed1 HacF) Enode.
    Step HennxF: (ac (edge (node (node x)))) By Rewrite: (fclosed1 HacF) Enode.
    Step HnxE: (hc (node x)).
      By Rewrite: /edge_central Dhnx -{2 x}Enode embedqz_face ?Eface ?set11.
    By Rewrite: HnxE /= /qstepR Hrec ?De2c 1?HhcE // (eqP HnxE) Dhnx.
   Move=> ql Hrecl qr Hrecr x HxF HexF HxE /=.
    Rewrite: !all_cat eqseq_adds maps_cat eqseq_cat ?size_maps ?size_walkq //.
    Move/and3P=> [HnxF HslF HsrF]; Case/and3P; Move/eqP=> Dhnx Hsl Hsr.
    Step HenxF: (ac (edge (node x))) By Rewrite: (fclosed1 HacF) Enode.
    Step HennxF: (ac (edge (node (node x)))) By Rewrite: (fclosed1 HacF) Enode.
    Step HnxE: (hc (node x)).
      By Rewrite: /edge_central Dhnx -{2 x}Enode embedqz_face ?Eface ?set11.
    Step HennxE: (hc (edge (node (node x)))).
      Rewrite: /edge_central De2c -{1 (node (node x))}Enode (Dn3c (Hacbc HxF)).
      Rewrite: (embedqz_face HexF) (eqP HxE) -{1 (h x)}Dn3m Enode.
      Rewrite: -{(h (edge (node (node x))))}Eface -embedqz_face //.
      By Rewrite: De2m Enode Dhnx set11.
    Rewrite: HnxE /= /qstepL /qstepR Hrecl // ?Hrecr // ?De2c ?HhcE //.
        By Rewrite: (eqP HnxE) Dhnx.
      By Rewrite: -{(node (node x))}Enode (Dn3c (Hacbc HxF)) -(fclosed1 HacF).
    By Rewrite: -{(h (edge (node (node x))))}Eface -embedqz_face // Enode Dhnx.
   Move=> q Hrec x HxF HexF HxE; Move/andP=> [HenLnxF HsF].
    Rewrite: eqseq_adds; Case/andP; Move/eqP=> DhenLnx Hs.
    Step HfexF: (ac (face (edge x))) By Rewrite: -(fclosed1 HacF).
    Step HffexF: (ac (face (face (edge x)))) By Rewrite: -(fclosed1 HacF).
    Step HenLnxE: (hc (edge (node (qstepL (node x))))).
      Rewrite: /edge_central De2c DhenLnx /qstepL De2m.
      Rewrite: -{1 x}Eedge (Dn3c (Hacbc HfexF)).
      Rewrite: -{1 (face (edge x))}Eface De2c (Dn3c (Hacbc HffexF)).
      Rewrite: !embedqz_face // (eqP HxE) -{2 (h x)}Eedge Dn3m .
      By Rewrite: -{2 (face (edge (h x)))}Eface De2m Dn3m set11.
    Rewrite: HenLnxE /= {1}/qstepL Hrec ?DhenLnx //.
    Rewrite: De2c -{1 x}Eedge /qstepL (Dn3c (Hacbc HfexF)).
    By Rewrite: -{1 (face (edge x))}Eface De2c (Dn3c (Hacbc HffexF)).
   Move=> q Hrec x HxF HexF HxE; Move/andP=> [HRnxF HsF].
    Rewrite: eqseq_adds; Case/andP; Move/eqP=> DhRnx Hs.
    Step HenxF: (ac (edge (node x))) By Rewrite: (fclosed1 HacF) Enode.
    Step HenenxF: (ac (edge (node (edge (node x))))).
      By Rewrite: (fclosed1 HacF) Enode.
    Step HRnxE: (hc (qstepR (node x))).
      Rewrite: /edge_central DhRnx /qstepR -(monic2F_eqd (Eface gm)).
      Rewrite: -embedqz_face //.
      By Rewrite: Enode -(monic2F_eqd (Eface gm)) -embedqz_face // Enode set11.
    By Rewrite: HRnxE /= {1}/qstepR Hrec ?De2c ?HhcE // (eqP HRnxE) DhRnx.
Step Hx0E: (hc x0c) By Rewrite: /edge_central Dhx0 Dhex0 set11.
Step Hex0E: (hc (edge x0c)) By Rewrite HhcE.
Move: {}Hqzc => [Hqz _ _ Dac].
Step Hs0F: (subset s0c ac) By Rewrite: -(eq_subset_r Dac); Apply ring_fband.
Step Ehs0: (maps h s0c) =d s0m.
  Apply/eqP; Pose n := (size (flatqz qz)).
  Step Dnc: (size s0c) = n By Rewrite: /s0c size_walkqz.
  Step Dnm: (size s0m) = n By Rewrite: /s0m size_walkqz.
  Rewrite: -(take_size s0c) -(take_size s0m) Dnc Dnm.
  Elim: {-2}n (leqnn n) => [|i Hrec] Hi; LeftBy Rewrite: !take0.
  Rewrite: (take_sub x0c) ?Dnc // maps_add_last Dhs0 (Hrec (ltnW Hi)).
  By Rewrite: -take_sub // Dnm.
Apply: subsetP; Move: Hs0F Ehs0 {Dac}; Rewrite: /s0c /s0m !subset_all.
Case: {}qz Hqz => [q0 q1] /=.
Rewrite: !all_cat maps_cat eqseq_cat; RightBy Rewrite: size_maps !size_walkq.
Case: q0 => //= [_ q01]; Case: q1 => //= [_ q10] _; Rewrite: Hx0E Hex0E /=.
Case/and3P; Case/andP; Move=> Hx0cF Hs01F Hex0cF Hs10F; Rewrite: !eqseq_adds.
Case/and3P; Case/andP; Case/eqP=> [] Hs01; Case/eqP=> [] Hs10.
Rewrite: /qstepR !Hq // ?De2c // ?(eqP Hx0E) //.
By Rewrite: /qstepR (eqP Hx0E) De2c De2m in Hs10 *.
Qed.

Lemma embedqz_rlinked : (rlink_connected (setI ac hc)).
Proof.
Step Hq1: (x : gc; a : (seq gc))
      (fband a x) -> (rlink_connected (setI (fband a) hc)) -> (hc (node x)) ->
    (rlink_connected (setI (fband (add_last a (node x))) hc)).
  Move=> x a Hx Ha Hnx y z; Rewrite: {1 2}/setI -cats1 !fband_cat /= !orbF.
  Step Henx: (setI (fband a) hc (edge (node x))).
    By Rewrite: /setI (fclosed1 (fbandF a)) Enode Hx HhcE.
  Case Hynx: (cface y (node x)).
    Case Hznx: (cface z (node x)).
      Move=> _ _; Exists (Seq0 gc); RightDone.
      By Rewrite: /= /rlink Eface (same_cface Hynx) Sface andbT.
    Rewrite: orbF; Move{Hznx}=> _ Hz.
    Case: {Ha}(Ha ? ? Henx Hz) => [p Hp Hap]; Exists (Adds (node x) p).
      By Move: Hp; Rewrite: Eedge /= {2}/rlink Eface Hynx.
    Rewrite: /= /setI fband_cat Hnx /= connect0 orbT.
    Apply/allP=> [t Ht]; Rewrite: fband_cat demorgan2; Apply/orP; Left.
    By Apply: (allP Hap).
  Case Hznx: (cface z (node x)) {Hynx}; Rewrite: !orbF.
    Move=>Hy; Case: {Ha}(Ha ? ? Hy Henx) => [p Hp Hap].
    Exists (add_last p (edge (node x))).
      By Rewrite: -cats1 path_cat Hp last_add_last /= /rlink De2c Sface Hznx.
    Apply/allP=> [t Ht]; Rewrite: /setI fband_cat demorgan2; Apply/orP; Left.
    Rewrite: mem_add_last in Ht; Case/setU1P: Ht => [[] | Ht] //.
    By Apply: (allP Hap).
  Move=> Hy Hz; Case: {Ha}(Ha ? ? Hy Hz) => [p Hp Hap]; Exists p; Auto.
  Apply/allP=> [t Ht]; Rewrite: /setI fband_cat demorgan2; Apply/orP; Left.
  By Apply: (allP Hap).
Step Hq : (x : gc; a : (seq gc); q : question)
   (fband a x) -> (fband a (edge x)) ->
   (all ac a) -> (rlink_connected (setI (fband a) hc)) ->
   let s = (walkq (node x) q) in
   (all (setI ac hc) s) -> (rlink_connected (setI (fband (cat a s)) hc)).
  Move=> x a q; Elim: q x a => /=; Try By Move=> *; Rewrite cats0.
  By Move=> _ x a Hx _ _ HaE; Rewrite: cats1 andbT; Case/andP; Auto.
  Move=> _ ql Hrec x a Hx Hex Ha HaE; Case/andP; Move/andP => [Hnx HnxE] Hql.
    Rewrite: -cat_add_last /qstepL; Apply Hrec; Auto.
        By Rewrite: -cats1 fband_cat /= cface1 Enode connect0 orbT.
      Rewrite: De2c -2![y](Enode gc (node (node y))) (Dn3c (Hacbc Hnx)) Enode.
      By Rewrite: -cats1 fband_cat -(fclosed1 (fbandF a)) Hex.
    By Rewrite: -cats1 all_cat Ha /= andbT.
  Move=> _ qr Hrec x a Hx _ Ha HaE; Case/andP; Move/andP=> [Hnx HnxE] Hqr.
    Rewrite: -cat_add_last /qstepR; Apply Hrec; Auto.  
        By Rewrite: -cats1 fband_cat (fclosed1 (fbandF a)) Enode Hx.
      By Rewrite: De2c -cats1 fband_cat /= connect0 orbT.
    By Rewrite: -cats1 all_cat Ha /= andbT.
  Move=> _ ql Hrecl qr Hrecr x a Hx Hex Ha HaE; Rewrite all_cat; Case/and3P.
    Move/andP=> [Hnx HnxE] Hql Hqr.
    Rewrite: -cat_add_last catA /qstepR; Apply Hrecr; Auto.
          By Rewrite: cat_add_last fband_cat /= (fclosed1 (fbandF a)) Enode Hx.
        By Rewrite: De2c cat_add_last fband_cat /= connect0 orbT.
      Rewrite: cat_add_last all_cat Ha /= Hnx /=.
      By Rewrite all_setI in Hql; Case/andP: Hql.
    Rewrite: /qstepL; Apply Hrecl; Auto.
        By Rewrite: -cats1 fband_cat /= cface1 Enode connect0 orbC.
      Rewrite: De2c -2![y](Enode gc (node (node y))) (Dn3c (Hacbc Hnx)) Enode.
      By Rewrite: -cats1 fband_cat -(fclosed1 (fbandF a)) Hex.
    By Rewrite: -cats1 all_cat Ha /= andbT.
  Move=> _ qll Hrec x a _ Hex Ha HaE; Case/andP; Move/andP=> [HneLnx HneLnxE] Hqll.
    Step Hfex: (ac (face (edge x))).
      Case/hasP: Hex => [y Hy Hexy]; Rewrite: cface1 in Hexy.
      By Rewrite (closed_connect HacF Hexy); Apply (allP Ha).
    Step Hffex: (ac (face (face (edge x)))) By Rewrite: -(fclosed1 HacF).
    Step Dffex: (node (qstepL (node x))) = (face (face (edge x))).
      Rewrite: /qstepL -{1 x}Eedge (Dn3c (Hacbc Hfex)).
      By Rewrite: -{1 (face (edge x))}Eface De2c (Dn3c (Hacbc Hffex)).
    Rewrite: -cat_add_last {2}/qstepL; Apply Hrec; Auto.
          By Rewrite: -cats1 fband_cat /= connect0 orbT.
        By Rewrite: De2c Dffex -cats1 fband_cat -!(fclosed1 (fbandF a)) /= Hex.
      By Rewrite: -cats1 all_cat Ha /= andbT.
    Rewrite: Dffex -{1 (face (face (edge x)))}Eface De2c; Apply Hq1; Auto.
      By Rewrite: -!(fclosed1 (fbandF a)).
    By Rewrite: -{(face (face (edge x)))}De2c Eedge -Dffex.
  Move=> _ qrr Hrec x a Hx _ Ha HaE; Case/andP; Move/andP=> [HRnx HRnxE] Hqrr.
    Step Henx: (ac (edge (node x))).
      Case/hasP: Hx => [y Hy Hxy]; Rewrite: -{x}Enode -cface1 in Hxy.
      By Rewrite: (closed_connect HacF Hxy); Apply (allP Ha).
    Rewrite: -cat_add_last {2}/qstepR; Apply Hrec; Auto.
          Rewrite: 2![a'](fclosed1 (!fbandF gc a')) /qstepR !Enode.
          By Rewrite: -cats1 fband_cat Hx.
        By Rewrite: De2c -cats1 fband_cat /= connect0 orbT.
      By Rewrite: -cats1 all_cat Ha /= andbT.
    By Rewrite: /qstepR; Apply Hq1; Auto; Rewrite: (fclosed1 (fbandF a)) Enode.
Case: {}Hqzc => [Hqz _ _ Dac].
Step Hs: (all (setI ac hc) s0c).
  Apply/allP=> [y Hy].
  By Rewrite: /setI -Dac (embedqz_central Hy) (subsetP (ring_fband ?) ? Hy).
Move: Hqz Dac Hs; Rewrite: /s0c; Case: {}qz => [q0 q1] /=; Rewrite: all_cat /=.
Case: q0 => //= [_ q01]; Case: q1 => //= [_ q10] _ Dac; Case/and3P; Case/andP.
Move/andP=> [Hx0F Hx0E] Hq01; Move/andP=> [Hx1F Hx1E] Hq10.
Pose a := (cat (seq2 x0c (edge x0c)) (walkq (qstepR x0c) q01)).
Pose a' := (cat a (walkq (qstepR (edge x0c)) q10)).
Step Ha': (rlink_connected (setI (fband a') hc)).
  Rewrite: /a' /qstepR; Apply Hq; Auto; Rewrite: ?De2c.
        By Apply (subsetP (ring_fband a)); Rewrite: /a /= /setU1 set11.
      By Apply (subsetP (ring_fband a)); Rewrite: /a /= /setU1 set11 /= orbT.
    Apply/allP=> [x Hx]; Rewrite: /= in Hx.
    By Do 2 Case/setU1P: Hx => [[] | Hx] //; Case/andP: (allP Hq01 ? Hx).
  Rewrite: /a /qstepR; Apply Hq; Auto; Rewrite: ?De2c /= ?connect0 ?orbT //.
    By Rewrite: Hx0F Hx1F.
  Rewrite: /seq2 -cat1s cats1 -{2 x0c}Eface De2c; Apply Hq1; Auto.
      By Rewrite: /= Sface fconnect1.
    Move=> x y; Rewrite: /setI /= !orbF; Move/andP=> [Hx _]; Move/andP=> [Hy _].
    By Exists (Seq0 gc); Rewrite: //= /rlink Eface (same_cface Hx) Sface andbT.
  By Rewrite: -{1 x0c}De2c Eedge.
Step Dac': ac =1 (fband a').
  Move=> x; Rewrite: -Dac /fband /= !has_cat /=; Congr orb.
  By Rewrite: !orbA; Congr orb; Rewrite orbC.
Move=> x y Hx Hy; Rewrite: /setI !Dac' in Hx Hy.
Case: (Ha' ? ? Hx Hy) => [p Hp Hpa]; Exists p; LeftDone.
By Apply/allP=> [z Hz]; Rewrite: /setI Dac'; Apply: (allP Hpa).
Qed.

Lemma quiz_preembedding : (preembedding ac embedqz).
Proof.
Split.
      Exact embedqz_face.
    Exact embedqz_arity.
  Case: {}Hqzc => [_ _ _ Dac]; Apply/subsetP=> [x]; Rewrite: -Dac.
  Move/hasP=> [y Hy Hxy]; Apply/set0Pn; Exists y.
  By Rewrite: /setI Hxy; Apply: embedqz_central.
Exact embedqz_rlinked.
Qed.

End QuizEmbedding.

Unset Implicit Arguments.
