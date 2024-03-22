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
Require color.
Require geometry.
Require coloring.
Require patch.
Require cfmap.
Require quiz.

Set Implicit Arguments.

(* Compile the quiz that tests for the occurrence of a configuration. Since *)
(* this requires to compute arities, we also check that the arity of ring   *)
(* regions are in the [3,6] range along the way. The procedure here is      *)
(* valid, but not complete, e.g., it assumes that skews only occur at       *)
(* articulations. The configuration data has been carefully knobbed to meet *)
(* those constraints.                                                       *)
(*   The algorithm proceeds by walking the map construction program         *)
(* backwards, keeeping track of kernel faces and of arities on the submap   *)
(* ring. During the traversal a list of questions is kept, that covers      *)
(* exactly the kernel faces that are disjoint from the current submap ring. *)
(* Each of these question is rooted at (node (ic x)) for some dart x of the *)
(* submap ring, where ic is the injection from the current submap to the    *)
(* full configuration map (crucially, this implies that "node" is computed  *)
(* in the full map). As the ring shrinks, questions are linked to form      *)
(* trees, until we arrive at the initial two-dart graph, where we have just *)
(* questions, which form a proper quiz.                                     *)
(*   H-type steps could be somewhat of a problem for this algorithm, but it *)
(* turns out that (with a little fiddling) in all the programs we consider, *)
(* we never need to join trees in an H step, so the code below doesn't      *)
(* cater to that case (we'd need to generate more LL and RR questions).     *)

(* We use a single sequence of records rather that three parallel sequences. *)

Record ring_question : Set :=
  RingQuestion {
    ring_question_is_kernel : bool;
    ring_question_outer_arity :> nat;
    ring_question_node_question :> question
  }.

Syntax constr level 10 :
  pp_ring_question [(Pretty $_ (RingQuestion $k $a $q))] ->
  ["+"$a (PPRQL $k) <<(Pretty question $q)>>]
| pp_rq_blink [<<(PPRQL $b)>>] -> ["(" $b ")>"]
| pp_rq_klink [<<(PPRQL <<true>>)>>] -> ["-N->"]
| pp_rq_xrlink [<<(PPRQL <<false>>)>>] -> ["..->"]
| pp_rqs [(Pretty (seq ring_question) $s)] ->
  ["RsSeq" [<hv 1> (PPRQL SPC ring_question $s)]].

Section ConfigQuiz.

Syntactic Definition isk := ring_question_is_kernel.

Remark ringQuestionDataP : (comparable ring_question).
Proof. Rewrite: /comparable; Decide Equality; Apply: comparable_data. Qed.
Definition ringQuestionData := Eval Compute in (compareData ringQuestionDataP).
Canonical Structure ringQuestionData.
Local rqseq : Set := (seq ringQuestionData).

(* We only compile questions for maps with kernel arities between 5 an 11; in *)
(* fact only the most central face (the one to which the "true" dart of the   *)
(* central submap belongs) can have more that 8 sides. We check and use this  *)
(* fact during the compilation. We also check that the ring arities are in    *)
(* the 3..6 range; this property allows us to lift the preembedding           *)
(* constructed in quiz.v into an actual embedding (see embed.v).              *)
(* All the functions below work with the arities offset by two, because each  *)
(* time a face is detached from the submap, if had at least two neighbors in  *)
(* that submap.                                                               *)

Definition small_qarity [a : nat] : qarity :=
  Cases a of (3) => Qa5 | (4) => Qa6 | (5) => Qa7 | (6) => Qa8
           | (7) => Qa10 | _ => Qa9 end.

Definition bad_small_arity [qa : qarity] : bool :=
  Cases qa of Qa9 => true | Qa10 => true | Qa11 => true | _ => false end.

Lemma small_qarityP : (a : nat) let qa = (small_qarity a) in
  (bad_small_arity qa) = (negb (qa::nat) =d (S (S a))).
Proof. Do 8 Case=> //. Qed.

Definition large_qarity [a : nat] : qarity :=
  Cases a of (7) => Qa9 | (8) => Qa10 | (9) => Qa11 | _ => (small_qarity a) end.

Definition bad_ring_arity [a : nat] : bool :=
  Cases a of (0) => true | (S (S (S (S (S _))))) => true | _ => false end.

Lemma not_bad_ring_arity : (g : hypermap; x : g)
  (bad_ring_arity (pred (pred (arity x)))) = false -> (good_ring_arity x).
Proof. Move=> g x; Rewrite: /good_ring_arity; Move: (arity x); Do 7 Case=> //. Qed.

(* Error value. *)
Local noquiz : quiz := (Quiz Qask0 Qask0).

(* The quiz construction proper.                                               *)

Definition rqs_Y [rq1, rq3 : ring_question; qs : rqseq; q1' : question] : rqseq :=
  let (k1, a1, _) = rq1 in let (k3, a3, q3) = rq3 in
  (Seq (RingQuestion k1 (S a1) q1') (RingQuestion k3 (S a3) q3) & qs).

Definition cfquiz_Y
    [rq1, rq2 : ring_question; rqs' : question -> rqseq] : rqseq :=
  let (_, _, q1) = rq1 in let (k2, a2, q2) = rq2 in
  if k2 then
    let qa2 = (small_qarity a2) in
    if (bad_small_arity qa2) then seq0 else
    (rqs' Cases q1 q2 of
      Qask0 Qask0 => (Qask1 qa2)
    | Qask0     _ => (QaskL qa2 q2)
    |     _ Qask0 => (QaskR qa2 q1)
    |     _     _ => (QaskLR qa2 q2 q1)
    end)
  else
    if (bad_ring_arity a2) then seq0 else
    Cases q1 q2 of
      Qask0            Qask0 => (rqs' Qask0)
    | (QaskR qa1 q1r)  Qask0 => (rqs' (QaskRR qa1 q1r))
    | Qask0  (QaskL qa1 q1l) => (rqs' (QaskLL qa1 q1l))
    |     _                _ => seq0
    end.

Definition rqs_H
     [rq1, rq3 : ring_question; qs : rqseq; q1', q2' : question] : rqseq :=
  let (k1, a1, _) = rq1 in let (k3, a3, q3) = rq3 in
  (Seq (RingQuestion k1 (S a1) q1')
       (RingQuestion true (1) q2')
       (RingQuestion k3 (S a3) q3) & qs).

Definition cfquiz_H
    [rq1, rq2 : ring_question; rqs' : question -> question -> rqseq] : rqseq :=
  let (k1, _, q1) = rq1 in let (k2, a2, q2) = rq2 in
  if k2 then
    let qa2 = (small_qarity (S a2)) in
    if (bad_small_arity qa2) then seq0 else
    Cases q1 q2 k1 of
      Qask0 Qask0 true => (rqs' (Qask1 qa2) q2) 
    | Qask0 Qask0    _ => (rqs' q1 (Qask1 qa2)) 
    | Qask0     _    _ => (rqs' q1 (QaskL qa2 q2)) 
    |     _ Qask0    _ => (rqs' (QaskR qa2 q1) q2)
    |     _     _    _ => seq0
    end
  else
    if (bad_ring_arity (S a2)) then seq0 else
    Cases q1 q2 of Qask0 Qask0 => (rqs' q1 q2) | _ _ => seq0 end.

Fixpoint cfquiz_rec [qs : rqseq; cp : cprog] : quiz :=
  Cases cp qs of
    Seq0 (Adds rq1 (Adds rq2 _)) =>
    let (k1, a1, q1) = rq1 in let (k2, a2, q2) = rq2 in
    if (negb (andb k1 k2)) then noquiz else
    let qa1 = (large_qarity (pred a1)) in
    let qa2 = (small_qarity (pred a2)) in
    if (orb (negb (qa1::nat) =d (S a1)) (bad_small_arity qa2)) then noquiz else
    (Quiz (QaskR qa1 q2) (QaskR qa2 q1))
  | (Adds s cp') (Adds rq1 (Adds rq2 (Adds rq3 qs'))) =>
    Cases s of
      (CpR n) => (cfquiz_rec (rotr n qs) cp')
    |  CpY    => (cfquiz_rec (cfquiz_Y rq1 rq2 (rqs_Y rq1 rq3 qs')) cp')
    |  CpH    => (cfquiz_rec (cfquiz_H rq1 rq2 (rqs_H rq1 rq3 qs')) cp')
    |   _     => noquiz
    end
  | _  _ =>
    noquiz
  end.

Section RqsWalk.

Variables g0, g : pointed_map; h : g -> g0.

Fixpoint rqs_fit [qs : rqseq; p : (seq g)] : bool :=
  Cases qs p of
    (Adds rqd qs') (Adds x p') => let rq = (rqd :: ring_question) in
    (and3b (arity (h x)) =d (addn rq (arity x))
           (fitq (node (h x)) rq)
           (rqs_fit qs' p'))
  | Seq0 Seq0 => true
  | _ _ => false
  end.

Lemma rqs_fit_adds : (rq : ring_question; qs : rqseq; x : g; p : (seq g))
  (rqs_fit (Adds rq qs) (Adds x p))
    = (and3b (arity (h x)) =d (addn rq (arity x))
             (fitq (node (h x)) rq)
             (rqs_fit qs p)).
Proof. Done. Qed.

Lemma rqs_fit_size : (qs : rqseq; p : (seq g))
  (rqs_fit qs p) -> (size qs) = (size p).
Proof. Elim=> [|rq qs Hrec] [|x p] //=; Case/and3P=> *; Congr S; Auto. Qed.

Fixpoint rqs_walk [qs : rqseq; p : (seq g0)] : (seq g0) :=
  Cases qs p of
    (Adds rqd qs') (Adds u p') => let rq = (rqd :: ring_question) in
    (cat (cat (seqn (isk rq) u) (walkq (node u) rq)) (rqs_walk qs' p'))
  | _ _ => seq0
  end.

Lemma rqs_walk_adds : (rq : ring_question; qs : rqseq; u : g0; p : (seq g0))
  (rqs_walk (Adds rq qs) (Adds u p))
    = (cat (cat (seqn (isk rq) u) (walkq (node u) rq)) (rqs_walk qs p)).
Proof. Done. Qed.

Definition rqs_ok [qs : rqseq] : Prop :=
  let r0 = (cpring g0) in let r = (cpring g) in let hr = (maps h r) in
  (and4 (rqs_fit qs r)
        (sub_set (setD r0 (setU (codom h) (fband hr))) good_ring_arity)
        (simple (cat (rqs_walk qs hr) r0))
        (fband (cat (rqs_walk qs hr) r0)) =1 (setU (setC (codom h)) (fband hr))).

End RqsWalk.

(* We check separately the radius of the configuration (the initial face *)
(* of the quiz might not be at the center of the kernel).                *)

Fixpoint cpradius2 [cp : cprog; i : nat] : bool :=
  if i is (S i') then
    let cm0 = (cpmask1 cp i') in
    let (mr1, _) = cm0 in let (_, mk1) = (cpadj cm0 cp) in
    let (_, mk2) = (cpadj (Cpmask mr1 mk1) cp) in
    if (all id mk2) then true else (cpradius2 cp i')
  else false.
    
Variable cf : config.

Local cp : cprog := (cfprog cf).

Definition cfquiz : quiz :=
  if (cpradius2 cp (cpksize cp)) then
    (cfquiz_rec (seqn (cprsize cp) (RingQuestion false (0) Qask0)) cp)
  else noquiz.

Hypothesis Hqz : (isQuizR cfquiz).

Remark Hcfk2 : (cpradius2 cp (cpksize cp)).
Proof. By Move: Hqz; Rewrite: /cfquiz; Case (cpradius2 cp (cpksize cp)). Qed.

Remark qs0_notR : (cp' : cprog) (isQuizR (cfquiz_rec seq0 cp')) = false.
Proof. By Elim=> //; Case. Qed.

Remark Hcp: (config_prog cp).
Proof.
Pose qs := (seqn (cprsize cp) (RingQuestion false (0) Qask0)).
Step Hcp: (setC1 seq0 cp) By Case: {}cp {}Hcfk2.
Step Eqs: (size qs) = (cprsize cp) By Rewrite: /qs size_seqn.
Move: Hcp Eqs Hqz; Rewrite: /cfquiz Hcfk2 -/qs.
Elim: {}cp qs => // [s cp' Hrec] [|rq1 [|rq2 [|rq3 qs]]] //= _.
Case: s cp' Hrec => //= [n||] [|s cp'] // H Eqs Hqs; Apply: H {}Hqs {H} => //.
    By Rewrite: -Eqs size_rotr.
  Move: Hqs; Rewrite: /cfquiz_Y  -(eq_add_S ? ? Eqs).
  Case: rq1 rq2 rq3 => [k1 a1 q1] [[|] a2 q2] [k3 a3 q3].
    By Case: (bad_small_arity (small_qarity a2)); LeftBy Rewrite qs0_notR.
  Case: (bad_ring_arity a2); LeftBy Rewrite qs0_notR.
  By Case: q1; Rewrite: ?qs0_notR //; Case: q2; Rewrite: ?qs0_notR.
Move: Hqs; Rewrite: /cfquiz_H  -Eqs.
Case: rq1 rq2 rq3 => [k1 a1 q1] [[|] a2 q2] [k3 a3 q3].
  Case: (bad_small_arity (small_qarity (S a2))); LeftBy Rewrite qs0_notR.
  By Case: q1; Rewrite: ?qs0_notR //; Case: q2; Rewrite: ?qs0_notR //; Case k1.
Case: (bad_ring_arity (S a2)); LeftBy Rewrite qs0_notR.
By Case: q1; Rewrite: ?qs0_notR //; Case: q2; Rewrite: ?qs0_notR.
Qed.
Hints Resolve Hcp.

Remark Hrad2 : (radius2 (kernel (cfring cf))).
Proof.
Rewrite: /cfring /cfmap -/cp.
Elim: {-2}(cpksize cp) (leqnn (cpksize cp)) {}Hcfk2 => //= [i Hrec] Hi.
Move: (proper_cpmask1 cp i) (cpsieve1 Hi Hcp).
Pose g := (cpmap cp); Pose cm0 := (cpmask1 cp i); Pose x0 := (sub g (cpker cp) i).
Move=> Hcm0 Ecm0; Case: (cpadj cm0 cp) (cpadj_proper Hcm0) (cpsieve_adj Hcp Hcm0).
Move=> mr1 mk1; Move/andP=> [_ Hmk1] Ecm1 /=; Rewrite: ~Ecm0 in Ecm1.
Pose cm1 := (Cpmask (seqn (cprsize cp) false) mk1).
Step Hcm1: (proper_cpmask cp cm1) By Rewrite: /= size_seqn set11.
Case: (cpadj cm1 cp) (cpadj_proper Hcm1) (cpsieve_adj Hcp Hcm1) => [mr2 mk2].
Move/andP=> [_ Emk2] Ecm2.
Case Hmk2: (all (!id bool) mk2); RightBy Apply: Hrec; Apply ltnW.
Clear; Clear Hrec; Pose kg := (kernel (rev (cpring g))).
Step Dkg: kg =1 (fband (cpker cp)).
  Move=> x; Move: (cpmap_simple Hcp) (cpmap_cover Hcp x).
  Rewrite: simple_cat fband_cat -/g orbC; Move/and3P=> [_ Ug _].
  Rewrite: /kg /kernel /setC fband_rev.
  Case Hx: (fband (cpker cp) x); RightBy Move=> *; Apply/idP.
  Case/hasP: Hx => [y Hy Hxy] _; Rewrite: [r](closed_connect (fbandF r) Hxy).
  By Apply: (hasPn Ug).
Step Hx0: (kg x0).
  Rewrite: Dkg; Apply: (subsetP (ring_fband ?)); Apply: mem_sub.
  By Rewrite: (size_cpker Hcp).
Apply/(radius2P ?); Exists x0; LeftDone.
Move=> x Hx; Apply/(!at_radius2P g kg (kernelF ?) ? ?).
Step Hx': (has (adj x) (cpsieve cm1 cp)).
  Rewrite: -Ecm2 /= fband_cat; Apply/orP; Right.
  Step []: (cpker cp) = (sieve mk2 (cpker cp)).
    Move: Hmk2 Emk2; Rewrite: -(size_cpker Hcp).
    By Elim: {}mk2 (cpker cp) => [|[|] m Hrec] [|y p] //= Hm Em; Rewrite: -Hrec.
  By Rewrite: -Dkg.
Case/hasP: Hx' => [y Hy]; Case/adjP=> [z Hxz Hzy].
Rewrite: /cm1 /= sieve_false /= in Hy.
Step Hez: (has (adj (edge z)) (seq1 x0)).
  By Rewrite: -Ecm1 /= fband_cat; Apply/orP; Right; Apply/hasP; Exists y.
Rewrite: has_seq1 Sadj in Hez; RightBy Apply: cpmap_plain; Apply config_prog_cubic.
Case/adjP: Hez => [t Hx0t Htz]; Exists t; Exists z; Split; Auto; Rewrite Dkg.
By Apply/hasP; Exists y; [Exact (mem_sieve Hy) | Rewrite: (same_cface Htz)].
Qed.  

Lemma cfquizP : (sub_set (cpring (cpmap cp)) good_ring_arity)
             /\ (EX x0 | (valid_quiz (cpring (cpmap cp)) x0 cfquiz)).
Proof.
Move: Hqz; Rewrite: /cfquiz Hcfk2 -{(cpmap cp)}/(cpmap (catrev cp seq0)).
Pose qs := (seqn (cprsize cp) (RingQuestion false (0) Qask0)).
Pose cp1 := (seq0 :: cprog); Step Hcp1: (cubic_prog cp1) By Done.
Pose cp2 := cp; Step Hcp2: (setU1 seq0 config_prog cp2) By Apply setU1r.
Step Arec : (rqs_ok (injcp cp1 2!cp2) qs).
  Rewrite: /cp2; Pose g := (cpmap cp); Pose r := (cpring g).
  Step Dq0: (rqs_walk qs r) = seq0.
    By Rewrite: /qs -size_ring_cpmap -/g -/r; Elim: r => //= *.
  Step Hd0: (codom [x : g]x) =1 g By Move=> x; Apply/set0Pn; Exists x; Apply/eqP.
  Split; Rewrite: //= ?maps_id -/g -/r ?~Dq0 /qs //=.
  By Rewrite: -size_ring_cpmap -/g -/r; Elim: r => //= *; Rewrite set11.
  By Move=> x; Rewrite: /setD /setU Hd0.
  By Move: (cpmap_simple Hcp); Rewrite: -/g -/r simple_cat; Case/andP.
  By Move=> x; Rewrite: /setU /setC Hd0.
Elim: cp2 Hcp2 cp1 Hcp1 qs Arec => [|s cp2 Hrec] Hscp2 cp1 Hcp1 qs Arec Hqz'.
  Case: Arec Hqz'; Pose g := (cpmap seq0); Pose g0 := (cpmap (catrev seq0 cp1)).
  Pose r := (cpring g); Pose r0 := (cpring g0); Pose h := (injcp cp1 2!seq0).
  Step EhE: (x : g) (edge (h x)) = (h (edge x)) By Move=> x; Apply: edge_injcp.
  Move=> Hr Hr0F Uq Eq; Case Dqs: qs Hr => [|[[|] a1 q1] [|[[|] a2 q2] qs']] //=.
  Case/and5P; Rewrite: addnC (addnC a2) /addn /= small_qarityP.
  Pose qa1 := (large_qarity (pred a1)); Case: ((qa1::nat) =P (S a1)) => //.
  Case: a2 Dqs => [|a2] Dqs //; Rewrite: /pred; Pose qa2 := (small_qarity a2).
  Case: ((qa2::nat) =P (S (S a2))) => // [[]] [] Eqa1 Hq1 Eqa2 Hq2.
  Case: qs' Dqs => //= [] Dqs  _ _; Split.
    Move=> u Hu; Apply: Hr0F; Rewrite: /setD Hu andbT /setU orbC.
    Case Hu': (fband (maps h r) u); Rewrite: /fband in Hu'.
      Move: Uq; Rewrite: simple_cat; Case/and3P; Clear; Case/hasP.
      Exists u; LeftDone; Rewrite: Dqs /= fband_cat /=.
      By Case/hasP: Hu' => [v]; Case/mapsP => [[|] _ []] Hu'; Rewrite: Hu' ?orbT.
    Apply/set0Pn => [[x Du]]; Case/hasP: Hu'; Exists u; RightBy Apply connect0.
    By Rewrite: (eqP Du); Apply maps_f; Case x.
  Pose qz := (Quiz (QaskR qa1 q2) (QaskR qa2 q1)).
  Step Eqz: (fband (walkqz (h false) qz)) =1 (fband (rqs_walk qs (maps h r))).
    Move=> u; Rewrite: /qz Dqs /= /qstepR !EhE /= !fband_cat /= cats0.
    By Repeat BoolCongr. 
  Exists (h false); Repeat Split.
      Rewrite: /fitqz /qz /= eqseq_adds fitq_cat /qstepR !EhE /= eqseq_adds.
      By Rewrite: eqd_sym Eqa1 Hq2 eqd_sym Eqa2.
    Rewrite (simple_perm Eqz); LeftBy Move: Uq; Rewrite: simple_cat; Case/and3P.
    By Rewrite: /qz Dqs /= cats0 !size_cat /= !addnS addnC /qstepR !EhE.
  Move=> u; Rewrite: Eqz; Apply/idP/idP=> [Hu].
    Move: Uq; Rewrite: simple_cat; Case/and3P=> [_ Uq _].
    Apply/hasP=> [[v Hv Huv]]; Case/hasP: Uq; Exists v; LeftDone.
    By Rewrite: -[q0](closed_connect (fbandF q0) Huv).
  Move: (Eq u); Rewrite: fband_cat (negbE Hu) orbF /setU /setC; Case/esym.
  Case Hu': (codom h u); RightDone; Apply/hasP; Exists u; RightBy Apply connect0.
  By Case/set0Pn: Hu' => [x Du]; Rewrite: (eqP Du); Apply maps_f; Case x.
Step [Hcp2 Hscp1]: (setU1 seq0 config_prog cp2) /\ (cubic_prog (Adds s cp1)).
  By Case: {}s Hscp2 Hqz' => //=; Case cp2; Split.
Move: {Hrec Hscp1}(Hrec Hcp2 ? Hscp1) => Hrec; Simpl in Hrec; Move: Hrec Arec Hqz'.
Case Dqs: qs => [|rq1 [|rq2 [|rq3 qs']]] //; Rewrite: -Dqs.
Pose h := (injcp cp1 2!(Adds s cp2)); Pose g' := (cpmap (Adds s cp2)).
Pose g := (cpmap cp2); Pose r := (cpring g).
Step Hh: (injective h) By Apply: (!injcp_inj).
Step EhE: (x : g') (edge (h x)) = (h (edge x)) By Move=> x; Apply: edge_injcp.
Step EhN: (x : g') (negb (cpring g' x)) -> (node (h x)) = (h (node x)).
  By Move=> x; Apply: node_injcp.
Step EhF: (x, y : g') (cface (h x) (h y)) = (cface x y).
  By Move=> x y; Apply: cface_injcp.
Move: (cpmap (catrev (Adds s cp2) cp1)) h Hh EhE EhN EhF {Hcp1} => g0.
Pose r0 := (cpring g0); Rewrite: ~/g'; Rewrite: /setU1 orFb in Hscp2.
Step Ur: (simple r).
  Rewrite: /r /g; Case/setU1P: Hcp2 => [[] | Hcp2] //.
  By Move: (cpmap_simple Hcp2); Rewrite: simple_cat; Case/and3P.
Pose simq := [q,q'; u : g0] (flatq q) = (flatq q') /\ (walkq u q) = (walkq u q').
Pose selq := [q, q', q'' : question] Cases q of Qask0 => q' | _ => q'' end.
Case: s Hscp2 (config_prog_cubic Hscp2) {Hcp2} => // [n||] Hscp2 Hcp2;
  Rewrite: /cpmap -/cpmap -/g -/r; Move=> h Hh EhE EhN EhF Hrec; Case.
    Rewrite: cpring_ecpR -/r -/r0 /= !maps_rot; Simpl in h; Pose hr := (maps h r).
    Rewrite: Dqs -Dqs; Move=> Hr Hr0 Uq Eq; Apply: Hrec {Hrec}.
    Pose r1 := (take n r); Pose r2 := (drop n r).
    Rewrite: /rotr (rqs_fit_size Hr) size_rot -size_drop -/r2 /rot.
    Pose qs1 := (drop (size r2) qs); Pose qs2 := (take (size r2) qs).
    Step [Hqs1 Hqs2]: (rqs_fit [x](h x) qs1 r1) /\ (rqs_fit [x](h x) qs2 r2).
      Apply: andP; Move: Hr; Rewrite: /rot -/r1 -/r2 /qs1 /qs2 andbC.
      Elim: {}r2 {}qs {qs' Dqs} => [|x r2' Hrec] [|rq qs']; Rewrite: // ?cats0 //=.
      By Move/and3P=> [Ha Hq Hqs]; Rewrite: Ha Hq /=; Auto.
    Pose pq2 := (rqs_walk qs2 (maps h r2)); Pose m2 := (size pq2).
    Pose pq1 := (rqs_walk qs1 (maps h r1)); Pose qs12 := (cat qs1 qs2).
    Step Dpq': (rqs_walk qs12 hr) = (rot m2 (rqs_walk qs (rot n hr))).
      Transitivity (cat pq1 pq2).
        Rewrite: /hr -(cat_take_drop n r) -/r1 -/r2 ~/qs12 ~/pq1.
        Elim: {}r1 qs1 Hqs1 => [|x r1' Hrec] [|rq qs1] //=.
        By Move/and3P=> [_ _ Hqs]; Rewrite: Hrec ?catA.
      Rewrite: -rot_size_cat ~/m2; Congr rot.
      Move: Hqs2; Rewrite: /hr -maps_rot /rot /pq1 /pq2 /qs1 /qs2 -/r1 -/r2.
      Elim: {}r2 {}qs {qs' Dqs} => [|x r' Hrec] [|rq qs'] //=.
      By Case/and3P=> *; Rewrite: -Hrec ?catA.
    Step Ehr: (maps [x](h x) r) = hr By Apply: eq_maps.
    Split; Auto; Rewrite: -/r -/r0 ?Ehr.
          Rewrite: -(cat_take_drop n r) -/r1 -/r2 /qs12.
          Elim: {}r1 {}qs1 Hqs1 => [|x r1' Hrec] [|rq qs1'] //=.
          Move/and3P=> [Ha Hq Hqs]; Rewrite: Ha Hq /=; Auto.
        Move=> u Hu; Apply: Hr0; Apply: etrans Hu; Congr andb.
        By Rewrite: /setU fband_rot.
      By Rewrite: Dpq' {1}/rot -catA simple_catCA catA cat_take_drop.
    By Move=> u; Rewrite: fband_cat Dpq' fband_rot -fband_cat Eq /setU fband_rot.
  Simpl in Hcp2; Def: Hgp := (cpmap_proper Hcp2); Rewrite: -/g in Hgp.
  Def: HgE := (cpmap_plain Hcp2); Def: Hg'E := (plain_ecpY g HgE).
  Rewrite: -/r0; Pose rY := (maps h (cpring (ecpY g))).
  Pose pY := (cat (rqs_walk qs rY) r0).
  Pose u0 := ((ecpY g) :: (dart ?)); Pose nu0 := (node u0).
  Step Hnu0: (cface nu0 (icpY g (node g))) By Apply: cface_node_ecpY.
  Pose h' := [x](h (icpY g x)); Pose rY' := (maps h' r).
  Step ErY : (fband rY) =1 (fband (Adds (h u0) rY')).
    Move=> u; Rewrite: /rY' /r head_cpring /rY cpring_ecpY -/u0 -/nu0 /= orbCA.
    Rewrite: -maps_comp; Do 2 Congr orb.
    By Rewrite: /h' !(Sface ? u); Apply: same_cface; Rewrite EhF.
  Pose r' := (drop (2) r); Pose au0 := (seq2 (node g) g).
  Step Eau0: (arity u0) = (2) By Apply: (order_cycle 3!(traject face u0 (2))).
  Step Eag: (x : g) (arity (icpY g x)) = (addn (fband au0 x) (arity x)).
    Pose bu0 := (maps edge (orbit face u0)).
    Step Ebu0: (fband bu0) =1 (fband (maps (icpY g) au0)).
      Move=> u; Rewrite: /au0 -adj_ecpY // /bu0 /fband has_maps.
      By Apply: eq_has => [v]; Rewrite: /comp Sface.
    Move=> x; Rewrite: /order -(cardIC bu0); Congr addn.
      Case Hx: (fband au0 x).
        Step Hbu0x: (fband bu0 (icpY g x)).
          Rewrite: Ebu0 /fband has_maps; Apply: etrans Hx.
          Apply: eq_has; Apply : cface_icpY.
        Rewrite: /fband in Hbu0x; Case/hasP: Hbu0x => [u Hbu0u Hxu].
        Rewrite: (cardD1 u) {1}/setI Hxu Hbu0u; Apply: eqP; Apply/set0Pn=> [[v]].
        Move/and3P=> [Huv Hxv Hbu0v]; Rewrite: (same_cface Hxu) in Hxv.
        Case/eqP: Huv; Apply: (!simple_cface) Hxv Hbu0u Hbu0v.
        Rewrite: (simple_perm Ebu0); RightBy Rewrite: /bu0 !size_maps size_orbit.
        Rewrite: (simple_maps (cface_icpY g)).
        Rewrite: /r (head_proper_cpring Hgp) -(cat1s g) -cat_adds seq2I in Ur.
        By Rewrite: simple_cat in Ur; Case/and3P: Ur.
      Apply: eqP; Apply/set0Pn=> [[u]]; Move/andP=> [Hxu Hbu0u].
      Step Hbu0x: (fband bu0 (icpY g x)) By Apply/hasP; Exists u.
      Rewrite: Ebu0 /fband has_maps in Hbu0x; Case/idP: Hx; Apply: etrans Hbu0x.
      By Apply: eq_has => [z]; Rewrite: /comp cface_icpY.
    Rewrite: -(card_image (icpY_inj 2!g)); Apply: eq_card => [u].
    Apply/andP/set0Pn => [[Hux Hu] | [y]].
      Step Hu0u: (negb (cface u0 u)).
        By Rewrite: Sface -(same_cface Hux) Sface /u0 cface_ecpY.
      Rewrite: /u0 cface_ecpY -/u0 in Hu0u.
      Rewrite: /bu0 /orbit -/(arity u0) Eau0 in Hu.
      Case: u Hu Hu0u Hux => //; Case=> // [y] _ _ Hxy; Exists y.
      By Rewrite: /setI /preimage set11 -(cface_icpY g).
    Case/andP; Rewrite: /preimage; Move/eqP=> Du; Rewrite: Du cface_icpY.
    By Split; LeftDone; Rewrite: /bu0 /orbit -/(arity u0) Eau0.
  Rewrite Dqs; Move=> Hqs Hr0 UpY EpY /=.
  Def DcqY: cqY := (rqs_Y rq1 rq3 qs'); Def DqsY: qsY := (cfquiz_Y rq1 rq2 cqY).
  Case: rq1 rq2 rq3 DcqY DqsY Hqs Dqs => [k1 a1 q1] [k2 a2 q2] [k3 a3 q3].
  Move=> DcqY DqsY Hqs Dqs HqY; Apply: Hrec {}HqY {Hrec}.
  Rewrite: /u0 cpring_ecpY /behead (head_proper_cpring Hgp) -/u0 -/nu0 in Hqs.
  Rewrite: maps_adds !rqs_fit_adds Eau0 (arity_cface Hnu0) in Hqs.
  Rewrite: -EhF in Hnu0; Rewrite: (arity_cface Hnu0) !Eag /= !connect0 in Hqs.
  Rewrite: addnS orbT /= !addnA !addn1 in Hqs.
  Case/and5P: Hqs => [Ea1 Hq1 Ea2 Hq2]; Move/and3P=> [Ea3 Hq3 Hqs].
  Step Hqs': (rqs_fit [x](h (icpY g x)) qs' r').
    Def Dea: ea := [x](arity (icpY g x)) =d (arity x).
    Step Hr': (all ea r').
      Apply/allP=> [x Hx]; Rewrite: Dea Eag //; Apply/eqP.
      Rewrite: /r (head_proper_cpring Hgp) -/r' -(cat1s g) -cat_adds seq2I in Ur.
      Rewrite: simple_cat -/r -/r' -/au0 in Ur; Case/and3P: Ur => [_ Ur _].
      By Rewrite: (negbE (hasPn Ur ? Hx)).
    Elim: r' {}qs' Hr' Hqs {Dqs Hr0} => [|x r' Hrec] [|rq qs''] //=.
    Move/andP=> [Ear' Hr']; Move/and3P=> [Ea Hq Hqs]; Rewrite: Dea /= in Ear'.
    By Rewrite: -(eqP Ear') Ea Hq Hrec.
  Pose v1 := (icpY g (node g)); Step Uv1: (negb (cpring u0 v1)).
    Rewrite: /u0 /v1 cpring_ecpY /= /setU1 /= (mem_maps (icpY_inj 2!g)).
    By Move: (simple_uniq Ur); Rewrite: {1 r}(head_cpring g); Case/andP.
  Step Eenv1: (edge (node (h v1))) = (h nu0).
    By Rewrite: /v1 (EhN ? Uv1) EhE /= set11.
  Step Eennv1: (edge (node (node (h v1)))) = (h u0).
    Rewrite: !EhN // ?EhE ?cpring_ecpY /= /setU1 ?set11 //=.
    By Apply/mapsP; Case.
  Step EpY': (fband pY) =1 (setU (setC (codom h')) (fband rY')).
    Step HrY'F: (fclosed face (setU (setC (codom h')) (fband rY'))).
      Apply: (intro_closed (Sface ?)) => [u v]; Case/eqP=> [] {v} Hu.
      Apply/norP; Rewrite: /setC negb_elim; Move=> [Hfu HfuF]; Move: Hu; 
      Rewrite: /setU (fclosed1 (fbandF rY')) (negbE HfuF) orbF; Case/set0Pn.
      Move: (iinv Hfu) (f_iinv Hfu) => x Dx; Rewrite: /h' in Dx.
      Exists (edge (node x)); Apply/eqP; Rewrite: /h'.
      Rewrite: -icpY_edge -icpY_node.
        Rewrite: -EhE -EhN; LeftBy Rewrite: Dx Eface.
        Rewrite: cpring_ecpY /= /setU1 /=; Apply/idP=> [HxF].
        Case/hasP: HfuF; Exists (face u); RightBy Apply connect0.
        Rewrite: /rY' -Dx; Apply mem_behead.
        By Rewrite: /h' (maps_comp h (icpY g)) !behead_maps; Apply maps_f.
      Apply/idP=> [HxF]; Case/hasP: HfuF; Exists (face u); RightBy Apply connect0.
      Rewrite: /rY' -Dx; Apply: maps_f.
      Rewrite: /r (head_proper_cpring Hgp) -(cat1s g) -cat_adds seq2I.
      By Rewrite: mem_cat /setU HxF.
    Move=> u; Rewrite: EpY {1}/setU {1}/setC ErY; Case Hu: (codom h u).
      Case: (fband_icpY (iinv Hu)) => [[x Hx] | Hu'].
        Rewrite: -EhF f_iinv in Hx; Rewrite: (closed_connect HrY'F Hx).
        Rewrite: [p](closed_connect (fbandF p) Hx) /setU /setC /= EhF Sface.
        By Rewrite: /u0 cface_ecpY -/(h' x) codom_f.
      Simpl; Congr orb; Rewrite: -EhF f_iinv in Hu'.
      Rewrite: Sface /u0 Hu'; Apply esym; Apply/idP=> [Hx].
      By Rewrite: -(f_iinv Hx) /h' EhF cface_ecpY in Hu'.
    Apply esym; Apply/orP; Left; Apply/idP=> [Hu'].
    By Rewrite: -(f_iinv Hu') /h' codom_f in Hu.
  Step Hr0': (sub_set (setD r0 (setU (codom h') (fband rY'))) good_ring_arity).
    Move=> u; Case/andP; Move/norP=> [Hh'u Hr'u] Hr0u.
    Case Hu: (cface (h u0) u).
      Rewrite: /good_ring_arity -(arity_cface Hu); Apply: not_bad_ring_arity.
      Rewrite: (eqP Ea2) /=; Apply/idP=> [Ha2].
      Rewrite: /pY simple_cat in UpY; Case/and3P: UpY; Clear; Case/hasP.
      Exists u; LeftDone; Apply/hasP; Exists (h u0); RightBy Rewrite Sface.
      Rewrite: Dqs /rY cpring_ecpY -/u0 -/nu0 /= mem_cat; Apply/orP; Right.
      Do 2 (Rewrite mem_cat; Apply/orP; Left); Move: HqY; Rewrite: DqsY.
      By Case k2; [Rewrite: /= setU11 | Rewrite: /= Ha2 qs0_notR].
    Apply: Hr0; Rewrite: /setD Hr0u /setU ErY fband_adds Sface Hu (negbE Hr'u).
    Step HuY: (fband pY u) By Rewrite: EpY' /setU /setC Hh'u.
    Rewrite: EpY /setU /setC ErY fband_adds Sface Hu (negbE Hr'u) orbF in HuY.
    By Rewrite: orbF HuY.
  Move: HqY; Rewrite: -/h' DqsY; Case Dk2: k2.
    Rewrite: /= small_qarityP; Pose qa2 := (small_qarity a2).
    Case: ((qa2::nat) =P (S (S a2))) => [Dqa2 | _]; RightBy Rewrite qs0_notR.
    Clear; Rewrite: -~Dqa2 in Ea2; Rewrite: -/v1 in Ea1.
    Pose q1' := (QaskLR qa2 q2 q1).
    Pose q1'' := (selq q1 (selq q2 (Qask1 qa2) (QaskL qa2 q2))
                          (selq q2 (QaskR qa2 q1) q1')).
    Change (rqs_ok h' (cqY q1'')).
    Step [Eq1 Eq1v1]: (simq q1'' q1' (node (h v1))).
      By Rewrite: /q1'' /q1' /simq; Case q1; Case: {}q2 => //= *; Rewrite: !cats0.
    Rewrite: /= /qstepR /qstepL Eennv1 Eenv1 in Eq1v1.
    Step Eq1''F: (fband (cat (rqs_walk (cqY q1'') rY') r0)) =1 (fband pY).
      Rewrite: /rY' /pY /rY cpring_ecpY /r /behead  (head_proper_cpring Hgp).
      Rewrite: -/r -/r' !maps_adds DcqY -/u0 -/nu0 Dqs Dk2 /rqs_Y.
      Rewrite: !rqs_walk_adds {1 2}/h' -/v1 -maps_comp !catA.
      Move=> u; Rewrite: !fband_cat; Do 4 Congr orb.
      Rewrite: (fband_seqn Hnu0) -!orbA; Congr orb.
      Rewrite: /= Eq1v1 /= fband_cat orbA orbC orbF; Do 2 Congr orb.
      By Rewrite: (cface1r (h u0)) -Eennv1 Enode.
    Split; Auto; Rewrite: -/r -/rY' -/r0.
        Rewrite: (head_proper_cpring Hgp) DcqY /=; Apply/and5P; Split; Auto.
        Rewrite: /h' -/v1 /fitq Eq1 Eq1v1 /= eqseq_adds fitq_cat.
        By Rewrite: -arity_face -Eennv1 Enode in Ea2; Rewrite: eqd_sym Ea2 Hq2.
      Rewrite: (simple_perm Eq1''F) // /rY' /pY /rY cpring_ecpY.
      Rewrite: /r /behead (head_proper_cpring Hgp) -/r -/r' !maps_adds.
      Rewrite: DcqY -/u0 -/nu0 Dqs Dk2 /rqs_Y !rqs_walk_adds {1 2}/h' -/v1.
      Rewrite: -maps_comp !size_cat /= Eq1v1 /= !size_cat !addnA; Do 4 Congr addn.
      Rewrite: !size_seqn -!addnA; Congr addn.
      By Symmetry; Rewrite addnC.
    By Move=> u; Rewrite: Eq1''F EpY'.
  Rewrite: /=; Case: (bad_ring_arity a2); LeftBy Rewrite qs0_notR.
  Case: {}q1 Dqs Hq1 Hq2; Rewrite: ?qs0_notR //.
    Case: {}q2; Rewrite: ?qs0_notR //.
      Move=> Dqs _ _ _.
      Step EqsF: (fband (cat (rqs_walk (cqY Qask0) rY') r0)) =1 (fband pY).
        Rewrite: /rY' /pY /rY cpring_ecpY /r /behead (head_proper_cpring Hgp).
        Rewrite: -/r -/r' !maps_adds DcqY -/u0 -/nu0 Dqs Dk2 /rqs_Y.
        Rewrite: !rqs_walk_adds {1 2}/h' -/v1 -maps_comp !catA.
      Move=> u; Rewrite: !fband_cat !orbF; Do 4 Congr orb.
      By Rewrite: (fband_seqn Hnu0).
      Split; Auto; Rewrite: -/r -/rY' -/r0.
          By Rewrite: (head_proper_cpring Hgp) DcqY /=; Apply/and4P; Split.
        Rewrite: (simple_perm EqsF) // /rY' /pY /rY cpring_ecpY.
        Rewrite: /r /behead (head_proper_cpring Hgp) -/r -/r' !maps_adds.
        Rewrite: DcqY -/u0 -/nu0 Dqs Dk2 /rqs_Y !rqs_walk_adds {1 2}/h' -/v1.
        Rewrite: -maps_comp !size_cat /= !addnA; Do 4 Congr addn.
        By Rewrite: !size_seqn !addn0.
      By Move=> u; Rewrite: EqsF EpY'.
    Move=> qa2l q2l Dqs _ Hq2 _.
    Step EqsF: (fband (cat (rqs_walk (cqY (QaskLL qa2l q2l)) rY') r0))
                  =1 (fband pY).
      Rewrite: /rY' /pY /rY cpring_ecpY /r /behead (head_proper_cpring Hgp).
      Rewrite: -/r -/r' !maps_adds DcqY -/u0 -/nu0 Dqs Dk2 /rqs_Y.
      Rewrite: !rqs_walk_adds {1 2}/h' -/v1 -maps_comp !catA.
      Move=> u; Rewrite: !fband_cat !orbF; Do 4 Congr orb.
      Rewrite: (fband_seqn Hnu0); Congr orb; Simpl.
      By Rewrite: /qstepL Eennv1 cface1r Enode.
    Split; Auto; Rewrite: -/r -/rY' -/r0.
        Rewrite: (head_proper_cpring Hgp) DcqY /=; Apply/and5P; Split; Auto.
        Move: Hq2; Rewrite: /fitq /= !eqseq_adds /h' -/v1 /qstepL Eennv1.
        By Rewrite: -{1 (node (h u0))}Enode arity_face.
      Rewrite: (simple_perm EqsF) // /rY' /pY /rY cpring_ecpY.
      Rewrite: /r /behead (head_proper_cpring Hgp) -/r -/r' !maps_adds.
      Rewrite: DcqY -/u0 -/nu0 Dqs Dk2 /rqs_Y !rqs_walk_adds {1 2}/h' -/v1.
      Rewrite: -maps_comp !size_cat /= !addnA; Do 4 Congr addn.
      By Rewrite: !size_seqn !addn0 /qstepL Eennv1.
    By Move=> u; Rewrite: EqsF EpY'.
  Case q2; Try By Rewrite qs0_notR.
  Move=> qa1r q1r Dqs Hq1 _ _.
  Step EqsF: (fband (cat (rqs_walk (cqY (QaskRR qa1r q1r)) rY') r0))
                =1 (fband pY).
    Rewrite: /rY' /pY /rY cpring_ecpY /r /behead (head_proper_cpring Hgp).
    Rewrite: -/r -/r' !maps_adds DcqY -/u0 -/nu0 Dqs Dk2 /rqs_Y.
    Rewrite: !rqs_walk_adds {1 2}/h' -/v1 -maps_comp !catA.
    Move=> u; Rewrite: !fband_cat !orbF; Do 4 Congr orb.
    Rewrite: (fband_seqn Hnu0); Congr orb; Simpl.
    By Rewrite: /qstepR Eenv1.
  Split; Auto; Rewrite: -/r -/rY' -/r0.
      Rewrite: (head_proper_cpring Hgp) DcqY /=; Apply/and5P; Split; Auto.
      By Move: Hq1; Rewrite: /fitq /= !eqseq_adds /h' -/v1 /qstepR Eenv1.
    Rewrite: (simple_perm EqsF) // /rY' /pY /rY cpring_ecpY.
    Rewrite: /r /behead (head_proper_cpring Hgp) -/r -/r' !maps_adds.
    Rewrite: DcqY -/u0 -/nu0 Dqs Dk2 /rqs_Y !rqs_walk_adds {1 2}/h' -/v1.
    Rewrite: -maps_comp !size_cat /= !addnA; Do 4 Congr addn.
    By Rewrite: !size_seqn !addn0 /qstepR Eenv1.
  By Move=> u; Rewrite: EqsF EpY'.
Simpl in Hcp2; Def: Hgp := (cpmap_proper Hcp2); Rewrite: -/g in Hgp.
Simpl in Hscp2; Def: Hgl := (cfmap_long Hscp2); Rewrite: -/g in Hgl.
Def: HgE := (cpmap_plain Hcp2); Def: Hg'E := (plain_ecpH g HgE).
Rewrite: -/r0; Pose rH := (maps h (cpring (ecpH g))).
Pose pH := (cat (rqs_walk qs rH) r0).
Pose u0 := ((ecpH g) :: (dart ?)); Pose nu0 := (node u0).
Pose v1 := (icpH g (node g)); Pose v2 := (icpH g g).
Pose v3 := (icpH g (face (edge g))).
Step Hnu0: (cface nu0 v1) By Apply: cface_node_ecpH.
Pose h' := [x](h (icpH g x)); Pose rH' := (maps h' r).
Pose r' := (drop (3) r); Pose au0 := (seq3 (node g) g (face (edge g))).
Step Dr: r = (cat au0 r') By Rewrite: /r head_long_cpring.
Step DrH: rH = (Adds (h nu0) (Adds (h u0) (Adds (h v3) (maps h' r')))).
  By Rewrite: /rH cpring_ecpH // -/r -/u0 -/nu0 Dr /= -maps_comp.
Step DrH': rH' = (Adds (h v1) (Adds (h v2) (Adds (h v3) (maps h' r')))).
  By Rewrite: /rH' Dr.
Step ErH : (fband (Adds (h v2) rH)) =1 (fband (Adds (h u0) rH')).
  Move=> u; Rewrite: DrH DrH' !fband_adds; BoolCongr.
  Rewrite orbCA; BoolCongr; Congr orb.
  By Rewrite: !(Sface ? u); Apply: same_cface; Rewrite EhF.
Step Eau0: (arity u0) = (3).
  Apply: (order_cycle 3!(traject face u0 (3))) => //=.
  By Rewrite: /eqdf /= Enode (negbE Hgp).
Step Eag: (x : g) (arity (icpH g x)) = (addn (fband au0 x) (arity x)).
  Pose bu0 := (maps edge (orbit face u0)).
  Step Ebu0: (fband bu0) =1 (fband (maps (icpH g) au0)).
    Move=> u; Rewrite: /au0 -adj_ecpH // /bu0 /fband has_maps.
    By Apply: eq_has => [v]; Rewrite: /comp Sface.
  Move=> x; Rewrite: /order -(cardIC bu0); Congr addn.
    Case Hx: (fband au0 x).
      Step Hbu0x: (fband bu0 (icpH g x)).
        Rewrite: Ebu0 /fband has_maps; Apply: etrans Hx.
        Apply: eq_has; Apply : cface_icpH.
      Rewrite: /fband in Hbu0x; Case/hasP: Hbu0x => [u Hbu0u Hxu].
      Rewrite: (cardD1 u) {1}/setI Hxu Hbu0u; Apply: eqP; Apply/set0Pn=> [[v]].
      Move/and3P=> [Huv Hxv Hbu0v]; Rewrite: (same_cface Hxu) in Hxv.
      Case/eqP: Huv; Apply: (!simple_cface) Hxv Hbu0u Hbu0v.
      Rewrite: (simple_perm Ebu0); RightBy Rewrite: /bu0 !size_maps size_orbit.
      Rewrite: (simple_maps (cface_icpH g)).
      By Rewrite: Dr simple_cat in Ur; Case/and3P: Ur.
    Apply: eqP; Apply/set0Pn=> [[u]]; Move/andP=> [Hxu Hbu0u].
    Step Hbu0x: (fband bu0 (icpH g x)) By Apply/hasP; Exists u.
    Rewrite: Ebu0 /fband has_maps in Hbu0x; Case/idP: Hx; Apply: etrans Hbu0x.
    By Apply: eq_has => [z]; Rewrite: /comp cface_icpH.
  Rewrite: -(card_image (icpH_inj 2!g)); Apply: eq_card => [u].
  Apply/andP/set0Pn => [[Hux Hu] | [y]].
    Step Hu0u: (negb (cface u0 u)).
      By Rewrite: Sface -(same_cface Hux) Sface /u0 cface_ecpH.
    Rewrite: /u0 cface_ecpH // -/u0 in Hu0u.
    Rewrite: /bu0 /orbit Eau0 in Hu.
    Case: u Hu Hu0u Hux => //; Case=> //; Case=> // [y] _ _ Hxy; Exists y.
    By Rewrite: /setI /preimage set11 -(cface_icpH g).
  Case/andP; Rewrite: /preimage; Move/eqP=> Du; Rewrite: Du cface_icpH.
  By Split; LeftDone; Rewrite: /bu0 /orbit Eau0.
Rewrite Dqs; Move=> Hqs Hr0 UpH EpH /=.
Def DcqH: cqH := (rqs_H rq1 rq3 qs'); Def DqsH: qsH := (cfquiz_H rq1 rq2 cqH).
Case: rq1 rq2 rq3 DcqH DqsH Hqs Dqs => [k1 a1 q1] [k2 a2 q2] [k3 a3 q3].
Move=> DcqH DqsH Hqs Dqs HqH; Apply: Hrec {}HqH {Hrec}.
Rewrite: /u0 cpring_ecpH -/u0 -/nu0 // -/r Dr /au0 /seq3 /seq2 !cat_adds in Hqs.
Rewrite: cat1s /drop maps_adds -/v3 !rqs_fit_adds Eau0 (arity_cface Hnu0) in Hqs.
Rewrite: -EhF in Hnu0; Rewrite: (arity_cface Hnu0) in Hqs.
Rewrite: {2}/v1 {2}/v3 !Eag /= !connect0 in Hqs.
Rewrite: 2!addnS !orbT /= !addnA !addn1 in Hqs.
Case/and5P: Hqs => [Ea1 Hq1 Ea2 Hq2]; Move/and3P=> [Ea3 Hq3 Hqs].
Step Hqs': (rqs_fit [x](h (icpH g x)) qs' r').
  Def Dea: ea := [x](arity (icpH g x)) =d (arity x).
  Step Hr': (all ea r').
    Apply/allP=> [x Hx]; Rewrite: Dea Eag //; Apply/eqP.
    Rewrite: Dr simple_cat in Ur; Case/and3P: Ur => [_ Ur _].
    By Rewrite: (negbE (hasPn Ur ? Hx)).
  Elim: {}r' {}qs' Hr' Hqs {Dqs Hr0} => [|x r'' Hrec] [|rq qs''] //=.
  Move/andP=> [Ear'' Hr'']; Move/and3P=> [Ea Hq Hqs]; Rewrite: Dea /= in Ear''.
  By Rewrite: -(eqP Ear'') Ea Hq Hrec.
Step UrH: (x : g) (cpring u0 (icpH g x)) = (drop (2) r x).
  Move=> x; Rewrite: /u0 cpring_ecpH //= /setU1 /= (mem_maps (icpH_inj 2!g)).
  By Rewrite: /long_cpring /= Enode (negbE Hgp).
Step Uv1: (negb (cpring u0 v1)).
  Move: (simple_uniq Ur).
  By Rewrite: {1 r}(head_proper_cpring Hgp) /v1 UrH; Case/andP; Case/norP.
Step Uv2: (negb (cpring u0 v2)).
  Move: (simple_uniq Ur).
  By Rewrite: {1 r}(head_proper_cpring Hgp) /v2 UrH ; Case/and3P.
Step Eenv1: (edge (node (h v1))) = (h nu0).
  Rewrite: (EhN ? Uv1) EhE.
  By Rewrite: /v1 /nu0 /= !set11 /long_cpring /= Enode (negbE Hgp).
Step Hnv1: (cface (node (h v1)) (h u0)).
  By Rewrite: EhN // EhF Sface /u0 cface_ecpH //= !set11 /= /setU1 !orbT.
Step Eennv2: (edge (node (node (h v2)))) = (h u0).
  Rewrite: EhN // /v2 /= (negbE Hgp) /= !set11 /= EhN ?EhE //.
  Rewrite: cpring_ecpH // /= /setU1 /= /long_cpring /= Enode (negbE Hgp) /=.
  By Apply/mapsP; Case.
Step EpH': (fband (Adds (h v2) pH)) =1 (setU (setC (codom h')) (fband rH')).
  Step HrH'F: (fclosed face (setU (setC (codom h')) (fband rH'))).
    Apply: (intro_closed (Sface ?)) => [u v]; Case/eqP=> [] {v} Hu.
    Apply/norP; Rewrite: /setC negb_elim; Move=> [Hfu HfuF]; Move: Hu; 
    Rewrite: /setU (fclosed1 (fbandF rH')) (negbE HfuF) orbF; Case/set0Pn.
    Move: (iinv Hfu) (f_iinv Hfu) => x Dx; Rewrite: /h' in Dx.
    Exists (edge (node x)); Apply/eqP; Rewrite: /h'.
    Rewrite: -icpH_edge -icpH_node.
      Rewrite: -EhE -EhN; LeftBy Rewrite: Dx Eface.
      Rewrite: -/u0 UrH; Apply/idP=> [HxF].
      Case/hasP: HfuF; Exists (face u); RightBy Apply connect0.
      Rewrite: /rH' -Dx; Apply (!mem_drop (2)).
      By Rewrite: -maps_drop; Apply: maps_f.
    Apply/idP=> [HxF]; Case/hasP: HfuF; Exists (face u); RightBy Apply connect0.
    Rewrite: /rH' -Dx; Apply: maps_f.
    By Rewrite: Dr mem_cat /au0 /setU HxF.
  Move=> u; Rewrite: fband_adds EpH {1}/setU {1}/setC orbCA -fband_adds ErH.
  Case Hu: (codom h u).
    Case: (fband_icpH (iinv Hu)) => [[x Hx] | Hu'].
      Rewrite: -EhF f_iinv in Hx; Rewrite: (closed_connect HrH'F Hx).
      Rewrite: [p](closed_connect (fbandF p) Hx) /setU /setC /= EhF Sface.
      By Rewrite: /u0 cface_ecpH // -/(h' x) codom_f.
    Simpl; Congr orb; Rewrite: -EhF f_iinv in Hu'.
    Rewrite: Sface /u0 Hu'; Apply esym; Apply/idP=> [Hx].
    By Rewrite: -(f_iinv Hx) /h' EhF cface_ecpH in Hu'.
  Apply esym; Apply/orP; Left; Apply/idP=> [Hu'].
  By Rewrite: -(f_iinv Hu') /h' codom_f in Hu.
Step Hr0': (sub_set (setD r0 (setU (codom h') (fband rH'))) good_ring_arity).
  Move=> u; Case/andP; Move/norP=> [Hh'u Hr'u] Hr0u.
  Case Hu: (cface (h u0) u).
    Rewrite: /good_ring_arity -(arity_cface Hu); Apply: not_bad_ring_arity.
    Rewrite: (eqP Ea2) {3 S}lock /= -lock; Apply/idP=> [Ha2]; Simpl in Ha2.
    Rewrite: /pH simple_cat in UpH; Case/and3P: UpH; Clear; Case/hasP.
    Exists u; LeftDone; Apply/hasP; Exists (h u0); RightBy Rewrite Sface.
    Rewrite: Dqs DrH !rqs_walk_adds mem_cat; Apply/orP; Right.
    Do 2 (Rewrite mem_cat; Apply/orP; Left); Move: HqH; Rewrite: DqsH.
    By Case k2; Rewrite: /= ?setU11 // Ha2 /= qs0_notR.
  Apply: Hr0; Rewrite: /setD Hr0u /setU.
  Step HuH: (fband (Adds (h v2) pH) u) By Rewrite: EpH' /setU /setC Hh'u.
  Step Hur: (negb (fband (Adds (h v2) rH) u)).
    By Rewrite: ErH fband_adds Sface Hu.
  Rewrite: fband_adds EpH /setU /setC orbCA -fband_adds (negbE Hur) orbF in HuH.
  Rewrite: fband_adds in Hur; Case/norP: Hur => [_ Hur].
  By Rewrite: (negbE Hur) orbF HuH.
Step HrHv2: (negb (fband rH (h v2))).
  Rewrite: DrH !fband_adds Sface (same_cface Hnu0) Sface !EhF /h' /fband.
  Rewrite: (maps_comp h (icpH g)) has_maps (eq_has 2!(comp ? h) (EhF v2)).
  Rewrite: orbCA Sface /u0 cface_ecpH // orFb.
  Rewrite: /v1 /v2 /v3 !cface_icpH has_maps.
  Rewrite: (eq_has 2!(comp ? (icpH g)) (cface_icpH g g)).
  Move: Ur; Rewrite: Dr simple_recI /= Sface; Case/and3P.
  By Move/norP => [Ung _] Ug _; Apply/norP; Split.
Step HpHv2: (negb (fband pH (h v2))) By Rewrite: EpH /setU /setC codom_f.
Step Uv2pH: (simple (Adds (h v2) pH)) By Rewrite: simple_adds HpHv2.
Step Eav2: (arity (h v2)) = (S (arity g)).
  Transitivity (arity v2); RightBy Rewrite: /v2 Eag /= connect0 orbT.
  Rewrite: /order -(card_image Hh); Apply: eq_card => [u].
  Apply/idP/idP=> [Hu | ];
    RightBy Case/set0Pn=> [x]; Case/andP; Move/eqP=> Du; Rewrite: Du EhF.
  Rewrite: (closed_connect (fbandF pH) Hu) EpH /setU /setC in HpHv2.
  Rewrite: -(closed_connect (fbandF rH) Hu) (negbE HrHv2) orbF negb_elim in HpHv2.
  By Rewrite: -(f_iinv HpHv2) (image_f Hh) -EhF f_iinv.
Move: HqH; Rewrite: -/h' DqsH; Case Dk2: k2.
  Rewrite: /cfquiz_H small_qarityP; Pose qa2 := (small_qarity (S a2)).
  Case: ((qa2::nat) =P (S (S (S a2)))) => [Dqa2 | _]; RightBy Rewrite qs0_notR.
  Rewrite: -~Dqa2 in Ea2; Rewrite: if_negb.
  Pose q1' := (QaskR qa2 q1); Pose q2' := (QaskL qa2 q2).
  Step Hq1': (q : question) q2 = Qask0 -> (simq q q1' (node (h v1))) ->
    (rqs_ok h' (cqH q q2)).
    Move=> q Dq2 [Eq Eqv1]; Rewrite: /= /qstepR Eenv1 in Eqv1.
    Step EqsF:
        (fband (cat (rqs_walk (cqH q q2) rH') r0)) =1 (fband (Adds (h v2) pH)).
      Move=> u; Rewrite: /pH Dqs Dk2 DrH' DrH DcqH Dq2 /= Eqv1.
      Rewrite: !fband_cat !fband_adds !fband_cat !orbA; Do 4 Congr orb.
      Rewrite: (fband_seqn Hnu0) -!orbA !(Sface ? u) (same_cface Hnv1).
      By Repeat BoolCongr.
    Split; Auto; Rewrite: -/r -/r0 -/rH'.
        Rewrite: Dr DcqH Dq2 /= {-6}/h' -/v1 -/v2 -/v3 Hq3 Eav2 set11.
        Apply/and5P; Split; Auto.
        By Rewrite: /fitq Eq Eqv1 /= eqseq_adds (arity_cface Hnv1) eqd_sym Ea2.
      Rewrite: (simple_perm EqsF) // DrH' /pH DrH Dqs Dq2 Dk2 DcqH /=.
      Rewrite: !size_cat /= !size_cat !size_seqn Eqv1 /=.
      By NatNorm; Repeat NatCongr.
    By Move=> u; Rewrite: EqsF EpH'.
  Step Hq2': (q : question) q1 = Qask0 -> (simq q q2' (node (h v2))) ->
    (rqs_ok h' (cqH q1 q)).
    Move=> q Dq1 [Eq Eqv2]; Rewrite: /= /qstepL Eennv2 in Eqv2.
    Step EqsF:
        (fband (cat (rqs_walk (cqH q1 q) rH') r0)) =1 (fband (Adds (h v2) pH)).
      Move=> u; Rewrite: /pH Dqs Dk2 DrH' DrH DcqH Dq1 /= Eqv2 !cats0.
      Rewrite: !fband_cat !fband_adds !fband_cat fband_adds !orbA; Do 5 Congr orb.
      Rewrite: (fband_seqn Hnu0) -!orbA orbCA; Do 2 Congr orb.
      By Rewrite: (cface1r (h u0)) -Eennv2 Enode. 
    Split; Auto; Rewrite: -/r -/r0 -/rH'.
        Rewrite: Dr DcqH Dq1 /= {-6}/h' -/v1 -/v2 -/v3 Hq3 Eav2 set11.
        Apply/and5P; Split; Auto.
        Rewrite: /fitq Eq Eqv2 /= eqseq_adds -{(node (h v2))}Enode Eennv2.
        By Rewrite: arity_face eqd_sym Ea2.
      Rewrite: (simple_perm EqsF) // DrH' /pH DrH Dqs Dq1 Dk2 DcqH /=.
      Rewrite: !size_cat /= !size_cat !size_seqn Eqv2 /=.
      By NatNorm; Repeat NatCongr.
    By Move=> u; Rewrite: EqsF EpH'.
  Step Hsimq: (q : question; u : g0) (simq q q u) By Split. 
  Case Dq1: q1 Hq1' Hq2'; Case Dq2: q2; Auto; Try By Rewrite qs0_notR.
  By Rewrite: ~/q1' ~/q2' ~Dq1 ~Dq2; Case: {}k1 => [H _| _ H] _; Apply: H.
Rewrite: /cfquiz_H; Case: (bad_ring_arity (S a2)); LeftBy Rewrite qs0_notR.
Case Dq1: q1; Rewrite: ?qs0_notR //; Case Dq2: q2; Rewrite: ?qs0_notR //.
Step EqsF:
  (fband (cat (rqs_walk (cqH Qask0 Qask0) rH') r0)) =1 (fband (Adds (h v2) pH)).
  Move=> u; Rewrite: /pH Dqs Dk2 DrH' DrH DcqH Dq1 Dq2 /= !cats0.
  Rewrite: !fband_cat !fband_adds !fband_cat !orbA; Do 4 Congr orb.
  By Rewrite: (fband_seqn Hnu0) orbC.
Split; Auto; Rewrite: -/r -/r0 -/rH'.
    Rewrite: Dr DcqH /= {-5}/h' -/v1 -/v2 -/v3 Hq3 Eav2 set11 /=.
    By Apply/and3P; Split.
  Rewrite: (simple_perm EqsF) // DrH' /pH DrH Dqs Dq1 Dq2 Dk2 DcqH /=.
  Rewrite: !size_cat /= !size_cat !size_seqn /=.
  By NatNorm; Repeat NatCongr.
By Move=> u; Rewrite: EqsF EpH'.
Qed.

Lemma embeddable_cfquiz : (embeddable (cfring cf)).
Proof.
Split; Try Exact Hrad2.
  Def: Hcpq := (config_prog_cubic Hcp); Repeat Split.
  By Apply: cpmap_plain.
  By Apply: cpmap_cubic.
  By Apply: ucycle_rev_cpring.
  By Apply: cpmap_connected.
  By Move: (cpmap_simple Hcp); Rewrite: simple_cat -simple_rev; Case/and3P.
  By Apply: cpmap_planar.
  By Apply: cpmap_bridgeless.
Apply/allP=> [x Hx]; Case: {}cfquizP => [H _]; Apply: H {H}.
By Rewrite: -mem_rev.
Qed.

Lemma valid_cfquiz : (EX u | (valid_quiz (cfring cf) u cfquiz)).
Proof.
Case: {}cfquizP => [_ [u [Hcqz Hu Uqz Eqz]]]; Exists u; Split; Auto.
By Move=> v; Rewrite: ~{u Hcqz Hu Uqz}Eqz /kernel /setC -fband_rev.
Qed.

End ConfigQuiz.

Unset Implicit Arguments.
