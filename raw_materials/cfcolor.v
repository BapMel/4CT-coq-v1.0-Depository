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

Set Implicit Arguments.

(* Compute the set of colorings of a configuration ring, directly from the   *)
(* contruction program. The algorithm handles the six kinds of steps, as it  *)
(* is also used to color contracts and explicit configurations.              *)

(* First, the optimized all-in-one production of the tree branch, directly   *)
(* from the ring trace.                                                      *)

Section Cpbranch2.

Variable h : color -> ctree -> ctree.

Fixpoint cfcbr2 [et : colseq] : ctree :=
  if et is (Adds e et') then (h e (cfcbr2 et')) else ctree_simple_leaf.

End Cpbranch2.

Definition ctree_cons_perm [g : color -> color] : color -> ctree -> ctree :=
  let cte = ctree_cons_e in
  (palette (cte (g Color0)) (cte (g Color1)) (cte (g Color2)) (cte (g Color3))).

Section Cpbranch1.

Variable g : color -> color.

Fixpoint cfcbr1 [et : colseq] : ctree :=
  if et is (Adds e et') then
    Cases (g e) of
      Color0 => Ctree_empty
    | Color1 => (ctree_cons1 (cfcbr1 et'))
    | Color2 => (ctree_cons2 (cfcbr2 (ctree_cons_perm g) et'))
    | Color3 => (ctree_cons2 (cfcbr2 (ctree_cons_perm (comp Eperm132 g)) et'))
    end
  else ctree_simple_leaf.

End Cpbranch1.

Definition cpbranch [et : colseq] : ctree :=
  if et is (Adds _ (Adds e et')) then
    if e =d Color0 then Ctree_empty else (cfcbr1 (edge_rot e) et')
  else Ctree_empty.

(* The coloring procedure uses higher-order programming : we first create a  *)
(* generic iterator over all equivalence classes of colorings of a map given *)
(* by a construction program, then apply it to cpbranch. The iterator is    *)
(* specialized to ctrees, and computes the union of all the trees returned   *)
(* by the function.                                                          *)

Definition cpcolor1 [s : cpstep; f : colseq -> ctree; et : colseq] : ctree :=
  let f2 = [c; et'](f (Adds c (Adds c et'))) in
  Cases s et of
    (CpR n) _ =>
    (f (rot n et))
  | CpR' _ =>
    if (leq (size et) (1)) then Ctree_empty else (f (rotr (1) et))
  | CpU _ =>
    (ctree_union (f2 Color1 et) (ctree_union (f2 Color2 et) (f2 Color3 et)))
  | CpK (Adds e1 (Adds e2 et')) =>
    if e1 =d e2 then Ctree_empty else (f (Adds (addc e1 e2) et'))
  | CpY (Adds e1 et') =>
    let e2 = (Eperm231 e1) in let e3 = (Eperm312 e1) in
    (ctree_union (f (Adds e2 (Adds e3 et'))) (f (Adds e3 (Adds e2 et'))))
  | CpH (Adds e1 (Adds e2 et')) =>
    if e1 =d e2 then (ctree_union (f2 (Eperm231 e1) et') (f2 (Eperm312 e1) et'))
    else (f (Adds e2 (Adds e1 et')))
  | CpA (Adds e1 (Adds e2 et')) =>
    if e1 =d e2 then (f if et' is Seq0 then et else et') else Ctree_empty
  | _ _ => Ctree_empty
  end.

(* For the very first steps, we can examine fewer colorings. *)

Fixpoint cpcolor0 [cp : cprog] : ctree :=
  let cpcol = (foldr cpcolor1 cpbranch) in
  Cases cp of
    (Adds (CpR _) cp') =>
    (cpcolor0 cp')
  | (Adds CpY cp') =>
    (cpcol cp' (seq3 Color1 Color2 Color3))
  | (Adds CpU cp') =>
    (ctree_union (cpcol cp' (seq4 Color1 Color1 Color2 Color2))
                 (cpcol cp' (seq4 Color1 Color1 Color1 Color1)))
  | _ =>
    (cpcol cp (seq2 Color1 Color1))
  end.

Definition cpcolor [cp : cprog] : ctree := (ctree_cons_rot (cpcolor0 (rev cp))).

(* Basic correctness lemmatas first. *)

Lemma cpbranch_spec : (et : colseq)
  (cpbranch et) = (ctree_of_ttail (etail (behead et))).
Proof.
Move=> [|e0 [|e1 et]] {e0}//=.
Rewrite: /etail /etrace_perm /even_trace /ttail /proper_trace /head_color /head.
Case: (e1 =d Color0) => //; Move/edge_rot: e1 => g /=.
Elim: et => //= [e et Hrec] //=; Case/g: e => //=; Case: Hrec; First [
  By Case (even_tail (permt g et))
| By Congr ctree_cons2; Elim: et {Hrec} => //= [e et []]; Case e].
Qed.

(* The main coloring invariant. *)

Section CprogColoringCorrectness.

Variable et0 : colseq.

Section CpcolInvariant.

Variables cp1, cp2 : cprog; f : colseq -> ctree; k : (cpmap cp2) -> color.

Definition cp_ht0 : nat := (pred (pred (cprsize (catrev cp2 cp1)))).

Definition cp_tr0 [k0 : (cpmap (catrev cp2 cp1)) -> color] : Prop :=
  (ttail et0) = (eptrace (rot (1) (maps k0 (cpring (cpmap (catrev cp2 cp1)))))).

Inductive cp_extcol : Set :=
  CpExtcol : [et := (trace (maps k (cpring (cpmap cp2))))]
    (ctree_proper cp_ht0 (f et)) ->
    (reflect
      (EX k0 | (coloring k0) /\ (cp_tr0 k0) & (comp k0 (injcp cp1 2!cp2)) =1 k)
      (ctree_mem (f et) (ttail et0))) ->
    cp_extcol.

End CpcolInvariant.

Section GlobalColoring.

Variables cp1, cp2 : cprog; k0 : (cpmap (catrev cp2 cp1)) -> color.

Lemma gcol_perm : 
  (coloring k0) /\ (cp_tr0 k0) -> 
  (c : color; h : edge_perm) [k := [x](addc c (h (k0 x)))]
  (coloring k) /\ (cp_tr0 k).
Proof.
Move=> [Hk0 Ek0] c h k; Split.
  Apply: (coloring_inj 2!(comp (addc c) h)) Hk0 => //.
  Apply: inj_comp; [Apply inj_addc | Apply permc_inj].
Rewrite: /cp_tr0 /eptrace (maps_comp (addc c) (comp h k0)) (maps_comp h k0).
By Rewrite: -2!maps_rot ptrace_addc -/(permt h) ptrace_permt etail_permt.
Qed.

Lemma gcol_cface : (coloring k0) -> [k := [x](k0 (injcp cp1 x))]
  (x, y : (cpmap cp2)) (cface x y) -> (k x) = (k y).
Proof.
Move=> [_ Hk0F] k x y Hxy; Apply: (fconnect_invariant Hk0F).
By Apply sub_cface_injcp.
Qed.

Lemma gcol_adj : (coloring k0) -> [k := [x](k0 (injcp cp1 x))]
  (x : (cpmap cp2); p : (seq (cpmap cp2))) (adj x) =1 (fband p) ->
  (all [y](negb (k y) =d (k x)) p).
Proof.
Move=> [Hk0E Hk0F] /= x p Dp; Apply/allP=> [y Hy]; Apply/negPf.
Step Hxy: (adj x y) By Rewrite: Dp (subsetP (ring_fband p)).
Case/adjP: (sub_adj_injcp cp1 Hxy) => [u Hxu Huy].
Rewrite: (fconnect_invariant Hk0F Hxu) -(fconnect_invariant Hk0F Huy).
Apply: Hk0E.
Qed.
 
End GlobalColoring.

Section TraceCpring.

Variables g : hypermap; x0 : g; k : g -> color.
Hypothesis Hk : (coloring k).
Local et : colseq := (trace (maps k (cpring x0))).

Lemma memc0_trace_cpring : (et Color0) = false.
Proof.
Move: {}Hk => [HkE HkF]; Rewrite: -mem_rev -(mem_rot (1)) /et -trace_rev.
Rewrite: -maps_rev -urtrace_trace urtrace_rot mem_rot.
Case: (rev (cpring x0)) (cycle_rev_cpring x0) => [|x p] //.
Rewrite: (cycle_path x) {path}lock /urtrace {2 maps}lock /= last_maps -!lock.
Elim: {x p}(Adds x p) (last x p) => [|y p Hrec] x //=; Move/andP=> [Dy Hp].
Rewrite: /setU1 (Hrec ? Hp) orbF -{x}Enode (eqP Dy) (eqcP (HkF (edge y))).
By Rewrite: -eq_addc0; Apply: HkE.
Qed.

Lemma coloring_proper_cpring : (proper_cpring x0).
Proof.
Move: memc0_trace_cpring; Rewrite: /et size_proper_cpring ltnNge head_cpring.
By Case (behead (cpring x0)).
Qed.

Local e1 : color := (addc (k (node x0)) (k x0)).
Local e2 : color := (addc (k x0) (k (face (edge x0)))).
Local et'' : colseq :=
  (ptrace (maps k (add_last (drop (2) (cpring x0)) (node x0)))).

Lemma trace_cpring_eq : et = (Adds e1 (Adds e2 et'')).
Proof.
Move: (size_long_cpring x0).
Rewrite: /et (head_proper_cpring coloring_proper_cpring) ltnNge.
Rewrite: -urtrace_trace /= rot1_adds /urtrace last_add_last /= /et''.
Case Dcp: {1}(drop (2) (cpring x0)) => [|z p].
  By Rewrite: Dcp /e1 /e2 /=; Case/eqP.
By Move/head_long_cpring {Dcp} => Dcp {z p}; Rewrite: -maps_add_last Dcp.
Qed.

Lemma proper_trace_cpring : (proper_trace (behead et)).
Proof.
Move: {}memc0_trace_cpring; Rewrite trace_cpring_eq.
By Case/norP; Clear; Case/norP.
Qed.

End TraceCpring.

Section Cpcol1Inv.

Variables cp1, cp2 : cprog.
Local g2 := (cpmap cp2).
Variable k : g2 -> color.
Hypothesis Hk : (coloring k).
Local et : colseq := (trace (maps k (cpring g2))).

Remark Hetc0 : (et Color0) = false. Proof. Exact (memc0_trace_cpring ? Hk). Qed.

Remark Hg2p : (proper_cpring g2). Proof. Exact (coloring_proper_cpring ? Hk). Qed.

Local e1 : color := (addc (k (node g2)) (k g2)).
Local e2 : color := (addc (k g2) (k (face (edge g2)))).
Local et'' : colseq :=
  (ptrace (maps k (add_last (drop (2) (cpring g2)) (node g2)))).
Local et' : colseq := (Adds e2 et'').

Remark Det : et = (Adds e1 et'). Proof. Exact (trace_cpring_eq ? Hk). Qed.

Remark Hetp : (proper_trace et').
Proof. By Move: (proper_trace_cpring g2 Hk); Rewrite: -/et Det. Qed.

Lemma cpbranch_correct : (cp_extcol seq0 cpbranch k).
Proof.
Split; Rewrite: /cp_ht0 /cp_tr0 /= -/g2 -/et cpbranch_spec.
  Rewrite: -size_ring_cpmap -/g2 -(size_maps k) -size_trace -/et Det /=.
  Apply ctree_of_ttail_proper; Case: (etail_perm Hetp) => [g Eg].
  By Move: (congr size Eg); Rewrite: /permt size_maps /=; Injection=> [].
Step Heet: (negb (etail (behead et) Color0)).
  Move: (etail_perm Hetp) {}Hetc0 => [g Eg].
  By Rewrite: Det {et'}lock /= /setU1 -lock -(memc0_permt g) Eg; Case/norP.
Apply: (iffP (ctree_of_ttail_mem ? Heet)).
  Move=> D0; Exists k; RightDone; Split; Rewrite: // /eptrace ~D0; Congr etail.
  By Rewrite: /et (head_proper_cpring Hg2p) -urtrace_trace.
Case=> [k0 [_ Det0] Dk]; Rewrite: ~Det0 /eptrace /et ~{k0 Dk}(eq_maps 3!k0 Dk).
By Rewrite: (head_proper_cpring Hg2p) -urtrace_trace.
Qed.

Lemma cpcolor1U_correct : (f : colseq -> ctree)
  ((k' : (cpmap (Adds CpU cp2)) -> color)
     (coloring k') -> (cp_extcol cp1 f k')) ->
  (cp_extcol (Adds CpU cp1) (cpcolor1 CpU f) k).
Proof.
Rewrite: /cpmap -/cpmap -/g2.
Pose k' := [e; u]
  if pick x in [x](cface u (icpU g2 x)) then (k x) else (addc e (k (node g2))).
Step Hk'F: (e : color) (invariant face (k' e)) =1 (ecpU g2).
  Move=> e u; Apply/eqP; Congr [w](if w is (Some x) then (k x) else ?).
  By Apply: eq_pick => [v]; Rewrite: -cface1.
Step Ek': (e : color; x : g2) (k' e (icpU g2 x)) = (k x).
  Move=> e x; Rewrite: /k' -(eq_pick 2!(cface x)).
    Case: (pickP (cface x)) {}Hk => [y Hxy | Hx] [_ HkF].
      Exact (esym (fconnect_invariant HkF Hxy)).
    By Case/idP: (Hx x); Apply connect0.
  By Move=> y; Rewrite: cface_icpU.
Step Ek'X: (e : color) (k' e (ecpU g2)) = (addc e (k (node g2))).
  Move=> e; Rewrite: /k'; Case: (pickP [x](cface (ecpU g2) (icpU g2 x))) => //.
  By Move=> x; Rewrite: cface_ecpU.
Step Ek'Xe: (e : color) (k' e (edge (ecpU g2))) = (k (node g2)).
  Move=> e; Rewrite: -(Ek' e); Apply: (fconnect_invariant (Hk'F e)).
  Apply: fconnect1.
Step Hk': (e : color) (negb e =d Color0) -> (coloring (k' e)).
  Move=> e He; Step Hk'EX: (invariant edge (k' e) (ecpU g2)) = false.
    By Rewrite: /invariant Ek'X Ek'Xe addcC eq_addc0 addc_inv (negbE He).
  Split; Auto; Move=> [||x] //; Rewrite: /invariant; LeftBy Rewrite eqd_sym.
  By Rewrite: -/(icpU g2 x) -icpU_edge !Ek'; Case: {}Hk => [HkE _]; Apply: HkE.
Step Ek't: (e : color)
  (trace (maps (k' e) (cpring (ecpU g2)))) = (Adds e (Adds e et)).
  Move=> e; Rewrite: cpring_ecpU !maps_adds Ek'X addcC -maps_comp.
  Simpl in Ek'Xe; Rewrite: (eq_maps 3!(comp (k' ?) ?) (Ek' e)) /= Ek'Xe.
  By Rewrite: addc_inv /et head_cpring /= addcC addc_inv /ctrace /= addc_inv.
Move=> f Hf; Case: (Hf ? (Hk' Color3 (erefl ?))).
Case: (Hf ? (Hk' Color2 (erefl ?))); Case: {Hf}(Hf ? (Hk' Color1 (erefl ?))).
Rewrite: /cpmap -/cpmap !Ek't; Move=> Ht1 Et1 Ht2 Et2 Ht3 Et3.
Split; LeftBy Repeat Apply: ctree_union_proper.
Rewrite: /cpcolor1 !(ctree_mem_union 1!(cp_ht0 cp1 (Adds CpU cp2))) //;
  RightBy Apply: ctree_union_proper.
Apply: (iffP or3P).
  Case; [Case/Et1 | Case/Et2 | Case/Et3]; Rewrite: /comp; Move=> k0 Hk0 Dk';
  By Exists k0; RightBy Move=>x; Rewrite: /comp /= Dk' Ek'.
Move=> [k0 Hk0 Dk]; Case: {}Hk0=> [Hk0c _].
Pose ic2 := (injcp cp1 2!(Adds CpU cp2)).
Pose e0 := (addc (k0 (ic2 (ecpU g2))) (k (node g2))).
Step Dk': (comp k0 ic2) =1 (k' e0).
  Rewrite: /comp /cpmap -/cpmap -/g2; Move=> u.
  Case: (fband_icpU u) => [[x Hx] | Hu].
    Rewrite: (fconnect_invariant (Hk'F e0) Hx) Ek' -Dk /injcp -/injcp.
    By Apply: gcol_cface.
  Rewrite: -(fconnect_invariant (Hk'F e0) Hu) Ek'X /e0 -addcA addcc addc0.
  By Apply: esym; Apply: gcol_cface.
Case De0: e0 Dk' => [] Dk'; [ Idtac
| By Constructor 1; Apply/Et1; Exists k0
| By Constructor 2; Apply/Et2; Exists k0
| By Constructor 3; Apply/Et3; Exists k0].
Case/andP: (gcol_adj 2!(Adds CpU ?) Hk0c (adj_ecpU 2!g2)); Case/idP.
By Rewrite: /comp /injcp -/injcp in Dk; Rewrite: Dk eq_addc0 -/ic2 addcC -/e0 De0.
Qed.

Lemma cpcolor1K_correct : (f : colseq -> ctree)
  ((k' : (cpmap (Adds CpK cp2)) -> color)
     (coloring k') -> (cp_extcol cp1 f k')) ->
  (cp_extcol (Adds CpK cp1) (cpcolor1 CpK f) k).
Proof.
Rewrite: /cpmap -/cpmap -/g2.
Pose k' := [u]if pick x in [x](cface u (icpK g2 x)) then (k x) else Color0.
Step Hk'F: (invariant face k') =1 (ecpK g2).
  Move=> u; Apply/eqP; Congr [w](if w is (Some x) then (k x) else ?).
  By Apply: eq_pick => [v]; Rewrite: -cface1.
Step Ek': (x : g2) (k' (icpK g2 x)) = (k x).
  Move=> x; Rewrite: /k' -(eq_pick 2!(cface x)).
    Case: (pickP (cface x)) {}Hk => [y Hxy | Hx] [_ HkF].
      Exact (esym (fconnect_invariant HkF Hxy)).
    By Case/idP: (Hx x); Apply connect0.
  By Move=> y; Rewrite: cface_icpK.
Pose ic2 := (injcp cp1 2!(Adds CpK cp2)).
Case He12: (e1 =d e2).
  Split; Rewrite: /cpcolor1 -/g2 -/et Det /et' /= He12 //; Right.
  Move=> [k0 [[Hk0E Hk0F] _] Dk].
  Rewrite: /e1 /e2 addcC [c](inj_eqd (!inj_addc c)) in He12.
  Step HaX: (adj (ic2 (icpK g2 (node g2))) (ic2 (icpK g2 (face (edge g2))))).
    Apply: sub_adj_injcp; Rewrite: (adj_icpK g2); Apply/or3P; Constructor 3.
    By Rewrite: fconnect1 connect0.
  Case/adjP: HaX => [u HXu HuX]; Case/idP: (Hk0E u).
  Rewrite: /comp /injcp -/injcp -/g2 -/ic2 in Dk.
  Rewrite: /invariant -(fconnect_invariant Hk0F HXu).
  By Rewrite: (fconnect_invariant Hk0F HuX) !Dk eqd_sym.
Step Hk': (coloring k').
  Rewrite: /e1 /e2 addcC [c](inj_eqd (!inj_addc c)) in He12.
  Split; RightDone; Move=> u; Rewrite: /invariant.
  Case: (fband_icpK u) (fband_icpK (edge u)) => [x Hx] [y Hy].
  Rewrite: (fconnect_invariant Hk'F Hx) (fconnect_invariant Hk'F Hy) !Ek'.
  Step Hxy: (adj (icpK g2 x) (icpK g2 y)).
    By Apply/adjP; Exists u; LeftBy Rewrite Sface.
  Case: {}Hk {u Hx Hy} => [HkE HkF]; Rewrite: (eqcP (HkF (edge g2))) in He12.
  Rewrite: adj_icpK in Hxy; Case/or3P: Hxy.
      Move/adjP=> [z Hxz Hzy]; Rewrite: (fconnect_invariant HkF Hxz).
      Rewrite: -(fconnect_invariant HkF Hzy); Apply: HkE.
    Move/andP=> [Hx Hy]; Rewrite: -(fconnect_invariant HkF Hx).
    By Rewrite: -(fconnect_invariant HkF Hy).
  Move/andP=> [Hy Hx]; Rewrite: -(fconnect_invariant HkF Hx).
  By Rewrite: -(fconnect_invariant HkF Hy) eqd_sym.
Move=> f Hf; Case: {Hf}(Hf ? Hk'); Rewrite: /cpmap -/cpmap -/g2.
Step []: (Adds (addc e1 e2) et'') = (trace (maps k' (cpring (ecpK g2)))).
  Rewrite: cpring_ecpK !maps_adds -maps_comp (eq_maps 3!(comp k' ?) Ek').
  Rewrite: (fconnect_invariant Hk'F (cface_node_ecpK g2)) Ek'.
  Move: (esym Det); Rewrite: /et drop_behead (head_proper_cpring Hg2p).
  Rewrite: maps_adds -!urtrace_trace /urtrace !rot1_adds !last_add_last /=.
  By Rewrite: headI /= /et'; Injection=> [] De2; Rewrite: /e1 De2 -addcA addc_inv.
Move=> Ht Et; Split; Rewrite: /cpcolor1 -/g2 -/et Det /et' He12 //.
Apply: (iffP Et) {Ht Et}; Move=> [k0 Hk0 Dk]; Exists k0; Auto.
  By Rewrite: /comp in Dk; Move=> x; Rewrite: /comp /injcp -/injcp Dk Ek'.
Move=> u; Rewrite: /comp -/ic2; Rewrite: /comp /injcp -/injcp -/ic2 -/g2 in Dk.
Case: (fband_icpK u) => [x Hu]; Rewrite: (fconnect_invariant Hk'F Hu).
By Case: Hk0 => [Hk0 _]; Rewrite: (gcol_cface 2!(Adds CpK ?) Hk0 Hu) Dk.
Qed.

Lemma cpcolor1A_correct : (f : colseq -> ctree)
  ((k' : (cpmap (Adds CpA cp2)) -> color)
     (coloring k') -> (cp_extcol cp1 f k')) ->
  (cp_extcol (Adds CpA cp1) (cpcolor1 CpA f) k).
Proof.
Rewrite: /cpmap -/cpmap -/g2; Case He1: (negb e1 =d e2).
  Split; Rewrite: /cpcolor1 -/g2 -/et Det /et' (negbE He1) //.
  Right; Move=> [k0 [[_ Hk0F] _] Dk]; Rewrite: /comp /= in Dk; Case/eqP: He1.
  Rewrite: /e1 addcC; Congr addc; Rewrite: -!Dk; Apply: (fconnect_invariant Hk0F).
  Apply: (!sub_cface_injcp cp1); Rewrite: (cface_icpA g2); Apply/orP; Right.
  By Rewrite: /= !connect0 !orbT.
Pose k' := (k :: (ecpA g2) -> color); Move/idP: He1 => He1.
Move/eqP: {}He1; Rewrite: /e1 addcC; Move/inj_addc=> DkXn.
Step Hk'F: (invariant face k') =1 (ecpA g2).
  Move=> x; Apply/eqP; Move: (fconnect1 face x); Rewrite: cface_icpA /k'.
  Case: {}Hk => [_ HkF]; Case/orP=> [Hx | Hx].
    By Apply: esym; Apply: (fconnect_invariant HkF).
  Step EkX: (y : g2) (set2 x (face x) y) -> (k y) = (k (node g2)).
    Move=> y; Rewrite: -mem_seq2; Move=> Hy.
    Move: (allP Hx ? Hy); Rewrite: /fband; Case/hasP=> [z Hz Hyz].
    Rewrite: (fconnect_invariant HkF Hyz); Repeat Case/setU1P: Hz => [[] | Hz] //.
  By Rewrite: (EkX ? (set21 ? ?)) (EkX ? (set22 ? ?)).
Step Hk': (coloring k').
  Split; Auto; Rewrite: /invariant /k' /= /ecpA_edge; Move: {}Hk => [HkE HkF] x.
  Case Hg2: (cface (edge g2) (node g2)); RightBy Apply: HkE.
  Case: (x =P g2) => [Dx | _] /=.
    Rewrite: -[y](eqcP (HkF y)) Enode -{x}Enode [y](eqcP (HkF y)) eqd_sym Dx.
    Apply: HkE.
  Case: (x =P (node (node g2))) => [Dx | _]; RightBy Apply: HkE.
  Rewrite:  -{(node g2)}Enode -Dx -cface1r in Hg2.
  By Rewrite: (fconnect_invariant HkF Hg2); Apply: HkE.
Move=> f Hf; Case: {Hf}(Hf ? Hk'); Rewrite: /cpmap -/cpmap -/g2.
Step []: (if et'' is Seq0 then et else et'')
            = (trace (maps k' (cpring (ecpA g2)))).
  Rewrite: /k' cpring_ecpA; Case Hg2l: (long_cpring g2).
    Rewrite: -urtrace_trace /et'' (head_long_cpring Hg2l) /= rot1_adds.
    By Rewrite: -DkXn /urtrace last_add_last -maps_add_last headI.
  By Rewrite: -/et /et'' drop_oversize // leqNgt -size_long_cpring Hg2l.
By Move=> Ht Et; Split; Rewrite: /cpcolor1 -/g2 -/et Det /et' -/et' -Det He1.
Qed.

Lemma cpcolor1R_correct : (n : nat; f : colseq -> ctree)
  ((k' : (cpmap (Adds (CpR n) cp2)) -> color)
     (coloring k') -> (cp_extcol cp1 f k')) ->
  (cp_extcol (Adds (CpR n) cp1) (cpcolor1 (CpR n) f) k).
Proof.
Move=> n f Hf; Case: {Hf}(Hf k Hk); Rewrite: /cpmap -/cpmap -/g2 cpring_ecpR.
By Rewrite: maps_rot trace_rot; Split.
Qed.

Lemma cpcolor1R'_correct : (f : colseq -> ctree)
  ((k' : (cpmap (Adds CpR' cp2)) -> color)
     (coloring k') -> (cp_extcol cp1 f k')) ->
  (cp_extcol (Adds CpR' cp1) (cpcolor1 CpR' f) k).
Proof.
Move=> f Hf; Case: {Hf}(Hf k Hk); Rewrite: /cpmap -/cpmap -/g2 /ecpR' cpring_ecpR.
Rewrite: -subn1 -size_cpring -/(rotr (1) (cpring g2)) maps_rotr.
Rewrite: -[lc](rotr_rot (1) (trace lc)) -trace_rot rot_rotr.
By Split; Rewrite: /cpcolor1 size_trace size_maps leqNgt -size_proper_cpring Hg2p.
Qed.

End Cpcol1Inv.

Definition cpexpand1 [s : cpstep] : cprog :=
  Cases s of
    CpY => (Cprog -1 K 1 U)
  | CpH => (Cprog -1 K K 1 U)
  | _ => (seq1 s)
  end.

Fixpoint cpexpand [cp : cprog] : cprog :=
  if cp is (Adds s cp') then (cat (cpexpand1 s) (cpexpand cp')) else seq0.

Lemma cpexpand_add_last : (cp : cprog; s : cpstep)
 (cpexpand (add_last cp s)) = (cat (cpexpand cp) (cpexpand (seq1 s))).
Proof. By Elim=> [|s' cp Hrec] s //=; Rewrite: Hrec -catA. Qed.

Lemma cpcolor1_cpexpand_rev : (cp : cprog; f : colseq -> ctree; et : colseq)
  (negb (et Color0)) ->
  (foldr cpcolor1 f (rev cp) et) = (foldr cpcolor1 f (rev (cpexpand cp)) et).
Proof.
Step EctE: (ct : ctree) (if ct is Ctree_empty then Ctree_empty else ct) = ct.
  By Case.
Elim/last_ind=> [|cp s Hrec] // f et Het.
Rewrite: cpexpand_add_last -cats1 !rev_cat !foldr_cat; Case Ds: s => [n||||||].
 By Rewrite: /= -Hrec // mem_rot.
 By Rewrite: /= -Hrec // mem_rotr.
 By Case: et Het => [|[|||] et] //= Het; Rewrite: -?Hrec ?ctree_union_Nl ?EctE //;
  Rewrite: !seq1I !cats1 -!add_last_adds !rotr1_add_last //;
  Repeat Rewrite: headI //=; Rewrite: ctree_union_sym.
 Case: et Het => [|e1 [|e2 et]] //=; LeftBy Rewrite: !if_same.
  Rewrite: !seq1I !cats1 -!add_last_adds !rotr1_add_last -!rot1_adds !size_rot /=.
  Case He12: (e1 =d e2).
     Case/eqP: {e2}He12.     
     Case: e1 => //= [] Het; Rewrite: -?Hrec ?ctree_union_Nl ?EctE //.
     By Rewrite: ctree_union_sym.
  By Case: e1 He12 => //; Case: e2 => //= [] _ Het;
    Rewrite: -?Hrec ?ctree_union_Nl ?EctE //.
 By Rewrite: /= -?Hrec.
 Case: et Het => [|e1 [|e2 et]] //=; Case He12: (e1 =d e2) => //.
  Case/norP; Clear; Move/norP=> [_ Het]; Apply Hrec.
  By Rewrite: /= /setU1 -eq_addc0 He12.
 Case: et Het => [|e1 [|e2 et]] //= Het; Rewrite: -?Hrec //.
  By Case: et Het => [|e3 et] //; Case/norP; Clear; Case/norP.
Qed.

Inductive pmap_eqdep [A : Set; g : pointed_map; h : A -> g]
                   : (g' : pointed_map) (A -> g') -> Prop :=
  PmapEqdepRefl : (pmap_eqdep h h).

Lemma pmap_eqdep_sym : (A : Set; g, g' : pointed_map; h : A -> g; h' : A -> g')
  (pmap_eqdep h h') -> (pmap_eqdep h' h).
Proof. By Move=> A g g' h h' []. Qed.

Lemma pmap_eqdep_split : (A : Set; g, g' : pointed_map; h : A -> g; h' : A -> g')
  (pmap_eqdep h 4!(PointedMap g') h') -> (pmap_eqdep h h').
Proof. By Move=> A g [x g']. Qed.

Lemma injcp_adds : (s : cpstep; cp1, cp2 : cprog)
  (pmap_eqdep [x](injcp cp1 2!(Adds s cp2) (injcp (seq1 s) x))
                 (injcp (Adds s cp1) 2!cp2)).              
Proof. Done. Qed.

Lemma injcp_cat : (cp1, cp2, cp3 : cprog)
  (pmap_eqdep [x](injcp cp2 (injcp cp1 x)) (injcp (cat cp1 cp2) 2!cp3)).
Proof.
Move=> cp1 cp2; Elim: cp1 => [|s' cp1 Hrec] cp3; LeftBy Case cp2.
Rewrite: cat_adds; Case (injcp_adds s' (cat cp1 cp2) cp3).
By Case: (Hrec (Adds s' cp3)).
Qed.

Lemma injcp_expand : (cp1, cp2 : cprog)
  (pmap_eqdep (injcp (rev cp1) 2!cp2) (injcp (rev (cpexpand cp1)) 2!cp2)).
Proof.
Move=> cp1 cp2; Elim: cp1 => [|s cp1 Hrec] //=; Rewrite: rev_adds -cats1 rev_cat.
Case: (injcp_cat (rev cp1) (seq1 s) cp2).
Case: (injcp_cat (rev (cpexpand cp1)) (rev (cpexpand1 s)) cp2).
Simpl; Case/pmap_eqdep_sym: Hrec; Move: {cp1}(rev (cpexpand cp1)) => rcp.
Move: {cp2}(cpmap cp2) {rcp}(catrev cp2 rcp) (injcp rcp 2!cp2) => A cp ic.
By Case: s => [n||||||] //; Apply pmap_eqdep_split; 
  Rewrite: /cpexpand1 /seq4 /seq3 /seq2 /seq1 /rev /catrev /injcp -/injcp;
  Rewrite: /cpmap -/cpmap /icpK /icpR' /icpR /ecpK !ecpR1_eq !ecpR'_eq !Eedge.
Qed.

Lemma cpcolor1_correct : (cp1, cp2 : cprog; k : (cpmap cp2) -> color)
  (coloring k) -> (cp_extcol cp1 (foldr cpcolor1 cpbranch cp1) k).
Proof.
Move=> cp1 cp2 k Hk; Rewrite: -(rev_rev cp1); Move/rev: cp1 => cp1.
Pose ecp1 := (rev (cpexpand cp1)).
Step Hecp1: (cp_extcol ecp1 (foldr cpcolor1 cpbranch ecp1) k).
  Rewrite: /ecp1 ~{ecp1 Eecp1}.
  Elim/last_ind: cp1 cp2 k Hk => [|cp1 s Hrec] cp2 k Hk.
    By Apply: cpbranch_correct.
  Rewrite: cpexpand_add_last rev_cat; Case: s => [n||||||] /=.
   Apply: cpcolor1R_correct; Auto.
   Apply: cpcolor1R'_correct; Auto.
   Apply: cpcolor1U_correct; LeftDone.
    Move=> k1 Hk1; Apply: cpcolor1R_correct; Auto.
    Move=> k2 Hk2; Apply: cpcolor1K_correct; Auto.
    Move=> k3 Hk3; Apply: cpcolor1R'_correct; Auto.
   Apply: cpcolor1U_correct; LeftDone.
    Move=> k1 Hk1; Apply: cpcolor1R_correct; Auto.
    Move=> k2 Hk2; Apply: cpcolor1K_correct; Auto.
    Move=> k3 Hk3; Apply: cpcolor1K_correct; Auto.
    Move=> k4 Hk4; Apply: cpcolor1R'_correct; Auto.
   Apply: cpcolor1U_correct; Auto.
   Apply: cpcolor1K_correct; Auto.
   Apply: cpcolor1A_correct; Auto.
Case: Hecp1; Rewrite: ~/ecp1 -cpcolor1_cpexpand_rev ?memc0_trace_cpring //.
Move=> Ht Et; Split.
  By Move: Ht; Rewrite: /cp_ht0 -!size_ring_cpmap; Case: (injcp_expand cp1 cp2).
By Move: Et; Rewrite: /cp_tr0; Case: (injcp_expand cp1 cp2).
Qed.

Lemma cpcolor0_correct : (cp : cprog)
 (cp_extcol cp 2!seq0 [_](cpcolor0 cp) (ccons true)).
Proof.
Move=> cp1; Pose cp2 := (seq0 :: cprog); Pose g2 := (cpmap cp2).
Pose k := ((ccons true) :: g2 -> color); Step Hk: (coloring k) By Split; Case.
Step Ek: (trace (maps k (cpring g2))) = (seq2 Color1 Color1) By Done.
Step Dg2: <hypermap>g2 == (cpmap seq0) By Done.
Move: k Hk Ek Dg2; Rewrite: ~/g2; Elim: cp1 cp2 => [|s cp1 Hrec] *.
  By Case: (cpcolor1_correct seq0 Hk); Rewrite: Ek; Split.
Case: (cpcolor1_correct (Adds s cp1) Hk); Rewrite Ek.
Pose g2 := (cpmap cp2); Step DknX: (k (node g2)) = (addc Color1 (k g2)).
  Move: Ek; Rewrite: trace_cpring_eq // -/g2; Injection=> _ _ [].
  By Rewrite: -addcA addcc addc0.
Step Hg2b: (cface g2 (node g2)) = false.
  By Move: (g2::g2); Rewrite: /g2 Dg2; Case.
Step Hg2b': ((node g2) =d g2) = false.
  By Move: (g2::g2); Rewrite: /g2 Dg2; Case.
Step Hg2: (x : g2) <g2> g2 = x \/ (node g2) = x.
  By Move: (g2::g2); Rewrite: /g2 Dg2; Do 2 Case; Auto.
Case: s => [n||||||]; First [By Split | Do 3 Clear].
    Case: (Hrec (Adds (CpR n) cp2) k Hk) => //; RightBy Split.
    Rewrite: /cpmap -/cpmap cpring_ecpR maps_rot trace_rot Ek.
    By Case: {}n => [|[|[|n']]].
  Simpl; Pose k' := [u]if (cface u (ecpY g2)) then Color2 else
                       if (cface u (icpY g2 g2)) then Color0 else Color3.
  Step [] : (trace (maps k' (cpring (ecpY g2)))) = (seq3 Color1 Color2 Color3).
    By Rewrite: /k'; Move: (g2::g2); Rewrite: /g2 Dg2; Case.
  Step Hk'F: (invariant face k') =1 (ecpY g2).
    By Move=> u; Apply/eqP; Rewrite: /k' -!cface1.
  Step Hk': (coloring k').
    Split; RightDone; Rewrite: /k'; Move: (g2 :: g2); Rewrite: /g2 Dg2.
    By Case=> [|] [||[||[|]]].
  Case: (cpcolor1_correct cp1 2!(Adds CpY cp2) Hk'); Rewrite: /cpmap -/cpmap -/g2.
  Move=> Ht Et; Split; LeftDone; Apply: (iffP Et) {Et Ht}.
    Move=> [k0 Hk0 Dk']; Pose h0 := (locked Eperm231).
    Exists [x](addc (k g2) (h0 (k0 x))); LeftBy Apply: (gcol_perm Hk0).
    Move=> x; Rewrite: /comp in Dk'; Rewrite: /comp /= Dk' addcC.
    Unlock h0; Move: x DknX; Rewrite: /k' -/g2; Move: {}k (g2 :: g2).
    By Rewrite: /g2 Dg2; Move=> k''; Do 2 Case.
  Move=> [k0 Hk0 Dk].
  Pose e0 := (addc (k g2) (k0 (injcp cp1 2!(Adds CpY cp2) (ecpY g2)))).
  Pose h0 := if e0 =d Color2 then Eperm321 else Eperm312.
  Exists [x](addc (h0 (k g2)) (h0 (k0 x))); LeftBy Apply: (gcol_perm Hk0).
  Move=> u; Rewrite: /comp in Dk; Rewrite: /comp /= -permc_addc /k'.
  Rewrite: /comp /injcp -/injcp in Dk.
  Case: (fband_icpY u) Hk0 => [[x Hu] | Hu] [Hk0 _].
    Rewrite: (gcol_cface 2!(Adds CpY ?) Hk0 Hu) ~Dk.
    Rewrite: !~{Hu}(same_cface Hu) cface_icpY Sface cface_ecpY ~/h0 /=.
    Case: (Hg2 x); Case {x}; LeftBy Rewrite: addcc permc0 connect0.
    By Rewrite: DknX (addcC Color1) addc_inv Sface Hg2b; Case e0.
  Rewrite: Sface Hu -(gcol_cface 2!(Adds CpY ?) Hk0 Hu) -/e0 /h0.
  Move: (gcol_adj 2!(Adds CpY ?) Hk0 (adj_ecpY (coloring_proper_cpring g2 Hk))).
  Case/and3P; Rewrite: !Dk -/g2 DknX eq_addc0 (eq_addc0 (k g2)) -addcA -/e0.
  By Case e0.
Pose k' := [e; u]if u =d (ecpU g2) then Color1 else
                 if u =d (icpU g2 g2) then e else Color0.
Step Hk'F : (e : color) (invariant face (k' e)) =1 (ecpU g2).
  Rewrite: /k'; Move: (g2::g2); Rewrite: /g2 Dg2; Do 2 Case; Repeat Case=> //.
Step Hk' : (e : color) (negb e =d Color0) -> (coloring (k' e)).
  Move=> e He; Split; RightDone; Rewrite: /k'; Move: (g2::g2); Rewrite: /g2 Dg2.
  Case: e He => // [] _; Case; Repeat Case=> //.
Step Ek': (e : color)
 (trace (maps (k' e) (cpring (ecpU g2)))) = (seq4 Color1 Color1 e e).
  By Rewrite: /k'; Move: (g2::g2); Rewrite: /g2 Dg2; Do 2 Case.
Case: (cpcolor1_correct cp1 2!(Adds CpU cp2) (Hk' Color2 (erefl ?))).
Case: {Hk'}(cpcolor1_correct cp1 2!(Adds CpU cp2) (Hk' Color1 (erefl ?))).
Rewrite: /cpmap -/cpmap -/g2 /cpcolor0 !~Ek'; Move=> Ht1 Et1 Ht2 Et2.
Split; LeftBy Apply: ctree_union_proper.
Rewrite: ~{Ht1 Ht2}(ctree_mem_union (ttail et0) Ht2 Ht1); Apply: (iffP orP).
  Case.
    Case/Et2=> [k0 Hk0 Dk']; Exists [x](addc (k (node g2)) (Eperm213 (k0 x))).
      By Apply: gcol_perm.
    Rewrite: /comp in Dk'; Move=> x; Rewrite: /comp /injcp -/injcp Dk' /k' /=.
    Rewrite: /eqd /= addcC; Case (Hg2 x); Case {x}; RightBy Rewrite Hg2b'.
    By Rewrite: set11 DknX addc_inv.
  Case/Et1=> [k0 Hk0 Dk']; Exists [x](addc (k (node g2)) (Eperm123 (k0 x))).
    By Apply: gcol_perm.
  Rewrite: /comp in Dk'; Move=> x; Rewrite: /comp /injcp -/injcp Dk' /k' /=.
  Rewrite: /eqd /= addcC; Case (Hg2 x); Case {x}; RightBy Rewrite Hg2b'.
  By Rewrite: set11 DknX addc_inv.
Move=> [k0 Hk0 Dk]; Rewrite: /= /cpmap /injcp -/cpmap -/injcp /comp in k0 Hk0 Dk.
Pose e0 := (addc (k (node g2)) (k0 (injcp cp1 2!(Adds CpU ?) (ecpU g2)))).
Case He00 : (e0 =d Color0).
  Case: Hk0 => [Hk0 _]; Case/andP: (gcol_adj Hk0 (adj_ecpU 2!?)); Case/idP.
  By Rewrite: -/cpmap Dk eq_addc0.
Case He01 : (e0 =d Color1).
  Right; Apply/Et1; Exists [w](addc (k (node g2)) (Eperm123 (k0 w))).
    By Apply: gcol_perm.
  Move=> u; Case: (fband_icpU u) Hk0 => [[x Hu] | Hu] [Hk0 _].
    Rewrite: (fconnect_invariant (Hk'F Color1) Hu) /comp (gcol_cface Hk0 Hu) Dk.
    Rewrite: /k' /eqd /=; Case (Hg2 x); Case {x Hu}; RightBy Rewrite: Hg2b' addcc.
    By Rewrite: set11 DknX -addcA addcc addc0.
  Rewrite: -(fconnect_invariant (Hk'F Color1) Hu) /comp -(gcol_cface Hk0 Hu).
  Rewrite: /k' set11; Exact (eqP He01).
Left; Apply/Et2; Pose h0 := if e0 =d Color2 then Eperm213 else Eperm231.
Exists [w](addc (h0 (k (node g2))) (h0 (k0 w))); LeftBy Apply: gcol_perm.
Move=> u; Rewrite: /comp -permc_addc.
Case: (fband_icpU u) Hk0 => [[x Hu] | Hu] [Hk0 _].
  Rewrite: [c](fconnect_invariant (Hk'F c) Hu) /comp ~{Hu}(gcol_cface Hk0 Hu) Dk.
  Rewrite: /k' /eqd /=; Case (Hg2 x); Case; RightBy Rewrite: Hg2b' addcc permc0.
  By Rewrite: set11 DknX -addcA addcc addc0 /h0; Case e0.
Rewrite: -[c](fconnect_invariant (Hk'F c) Hu) /comp -~{Hu}(gcol_cface Hk0 Hu).
By Rewrite: /k' set11 /h0 -/e0; Case: {}e0 He00 He01.
Qed.

End CprogColoringCorrectness.

Theorem cpcolor_proper : (cp : cprog)
  (ctree_proper (pred (cprsize cp)) (cpcolor cp)).
Proof.
Move=> cp; Rewrite: /cpcolor.
Case Dh: (pred (cprsize cp)) => [|h].
  Case: (cpcolor0_correct (seq1 Color1) (rev cp)) => /= [Ht Et].
  Move: (elimT Et) Ht; Rewrite: /cp_ht0 -/(rev (rev cp)).
  Case: (cpcolor0 (rev cp)) => [t1 t2 t3|lf|] //.
    By Clear; Rewrite: rev_rev Dh.
  Case=> // [k0 [Hk0 _] _] _; Rewrite: rev_rev in k0 Hk0.
  Move: (coloring_proper_cpring (cpmap cp) Hk0).
  By Rewrite: size_proper_cpring size_ring_cpmap ltn_lt0sub subn1 Dh.
Apply ctree_cons_rot_proper.
  Case: (cpcolor0_correct seq0 (rev cp)) => /= [Ht _].
By Rewrite: /cp_ht0 -/(rev (rev cp)) rev_rev Dh in Ht.
Qed.

Theorem ctree_mem_cpcolor : (cp : cprog; et : colseq)
  (reflect (even_trace et) /\ (ring_trace (cpring (cpmap cp)) (Adds (sumt et) et))
    (ctree_mem (cpcolor cp) et)).
Proof.
Move=> cp et0; Rewrite: /cpcolor ctree_mem_cons_rot.
Case: (cpcolor0_correct et0 (rev cp)) => /= [_ H]; Apply: (iffP H) {H}.
  Move=> [k [Hk Ek] _]; Move: k Hk Ek; Rewrite: /cp_tr0 -/(rev (rev cp)) rev_rev.
  Pose g := (cpmap cp); Move=> k Hk; Pose rc := (rot (1) (maps k (cpring g))).
  Move=> Erc; Step [Hrcp Het0p]: (proper_trace (ptrace rc)) /\ (proper_trace et0).
    Move: (memc0_trace_cpring g Hk) (proper_trace_cpring g Hk) Erc.
    Rewrite: -urtrace_trace -/rc; Case: rc => // [y rc].
    Rewrite: /urtrace /ptrace /= /ttail /eptrace; Case/norP; Clear.
    Case: (proper_trace et0); LeftBy Split.
    Move=> Hrc0 Hrcp H; Move: {H}(congr [s](mem s Color0) H).
    By Rewrite: /etail memc0_permt memc0_ttail /= (negbE Hrc0) Hrcp.
  Case: (etail_perm Het0p) (etail_perm Hrcp) => [h1 Eh1] [h2 Eh2].
  Rewrite: /etail /etrace_perm /even_trace ~Erc /eptrace even_etail in Eh1 *.
  Split; Rewrite: // permt_id -~Eh2 in Eh1.
  Pose h1' := (inv_eperm h1); Pose h12 := (comp h1' h2); Exists (comp h12 k).
    By Apply: (coloring_inj 2!h12) Hk => //; Apply: inj_comp; Apply permc_inj.
  Rewrite: (maps_comp h12 k) (maps_comp h1' h2) -/(permt h1') -/(permt h2).
  Rewrite: !trace_permt; Apply: (monic_move (monic_maps (inv_permc h1))).
  Rewrite: /= -sumt_permt -/(permt h1) Eh1 sumt_permt /permt -maps_adds.
  Congr (maps h2); Apply: (monic_inj (rotr_rot (1) 2!?)).
  By Rewrite: -trace_rot -/rc rot1_adds; Case: {}rc Hrcp.
Move=> [Het0e H]; Rewrite: -(rev_rev cp) {1 3 5}/rev in H; Case: H.
Pose g := (cpmap (catrev seq0 (rev cp))); Move=> k Hk Ek.
Def: Hetp := (proper_trace_cpring g Hk).
Pose ic0 := (injcp (rev cp) 2!seq0).
Pose e0 := (addc (k (ic0 true)) (k (ic0 false))).
Step He0: (proper_trace (seq1 e0)).
  Rewrite: /proper_trace /= /e0 -eq_addc0.
  By Case: [H](andP (gcol_adj Hk 5!false 6!(seq1 true) H)); LeftBy Case.
Case: (etail_perm He0) => [h0 Eh0]; Injection: Eh0 => _ Eh0.
Exists [w](addc (addc Color2 (h0 (k (ic0 false)))) (h0 (k w))).
  Apply: gcol_perm; Split; LeftDone.
  Move: Ek Hetp; Rewrite: /cp_tr0 -/g /eptrace -urtrace_trace.
  Case: (rot (1) (maps k (cpring g))) => [|x p] //=.
  Rewrite: /urtrace /=; Injection=> [] _.
  By Rewrite: /etail /etrace_perm Het0e permt_id.
Move=> x; Rewrite: /comp -addcA addcC -permc_addc; Case: x => /=.
  By Rewrite: {1 addc}lock addcC -/e0 -lock Eh0.
By Rewrite: addcc permc0.
Qed.

Unset Implicit Arguments.

    
