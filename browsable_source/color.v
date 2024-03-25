(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require tacticext.
Require boolprop.
Require funs.
Require dataset.
Require natprop.
Require seq.

Set Implicit Arguments.

(* The four colors, with color sum (xor) and comparison.                    *)

Inductive color : Set :=
  Color0 : color
| Color1 : color
| Color2 : color
| Color3 : color.

Grammar constr constr10 : constr :=
  palette ["palette" constr9($c0) constr9($c1) constr9($c2) constr9($c3)] ->
  [[palette_selector]Cases palette_selector of
         Color0 => $c0 | Color1 => $c1 | Color2 => $c2 | Color3 => $c3
       end].

Syntax constr level 9 :
  pp_Top_palette
  [<<(LAMBDALIST (MUTIND Top.color 0)
       [palette_selector](CASES $_ (TOMATCH palette_selector)
       (EQN $c0 $_) (EQN $c1 $_) (EQN $c2 $_) (EQN $c3 $_)))>>] ->
  [[<hv 0> "palette" [1 2] $c0:E [1 2] $c1:E [1 2] $c2:E [1 2] $c3:E]]
| pp_color_palette
  [<<(LAMBDALIST (MUTIND color.color 0)
       [palette_selector](CASES $_ (TOMATCH palette_selector)
       (EQN $c0 $_) (EQN $c1 $_) (EQN $c2 $_) (EQN $c3 $_)))>>] ->
  [[<hv 0> "palette" [1 2] $c0:E [1 2] $c1:E [1 2] $c2:E [1 2] $c3:E]].

(* Color comparison and sum; sum is used to compute traces, so it is taken *)
(* as primitive.                                                           *)

Definition addc : color -> color -> color :=
  (palette
     [c]c
     (palette Color1 Color0 Color3 Color2)
     (palette Color2 Color3 Color0 Color1)
     (palette Color3 Color2 Color1 Color0)).

Definition eqc [c, c' : color] : bool :=
   if (addc c c') is Color0 then true else false.

(* Properties of equality, and canonical dataSet.                       *)

Lemma eqcPx : (reflect_eq eqc).
Proof. By Do 2 Case; Constructor. Qed.

Canonical Structure colorData := (DataSet eqcPx).

Syntactic Definition eqcP := eqcPx | 2.

Lemma eqcE : eqc = (!eqd?).
Proof. Done. Qed.

(* Algebraic properties of addc *)

Lemma addcA : (c, c', c'' : color)
   (addc c (addc c' c'')) = (addc (addc c c') c'').
Proof. By Do 3 Case. Qed.

Lemma addcC : (c, c' : color) (addc c c') = (addc c' c).
Proof. By Do 2 Case. Qed.

Lemma add0c : (c : color) (addc Color0 c) = c.
Proof. By Case. Qed.

Lemma addc0 : (c : color) (addc c Color0) = c.
Proof. By Case. Qed.
 
Lemma addcc : (c : color) (addc c c) = Color0.
Proof. By Case. Qed.

Lemma addc_inv : (c, c' : color) (addc c (addc c c')) = c'.
Proof. By Do 2 Case. Qed.

Lemma inj_addc : (c : color) (injective (addc c)).
Proof. Exact [c](monic_inj (addc_inv c)). Qed.

Lemma iso_addc : (c : color) (iso (addc c)).
Proof. Move=> c; Exists (addc c); Exact (addc_inv c). Qed.

Lemma eq_addc0 : (c, c' : color) (c =d c') = ((addc c c') =d Color0).
Proof. By Do 2 Case. Qed.

(* Colors as bit vectors *)

Definition cbit0 : color -> bool := (palette false true false true).

Definition cbit1 : color -> bool := (palette false false true true).

Definition ccons [b1, b0 : bool] : color :=
  Cases b1 b0 of
    false false => Color0
  | false true  => Color1
  | true  false => Color2
  | true  true  => Color3
  end.

(* Bit properties. *)

Lemma ccons_cbits : (c : color) (ccons (cbit1 c) (cbit0 c)) = c.
Proof. By Case. Qed.

Lemma cbit1_ccons : (b1, b0 : bool) (cbit1 (ccons b1 b0)) = b1.
Proof. By Do 2 Case. Qed.

Lemma cbit0_ccons : (b1, b0 : bool) (cbit0 (ccons b1 b0)) = b0.
Proof. By Do 2 Case. Qed.

Lemma cbit1_addc : (c, c' : color)
  (cbit1 (addc c c')) = (addb (cbit1 c) (cbit1 c')).
Proof. By Do 2 Case. Qed.

Lemma cbit0_addc : (c, c' : color)
  (cbit0 (addc c c')) = (addb (cbit0 c) (cbit0 c')).
Proof. By Do 2 Case. Qed.

(* The six "edge" permutations that leave Color0 unchanged. *)

Inductive edge_perm : Set :=
  Eperm123 : edge_perm
| Eperm132 : edge_perm
| Eperm213 : edge_perm
| Eperm231 : edge_perm
| Eperm312 : edge_perm
| Eperm321 : edge_perm.

Definition permc [g : edge_perm] : color -> color :=
  Cases g of
    Eperm123 => [c]c
  | Eperm132 => (palette Color0 Color1 Color3 Color2)
  | Eperm213 => (palette Color0 Color2 Color1 Color3)
  | Eperm231 => (palette Color0 Color2 Color3 Color1)
  | Eperm312 => (palette Color0 Color3 Color1 Color2)
  | Eperm321 => (palette Color0 Color3 Color2 Color1)
  end.

Coercion permc : edge_perm >-> FUNCLASS.

Definition inv_eperm [g : edge_perm] : edge_perm :=
  Cases g of Eperm312 => Eperm231 | Eperm231 => Eperm312 | _ => g end.

Lemma inv_eperm_I : (g : edge_perm) (inv_eperm (inv_eperm g)) = g.
Proof. By Case. Qed.

Lemma inv_permc : (g : edge_perm) (monic g (inv_eperm g)).
Proof. By Do 2 Case. Qed.

Lemma permc_inv : (g : edge_perm) (monic (inv_eperm g) g).
Proof. By Do 2 Case. Qed.

Lemma permc_inj : (g : edge_perm) (injective g).
Proof. Exact [g](monic_inj (inv_permc g)). Qed.

Lemma iso_permc : (g : edge_perm) (iso g).
Proof.
Move=> g; Exists (permc (inv_eperm g)); [Apply inv_permc | Apply permc_inv].
Qed.

Lemma permc_addc : (g : edge_perm; c, c' : color)
  (g (addc c c')) = (addc (g c) (g c')).
Proof. By Do 3 Case. Qed.

Lemma permc0 : (g : edge_perm) (g Color0) = Color0.
Proof. By Case. Qed.

Lemma color_iso_permc : (f : color -> color; Hf : (iso f))
  (f Color0) = Color0 -> (EX g | (c : color) (f c) = (permc g c)).
Proof.
Move=> f Hf Ef0; Def: Hf0 := (iso_eqd Hf Color0); Rewrite Ef0 in Hf0.
Case Ef1: (f Color1) (iso_eqd Hf Color1) (Hf0 Color1); Move=> Hf1 // _;
Case Ef2: (f Color2) {Hf}(iso_eqd Hf Color2) (Hf0 Color2) (Hf1 Color2);
  Move=> Hf2 // _ _;
[ Exists Eperm123 | Exists Eperm132 | Exists Eperm213 | Exists Eperm231
| Exists Eperm312 | Exists Eperm321]; Case {Ef0 Ef1 Ef2} => //;
By Case: {f Hf0 Hf1 Hf2}(f Color3) (Hf0 Color3) (Hf1 Color3) (Hf2 Color3).
Qed.

Lemma other_colors : (c : color) (negb c =d Color0) ->
  (set4 Color0 c (Eperm312 c) (Eperm231 c)) =1 colorData.
Proof. By Case=> //; Clear; Case. Qed.

(* Basic operations on edge traces = pairwise sums of the list of colors on  *)
(* a configuration perimeter. Many of these operations use permutations of   *)
(* the non-zero colors, so we introduce an explicit enumeration of these six *)
(* permutations. A ``proper'' trace, one that begins with a non-zero color,  *)
(* has a ``normal'' tail, obtained by applying the rotation that sends the   *)
(* first color to Color1 to the rest of the trace. A trace is even if Color3 *)
(* does not occur before Color2 in its tail. To cut our work in half, we     *)
(* only consider even traces in our algorithm, as the match relation is      *)
(* invariant under swapping Color2 and Color3. The coloring function outputs *)
(* directly the even trace tail of colorings, so we prove here that this is  *)
(* invariant under permutations of the coloring.                             *)
(*   Allowing Color0 in traces allows us to carry fewer side conditions in   *)
(* our lemmas, and gives us a convenient ``bad'' value as well.              *)
(*   Finally, we define a completion operation that adds the last ``cyclic'' *)
(* sum to a a trace, and prove its basic properties. These will be used with *)
(* the ``canonical'' match relation.                                         *)

(* Boolean correctness predicate *)

Definition colseq : Set := (seq colorData).

Definition head_color : colseq -> color := (head Color0).
 
Definition proper_trace [et : colseq] : bool :=
  (negb (head_color et) =d Color0).

(* Conversion from color lists to traces is done in two steps: compute the   *)
(* pairwise sum to get a partial (linear) trace, then append the last color  *)
(* which can be computed as the sum of the partial trace, to get a full      *)
(* (cyclic) trace. The trace computation inverse just computes partial sums. *)

Definition ptrace [lc : colseq] : colseq :=
  if lc is (Adds c lc') then (pairmap addc c lc') else seq0.

Definition permt [g : edge_perm] : colseq -> colseq := (maps g).

Definition sumt : colseq -> color := (foldr addc Color0).

Definition ctrace [et : colseq] : colseq := (add_last et (sumt et)).

Definition trace [lc : colseq] : colseq :=
  if lc is (Adds _ _ ) then (ctrace (ptrace lc)) else seq0.

Definition urtrace [lc : colseq] : colseq := (pairmap addc (last Color0 lc) lc).

Definition untrace [c0 : color; et : colseq] : colseq :=
  (scanl addc c0 (belast Color0 et)).

(* Trace normalization. *)

Definition edge_rot : color -> edge_perm :=
  (palette Eperm123 Eperm123 Eperm312 Eperm231).

Definition ttail [et : colseq] : colseq :=
  if (proper_trace et) then
    if et is (Adds c et') then (permt (edge_rot c) et') else seq0
  else (seq1 Color0).

Definition even_tail : colseq -> bool :=
  (foldr [c;b]((palette b b true false) c) true).

Definition even_trace [et : colseq] : bool :=
  (even_tail (ttail et)).

Definition etrace_perm [et : colseq] : edge_perm :=
  if (even_trace et) then Eperm123 else Eperm132.

Definition etrace [et : colseq] : colseq :=
  (permt (etrace_perm et) et).

Definition etail [et : colseq] : colseq :=
  (permt (etrace_perm et) (ttail et)).

Definition eptrace [lc : colseq] : colseq :=
  (etail (ptrace lc)).

(* Counting cbit1, used to validate the initial tree construction.  *)

Definition count_cbit1 : colseq -> nat :=
  (foldr [c](addn (cbit1 c)) (0)).

(* Lemmas for edge permutations : the standard iso lemmas, and commutation *)
(* with addc (proved by brute force).                                      *)

(* Trace permutation. *)

Lemma permt_id : (et : colseq) (permt Eperm123 et) = et.
Proof. Move=> et; Unfold permt; Exact (maps_id ?). Qed.

Lemma etrace_id : (et : colseq) (permt Eperm132 (permt Eperm132 et)) = et.
Proof. Exact (monic_maps (inv_permc Eperm132)). Qed.

Lemma eqc0_permc : (g : edge_perm; c : color)
  ((g c) =d Color0) = (c =d Color0).
Proof. By Move=> g c; Case g; Case c. Qed.

Lemma memc0_permt : (g : edge_perm; et : colseq)
  (permt g et Color0) = (et Color0).
Proof.
By Move=> g et; Elim: et => [|e et Hrec] //=; Rewrite: /setU1 Hrec eqc0_permc.
Qed.

Lemma proper_permt : (g : edge_perm; et : colseq)
 (proper_trace (permt g et)) = (proper_trace et).
Proof. By Case; Case=> //; Case. Qed.

Lemma memc0_ttail : (et : colseq)
  (ttail et Color0) = (orb (negb (proper_trace et)) (et Color0)).
Proof.
Move=> et; Rewrite: /ttail; Case Het: (proper_trace et) => //.
By Case: et Het => //=; Case=> *; Rewrite: /= ?memc0_permt; Auto.
Qed.

(* Even and tail permutations. *)

Lemma even_etail : (et : colseq) (even_tail (etail et)).
Proof.
Move=> et; Rewrite: /etail /etrace_perm.
Case Het: (even_trace et) => /=; LeftBy Rewrite permt_id.
By Move: Het; Rewrite: /even_trace; Elim: (ttail et) => //; Case=> /= *; Auto.
Qed.

Lemma ttail_etrace : (et : colseq) (ttail (etrace et)) = (etail et).
Proof.
Move=> et; Rewrite: /etail /etrace /etrace_perm /ttail.
Case (even_trace et); Rewrite: /= ?permt_id // proper_permt.
Case Het: (proper_trace et) => //=; Case: et Het => //.
By Case=> // *; Rewrite: /ttail /permt /= -2!maps_comp; Apply: eq_maps; Case.
Qed.

Lemma even_etrace : (et : colseq) (even_trace (etrace et)).
Proof. By Move=> et; Rewrite: /even_trace ttail_etrace even_etail. Qed.

Lemma compose_permt : (g, g' : edge_perm; et : colseq)
  (EX h | (permt h et) = (permt g (permt g' et))).
Proof.
Move=> g g' et; Rewrite: /permt; Case (!color_iso_permc (comp g g')).
    Apply iso_comp; Apply iso_permc.
  By Rewrite: /comp !permc0.
Move=> h Eh; Exists h; Rewrite: -maps_comp; Apply: eq_maps; Move; Auto.
Qed.

Lemma etail_perm : (et : colseq; Het : (proper_trace et))
  (EX g | (permt g et) = (Adds Color1 (etail et))).
Proof.
Move=> et; Rewrite: -ttail_etrace /ttail /etrace.
Def: h := (etrace_perm et); Rewrite: -(proper_permt h); Move=> Het; Rewrite Het.
Case Dhet: (permt h et) Het => // [e het'] Het.
Def: [g Eg] := (compose_permt (edge_rot e) h et); Exists g.
By Rewrite: ~Eg ~Dhet; Case: e Het.
Qed.

Lemma etail_permt : (g : edge_perm; et : colseq)
  (etail (permt g et)) = (etail et).
Proof.
Move=> g et; Case Het: (proper_trace et);
  RightBy Rewrite: /etail /ttail proper_permt Het /= 2!permc0.
Case: (etail_perm Het) Het => [h Eh]; Rewrite: -(proper_permt g); Case/etail_perm.
Move=> h'; Case: (compose_permt h' g et) => [g' []] {h'}.
Rewrite: {1 et}(monic_move (monic_maps (inv_permc h)) Eh) -Eh.
Case: (compose_permt g' (inv_eperm h) (permt h et)).
Rewrite: {4}/permt; Move=> g'' [] {g'}; Rewrite: ~{h}Eh /=; Move=> Heq.
Injection: Heq (even_etail et) (even_etail (permt g et)); Case.
Case: g''; Move=> // _; LeftBy Move=> *; Apply: permt_id.
Elim: (etail et) => //; Case=> //= *; Congr Adds; Auto.
Qed.

(* Perimeter-trace equations. *)

Lemma ptrace_addc : (c : color; lc : colseq)
 (ptrace (maps (addc c) lc)) = (ptrace lc).
Proof.
Move=> c [|c' lc]; Rewrite: /ptrace //=.
Elim: lc c' => [|c'' lc Hrec] c' //=.
By Rewrite: (addcC c) -addcA addc_inv Hrec.
Qed.

Lemma ptrace_permt : (g : edge_perm; lc : colseq)
  (ptrace (permt g lc)) = (permt g (ptrace lc)).
Proof.
Move=> g [|c lc];  Rewrite: /ptrace //=.
By Elim: lc c => [|c' lc Hrec] c //=; Rewrite: Hrec permc_addc.
Qed.

Lemma eptrace_iso : (lc : colseq; f : color -> color; Hf : (iso f))
 (eptrace (maps f lc)) = (eptrace lc).
Proof.
Move=> lc f Hf; Rewrite: /eptrace -(ptrace_addc (f Color0)) -maps_comp.
Case (!color_iso_permc (comp (addc (f Color0)) f)).
    Apply iso_comp; Trivial; Apply iso_addc.
  Exact (addcc (f Color0)).
Move=> g Eg; Rewrite: (eq_maps Eg) -/(permt g) ptrace_permt; Apply etail_permt.
Qed.

(* Properties of the trace completion. *)

Lemma sumt_ctrace : (et : colseq) (sumt (ctrace et)) = Color0.
Proof.
Move=> et; Rewrite: /ctrace -(add0c (sumt et)).
Elim: et {}Color0 => [|e et Hrec] c; LeftBy Rewrite: /= 2!addc0.
Rewrite: add_last_adds /= addcA (addcC c e) Hrec; Apply addc_inv.
Qed.

Lemma memc0_ctrace : (et : colseq)
  (ctrace et Color0) = (orb (sumt et) =d Color0 (et Color0)).
Proof. By Move=> et; Rewrite: /ctrace -cats1 mem_cat /setU mem_seq1 orbC. Qed.

Lemma proper_ctrace : (et : colseq)
  (proper_trace (ctrace et)) = (proper_trace et).
Proof. By Case=> //; Case. Qed.

Lemma sumt_permt : (g : edge_perm; et : colseq)
  (sumt (permt g et)) = (g (sumt et)).
Proof.
Move=> g; Elim=> [|e et Hrec]; LeftBy Exact (esym (permc0 g)).
By Rewrite: /= permc_addc Hrec.
Qed.

Lemma ctrace_permt : (g : edge_perm; et : colseq)
  (ctrace (permt g et)) = (permt g (ctrace et)).
Proof.
Move=> g et; Rewrite: /ctrace sumt_permt /=.
By Elim: et (sumt et) => [|e et Hrec] c; Rewrite: /= ?Hrec.
Qed.

Lemma even_ctrace : (et : colseq)
  (even_trace (ctrace et)) = (even_trace et).
Proof.
Move=> [|e et] //=; Rewrite: /ctrace /even_trace /ttail /proper_trace /=.
Case: (e =d Color0) => //=; Def Dg: g := (edge_rot e).
Step He: (cbit1 (g e)) = false By Rewrite Dg; Case e.
Elim: et e He {Dg} => [|e' et Hrec] e /=; LeftBy Rewrite addc0; Case (g e).
Move=> He; Case Dge': (g e');
  By Rewrite: //= addcA Hrec // permc_addc cbit1_addc He Dge'.
Qed.

Lemma ctrace_inj : (injective ctrace).
Proof.
Move=> et0 et0'; Rewrite: /ctrace.
Elim: {-2}et0 {-2}et0' => [|c et Hrec]; LeftBy Move=> [|c [|c' et']].
Move=> [|c' et'] /=; LeftBy Case et.
By Injection=> Eetr [ ]; Congr Adds; Auto.
Qed.

(* Properties of the full (cyclic) trace. *)

Lemma trace_permt : (ep : edge_perm; lc : colseq)
  (trace (permt ep lc)) = (permt ep (trace lc)).
Proof. By Move=> ep [|c lc] //; Rewrite: /trace -ctrace_permt -ptrace_permt. Qed.

Lemma size_trace : (lc : colseq) (size (trace lc)) = (size lc).
Proof.
By Case=> // *; Rewrite: /trace /ctrace /ptrace /= size_add_last size_pairmap.
Qed.

Lemma trace_untrace : (c0 : color; et : colseq; Het : (sumt et) = Color0)
  (trace (untrace c0 et)) = et.
Proof.
Move=> c0 [|e1 et] // Het; Rewrite: /untrace /= /ptrace /=.
Rewrite: (pairmap_scanl 3!addc addc_inv) /ctrace lastI; Congr add_last.
Rewrite: -{(last e1 et)}add0c -~Het.
By Elim: et e1 => [|e2 et Hrec] e1 /=; Rewrite: -addcA ?Hrec //= addcc. 
Qed.

Lemma sumt_trace : (lc : colseq) (sumt (trace lc)) = Color0.
Proof. By Move=> [|c lc]; Rewrite: /trace ?sumt_ctrace. Qed.

Lemma untrace_trace : (c0 : color; lc : colseq)
  (untrace c0 (trace (Adds c0 lc))) = (Adds c0 lc).
Proof.
Move=> c0 lc; Rewrite: /= /untrace /ctrace belast_add_last /= addc0.
Congr Adds; Apply: (scanl_pairmap addc_inv).
Qed.

Lemma trace_addc : (c : color; lc : colseq)
  (trace (maps (addc c) lc)) = (trace lc).
Proof. Move=> c [|c0 lc] //; Congr ctrace; Exact (ptrace_addc ? (Adds ? ?)). Qed.

Lemma trace_adds : (c : color; lc : colseq)
  (trace (Adds c lc)) = (pairmap addc c (add_last lc c)).
Proof.
Move=> c0 lc; Rewrite: /trace /ptrace /ctrace /= -[et](addc_inv c0 (sumt et)) /=.
Elim: lc {-2 -6} c0 => [|c2 lc Hrec] c1 /=; LeftBy Rewrite: addc0 addcC.
By Congr Adds; Rewrite: -!addcA !addc_inv.
Qed.

Lemma trace_add_last : (c : color; lc : colseq)
  (trace (add_last lc c))
     = (if (trace (Adds c lc)) then lc else [e;et](add_last et e)).
Proof.
Move=> c0 [|c1 lc]; Rewrite: // {trace}lock /= -lock !trace_adds /=.
By Elim: lc {1 3}c1 => [|c3 lc Hrec] c2 /=; Congr Adds.
Qed.

Lemma urtrace_trace : (lc : colseq) (urtrace (rot (1) lc)) = (trace lc).
Proof.
Move=> [|x [|y p]]; Rewrite: // /urtrace /rot /= ?addcc // last_cat /=.
Rewrite: -(cat1s x) cats0 /ctrace -cats1 /= -addcA; Congr Adds.
Elim: p y => [|z p Hrec] y /=; LeftBy Rewrite: addc0 addcC.
By Rewrite: -!addcA addc_inv Hrec.
Qed.

Lemma urtrace_rot : (lc : colseq)
  (urtrace (rot (1) lc)) = (rot (1) (urtrace lc)).
Proof.
Move=> [|x [|y p]] //; Rewrite: /urtrace /rot /= last_cat /=; Congr Adds.
By Rewrite: -!cat1s !cats0; Elim: p y => [|z p Hrec] y //=; Rewrite: Hrec.
Qed.

Lemma trace_rot : (n : nat; rc : colseq) (trace (rot n rc)) = (rot n (trace rc)).
Proof.
Move=> n rc; Elim: n => [|n Hrec]; LeftBy Rewrite: !rot0.
Case: (ltnP n (size rc)) => [Hn | Hn].
  By Rewrite: -add1n !rot_addn ?size_trace // -Hrec -!urtrace_trace -urtrace_rot.
By Rewrite: !rot_oversize ?size_trace // ltnW.
Qed.

Lemma trace_rev : (lc : colseq)
  (trace (rev lc)) = (rot (1) (rev (trace lc))).
Proof.
Move=> [|c0 lc] //; Rewrite: -!urtrace_trace !urtrace_rot; Congr rot.
Elim/last_ind: lc => [|lc c Hrec] //; Move/(!congr ? ? behead ? ?): Hrec.
Case/lastP: lc => [|lc c']; LeftBy Rewrite: /urtrace /= (addcC c).
Rewrite: -!add_last_adds !rev_add_last -2!rot1_adds !urtrace_rot -urtrace_rot.
Repeat Rewrite: /urtrace !rot1_adds /=; Rewrite: !rev_add_last /=; Case.
By Rewrite: rev_adds !last_add_last !(addcC c).
Qed.

Unset Implicit Arguments.

