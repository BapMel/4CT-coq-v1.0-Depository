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
Require birkhoff.
Require quiztree.
Require part.
Require redpart.
Require discharge.
Require znat.
Require hubcap.
Require cfreducible.
Require configurations.
Require present.
Require cfmap.

Set Implicit Arguments.

Syntax constr level 10 :
  pp_seq_zpos [(Adds (Zpos $n) $s)] ->
  ["Zseq" [<hov 1> (PPSEQPP SPC znat <<(Adds (Zpos $n) $s)>>)]]
| pp_seq_zneg [(Adds (Zneg $n) $s)] ->
  ["Zseq" [<hov 1> (PPSEQPP SPC znat <<(Adds (Zneg $n) $s)>>)]].

Section DebugHub.

Variables nhub : nat; rrf : (drule_fork nhub); rp : part -> bool.

Fixpoint frcr [p : part; i, n : nat] : (seq znatData) := 
  if n is (S n') then
    let (n1, r1) = (sort_drules (rot_part i p) (target_drules rrf)) in
    let (n2, r2) = (sort_drules (rot_part i p) (source_drules rrf)) in
    (Adds (subnz (S n1) n2) (frcr p (S i) n'))
  else seq0.

Definition frc [p : part] : (seq znatData) :=
  (frcr (rot_part (minus nhub (2)) p) (0) nhub).

Inductive sdr_res : Set := Sdres : drules -> nat -> drules -> sdr_res.

Fixpoint sdrr [p : part; n : nat; rs, rf, r : drules] : sdr_res :=
  if r is (Adds p' r') then
    Cases (cmp_part p p') of
      Psubset => (sdrr p (S n) rs (Adds p' rf) r')
    | Pstraddle => (sdrr p n (Adds p' rs) rf r')
    | Pdisjoint => (sdrr p n rs rf r')
    end
  else (Sdres rf n rs).

Definition sdr [p : part; rf, r : drules] : sdr_res :=
  (sdrr p (0) seq0 rf r).

Inductive sckb1_res : Set :=
  Sckb1Ok : sckb1_res
| Sckb1Nok : part -> (d1, d2 : drules) sckb1_res.

Fixpoint sckb1r
     [p : part; r, rr, ru, rf, rfr : drules; n, m : nat] : sckb1_res :=
  if m is (S m') then
    if r is (Adds p1 r') then
      if (ltn (size r') n) then Sckb1Ok else
      let p' = (meet_part p p1) in
      Cases if (check_unfit p' ru) then Sckb1Ok else
            let (rf', dn, r'') = (sdr p' (Adds p1 rf) r') in
            let (rfr', dnr, rr') = (sdr p' rfr rr) in
            if (minus (plus dnr n) dn) is (S n') then
              (sckb1r p' r'' rr' ru rf' rfr' n' m')
            else if (rp p') then Sckb1Ok else (Sckb1Nok p' rf' rfr') of
        Sckb1Ok => (sckb1r p r' rr (Adds p1 ru) rf rfr n m')
      | nok => nok
      end
    else Sckb1Ok
  else (Sckb1Nok p rf rfr).

Definition sckb1 [p0 : part; i : nat; b0 : znat] : sckb1_res :=
  let p = (rot_part (minus nhub (3)) (rot_part i p0)) in
  let b = (oppz b0) in
  let (hr, co_hr, _) = rrf in
  let (rf, dn, r) = (sdr p seq0 co_hr) in
  let (rfr, dnr, rr) = (sdr p seq0 hr) in
  if (subz (subnz (S dnr) dn) b) is (Zpos n) then
    (sckb1r p r rr seq0 rf rfr n (plus (size r) (10)))
  else (Sckb1Nok p rf rfr).

Inductive sckb2_res : Set :=
  Sckb2Ok : sckb2_res
| Sckb2Nok : part -> part -> (d1, d2, d3, d4 : drules) sckb2_res.

Fixpoint sckb2r
  [p1, p2 : part; r1, rr1, ru1, r2, rr2, ru2 : drules;
   rf1, rfr1, rf2, rfr2 : drules; i, n, m : nat] : sckb2_res :=
  if m is (S m') then
    if r1 is (Adds q r1') then
      if (ltn (plus (size r1') (size r2)) n) then Sckb2Ok else
      let p1' = (meet_part p1 q) in let p2' = (rot_part i p1') in
      Cases
        if (orb (check_unfit p1' ru1) (check_unfit p2' ru2)) then Sckb2Ok else
        let (rf1', dn1, r1'') = (sdr p1' (Adds q rf1) r1') in
        let (rfr1', dnr1, rr1') = (sdr p1' rfr1 rr1) in
        let (rf2', dn2, r2') = (sdr p2' rf2 r2) in
        let (rfr2', dnr2, rr2') = (sdr p2' rfr2 rr2) in
        if (minus (plus dnr1 (plus dnr2 n)) (plus dn1 dn2)) is (S n') then
          (sckb2r p1' p2' r1'' rr1' ru1 r2' rr2' ru2
                  rf1' rfr1' rf2' rfr2' i n' m')
        else if (rp p1') then Sckb2Ok else
           (Sckb2Nok p1' p2' rf1' rf2' rfr1' rfr2')
      of
        Sckb2Ok => (sckb2r p1 p2 r1' rr1 (Adds q ru1) r2 rr2 ru2
                           rf1 rfr1 rf2 rfr2 i n m')
      | nok => nok
      end
    else if r2 is Seq0 then Sckb2Ok else
    (sckb2r p2 p1 r2 rr2 ru2 r1 rr1 ru1
            rf2 rfr2 rf1 rfr1 (minus nhub i) n m')
  else (Sckb2Nok p1 p2 rf1 rf2 rfr1 rfr2).

Definition sckb2 [p0 : part; i, j : nat; b0 : znat] : sckb2_res :=
  let b = (oppz b0) in
  let p1 = (rot_part (minus nhub (3)) (rot_part i p0)) in
  let k = (minus if (leq i j) then j else (plus j nhub) i) in
  let p2 = (rot_part k p1) in
  let (hr, co_hr, _) = rrf in
  let (rf1, dn1, r1) = (sdr p1 seq0 co_hr) in
  let (rfr1, dnr1, rr1) = (sdr p1 seq0 hr) in
  let (rf2, dn2, r2) = (sdr p2 seq0 co_hr) in
  let (rfr2, dnr2, rr2) = (sdr p2 seq0 hr) in
  if (subz (subnz (S (addn dnr1 dnr2)) (addn dn1 dn2)) b) is (Zpos n) then
    let m = (plus (size r1) (S (S (S (size r2))))) in
    (sckb2r p1 p2 r1 rr1 seq0 r2 rr2 seq0
            rf1 rfr1 rf2 rfr2 k n m)
  else (Sckb2Nok p1 p2 rf1 rf2 rfr1 rfr2).

End DebugHub.

Tactic Definition RC :=
  Match Context With [|- (succeeds_in ?1 ? ?3) ] ->
     Pose pT := (frc (the_drule_fork ?1) ?3); Compute in pT.

Tactic Definition DBR :=
  Try Clear cb1 cb2 r p;
  Match Context With [|- (succeeds_in ?1 ? ?3) ] ->
  Pose p := ?3; Pose rf := (the_drule_fork ?1); Pose pT := (frc rf p);
  Pose rp := (red_part ?1 the_quiz_tree); Compute in pT;
  Pose cb1 := (sckb1 rf rp p); Pose cb2 := (sckb2 rf rp p); Rewrite: /p.

Unset Implicit Arguments.
