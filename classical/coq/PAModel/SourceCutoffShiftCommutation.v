(** Two actual insertions above the witness variable commute with the
    insertion below the second binder. No internal formula is decoded. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions
  NumericalRenamingMaps NumericalRenaming NumericalSubstitutionMaps NumericalSubstitution
  RenamingSubstitution SourceBounded SourceRenamingSquare SourceFiniteCutoffShift.
From FOL.Tennenbaum Require Import Peano.
Unset Implicit Arguments.

Lemma source_cutoff_shift_map_length M depth b c n :
  source_cutoff_shift_map M depth b c n -> n=code_numeral M depth.
Proof.
  revert b c n. induction depth as [|depth IH];intros b c n HM.
  - exact (proj2 (proj2 HM)).
  - destruct HM as (u&v&m&HM&HL). rewrite (proj1 HL),(IH u v m HM). reflexivity.
Qed.

Lemma source_cutoff_shift_map_tail_lookup M depth b c n i :
  source_cutoff_shift_map M depth b c n ->
  substitution_lookup M b c n (code_numeral M (S depth))
    (source_succ_iter M depth i) (source_succ_iter M (S depth) i).
Proof.
  revert b c n. induction depth as [|depth IH];intros b c n HM.
  - destruct HM as [-> [-> ->]]. apply source_cutoff_shift_base_lookup.
  - destruct HM as (u&v&m&HM&HL). cbn [source_succ_iter].
    apply (proj2 (substitution_lift_tail M u v m (code_numeral M (S depth)) b c n
      (source_succ_iter M depth i) (source_succ_iter M (S depth) i) HL)).
    exact (IH u v m HM).
Qed.

Lemma source_cutoff_shift_map_renaming_lookup M depth b c n i v :
  source_cutoff_shift_map M depth b c n ->
  (renaming_lookup M b c n (code_numeral M 1) i v <->
   substitution_lookup M b c n (code_numeral M (S depth)) i v).
Proof.
  intro HM. rewrite (renaming_substitution_lookup M b c n (code_numeral M 1) i v).
  rewrite (source_cutoff_shift_map_length M depth b c n HM).
  change (substitution_lookup M b c (code_numeral M depth)
    (addM M (code_numeral M depth) (succM M (zeroM M))) i v <->
    substitution_lookup M b c (code_numeral M depth) (succM M (code_numeral M depth)) i v).
  rewrite Arithmetic.add_comm,Arithmetic.add_succ,Arithmetic.add_zero. reflexivity.
Qed.

Lemma source_cutoff_shift_map_renaming M depth f g b c n :
  source_cutoff_shift_map M depth b c n ->
  numerical_substitution M f b c n (code_numeral M (S depth)) g ->
  numerical_renaming M f b c n (code_numeral M 1) g.
Proof.
  intros HM HS. apply (proj2 (numerical_renaming_substitution M f b c n (code_numeral M 1) g)).
  assert (E:addM M n (code_numeral M 1)=code_numeral M (S depth)).
  { rewrite (source_cutoff_shift_map_length M depth b c n HM).
    change (addM M (code_numeral M depth) (succM M (zeroM M))=succM M (code_numeral M depth)).
    now rewrite Arithmetic.add_comm,Arithmetic.add_succ,Arithmetic.add_zero. }
  now rewrite E.
Qed.

Theorem source_cutoff_one_two_commute M phi p1 phi' q k :
  source_bounded M phi k -> source_cutoff_shift M 1 phi p1 ->
  source_cutoff_shift M 1 phi phi' -> source_cutoff_shift M 2 p1 q ->
  source_cutoff_shift M 1 phi' q.
Proof.
  intros HB (sb&sc&sn&HSM&HS) (rb&rc&rn&HRM&HR) (tb&tc&tn&HTM&HT).
  destruct (source_cutoff_shift_map_total M 1) as (ub&uc&un&HUM).
  exists ub,uc,un. split;[exact HUM|].
  apply (numerical_source_renaming_square M phi k sb sc sn (code_numeral M 2)
    rb rc rn (code_numeral M 1) tb tc tn (code_numeral M 1)
    ub uc un (code_numeral M 2) p1 phi' q HB HS
    (source_cutoff_shift_map_renaming M 1 phi phi' rb rc rn HRM HR)
    (source_cutoff_shift_map_renaming M 2 p1 q tb tc tn HTM HT)).
  intros i j l m HI HSI HTJ HRI.
  apply (proj1 (source_cutoff_shift_map_renaming_lookup M 1 rb rc rn i l HRM)) in HRI.
  apply (proj1 (source_cutoff_shift_map_renaming_lookup M 2 tb tc tn j m HTM)) in HTJ.
  destruct (@Peano.zero_or_succ (carrier M) (raw_interpretation M)
    (fun ax H rho=>axioms M ax rho H) i) as [E|[idx E]];subst i.
  - assert (EJ:j=zeroM M).
    { exact (substitution_lookup_functional M sb sc sn (code_numeral M 2) (zeroM M) j (zeroM M)
        HSI (source_cutoff_shift_map_fixed_lookup M 1 sb sc sn HSM 0)). }
    assert (EL:l=zeroM M).
    { exact (substitution_lookup_functional M rb rc rn (code_numeral M 2) (zeroM M) l (zeroM M)
        HRI (source_cutoff_shift_map_fixed_lookup M 1 rb rc rn HRM 0)). }
    subst j l.
    assert (EM:m=zeroM M).
    { exact (substitution_lookup_functional M tb tc tn (code_numeral M 3) (zeroM M) m (zeroM M)
        HTJ (source_cutoff_shift_map_fixed_lookup M 2 tb tc tn HTM 0)). }
    subst m. exact (source_cutoff_shift_map_fixed_lookup M 1 ub uc un HUM 0).
  - assert (EJ:j=succM M (succM M idx)).
    { exact (substitution_lookup_functional M sb sc sn (code_numeral M 2) (succM M idx) j _
        HSI (source_cutoff_shift_map_tail_lookup M 1 sb sc sn idx HSM)). }
    assert (EL:l=succM M (succM M idx)).
    { exact (substitution_lookup_functional M rb rc rn (code_numeral M 2) (succM M idx) l _
        HRI (source_cutoff_shift_map_tail_lookup M 1 rb rc rn idx HRM)). }
    subst j l.
    assert (EM:m=succM M (succM M (succM M idx))).
    { exact (substitution_lookup_functional M tb tc tn (code_numeral M 3) _ m _
        HTJ (source_cutoff_shift_map_tail_lookup M 2 tb tc tn idx HTM)). }
    subst m. exact (source_cutoff_shift_map_tail_lookup M 1 ub uc un (succM M idx) HUM).
Qed.

Print Assumptions source_cutoff_one_two_commute.
