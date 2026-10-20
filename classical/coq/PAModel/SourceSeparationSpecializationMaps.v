(** SepBody followed by removing its outer set binder is precisely the
    cutoff-one shift of the original matrix. All source codes are internal. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions
  NumericalContexts NumericalContextRenaming NumericalRenamingMaps NumericalRenaming
  NumericalSubstitutionMaps NumericalSubstitution NumericalInstantiation RenamingSubstitution SubstitutionSource
  SourceBounded SourceSubstitutionIdentity SourceShiftSpecialization SourceRenamingSquare
  SourceFiniteCutoffShift SchemaRenamingDescriptors.
From FOL.Tennenbaum Require Import Peano.
Unset Implicit Arguments.

Lemma source_cutoff_one_renaming M phi p1 :source_cutoff_shift M 1 phi p1 ->
  exists rb rc rn,
    renaming_lift M (zeroM M) (zeroM M) (zeroM M) (succM M (zeroM M)) rb rc rn /\
    numerical_renaming M phi rb rc rn (succM M (zeroM M)) p1.
Proof.
  intros (rb&rc&rn&HM&HS).
  destruct HM as (u&v&m&HM&HL). destruct HM as [EU [EV EM]].
  subst u v m.
  assert (HR:renaming_lift M (zeroM M) (zeroM M) (zeroM M) (succM M (zeroM M)) rb rc rn).
  { apply (proj2 (renaming_substitution_lift M (zeroM M) (zeroM M) (zeroM M)
      (succM M (zeroM M)) rb rc rn)). now rewrite Arithmetic.add_zero. }
  exists rb,rc,rn. split;[exact HR|].
  apply (proj2 (numerical_renaming_substitution M phi rb rc rn (succM M (zeroM M)) p1)).
  rewrite (proj1 HL) in HS |- *. change (numerical_substitution M phi rb rc (succM M (zeroM M))
    (succM M (succM M (zeroM M))) p1) in HS.
  now rewrite Arithmetic.add_succ,Arithmetic.add_zero.
Qed.

Theorem source_separation_body_zero_substitution M phi body p1 k ub uc d e j v w l :
  source_bounded M phi k ->schema_renaming M SepBody phi body ->source_cutoff_shift M 1 phi p1 ->
  substitution_lookup M ub uc (succM M (zeroM M)) (zeroM M) (zeroM M) (zeroM M) ->
  substitution_lift M ub uc (succM M (zeroM M)) (zeroM M) d e j ->
  substitution_lift M d e j (succM M (zeroM M)) v w l ->
  numerical_substitution M body v w l (succM M (succM M (zeroM M))) p1.
Proof.
  intros HB HBody HP HU HL1 HL2.
  destruct (source_cutoff_one_renaming M phi p1 HP) as (rb&rc&rn&HRL&HR).
  assert (HI:numerical_substitution M phi (zeroM M) (zeroM M) (zeroM M) (zeroM M) phi).
  { apply (numerical_substitution_identity_on_bound M phi _ _ _ _ k HB).
    intros i _. apply source_empty_substitution_lookup. }
  apply (numerical_source_renaming_square M phi k
    (zeroM M) (zeroM M) (zeroM M) (zeroM M)
    (code_numeral M 0) (code_numeral M 0) (code_numeral M 1) (code_numeral M 2)
    rb rc rn (succM M (zeroM M)) v w l (succM M (succM M (zeroM M)))
    phi body p1 HB HI HBody HR).
  intros i x y z HBound HX HZ HY.
  assert (EX:x=i) by (exact (substitution_lookup_functional M _ _ _ _ i x i HX (source_empty_substitution_lookup M i))).
  subst x.
  change (schema_lookup M SepBody i y) in HY.
  destruct (@Peano.zero_or_succ (carrier M) (raw_interpretation M)
    (fun ax H rho=>axioms M ax rho H) i) as [E|[idx E]];subst i.
  - apply (proj1 (renaming_lift_head M _ _ _ _ rb rc rn z HRL)) in HZ. subst z.
    apply (proj1 (schema_lookup_first M SepBody y)) in HY. change (y=zeroM M) in HY. subst y.
    exact (proj2 (substitution_lift_head M d e j (succM M (zeroM M)) v w l (zeroM M) HL2) eq_refl).
  - apply (schema_lookup_tail M SepBody (succM M idx) y) in HY.
    2:{ intro Hbad. exact (coding_not_lt_zero M idx (proj1 (coding_lt_succ_cancel M idx (zeroM M)) Hbad)). }
    change (y=addM M (succM M idx) (code_numeral M 2)) in HY.
    rewrite Arithmetic.add_succ,(Arithmetic.add_comm M idx (code_numeral M 2)) in HY.
    change (y=succM M (addM M (succM M (succM M (zeroM M))) idx)) in HY.
    rewrite !Arithmetic.add_succ,Arithmetic.add_zero in HY.
    subst y.
    destruct (renaming_lift_tail_inv M _ _ _ _ rb rc rn idx z HRL HZ) as [z' [HZ' EZ]].
    apply context_shift_lookup in HZ'. subst z' z.
    apply (proj2 (substitution_lift_tail M d e j (succM M (zeroM M)) v w l
      (succM M (succM M idx)) (succM M idx) HL2)).
    apply (proj2 (substitution_lift_tail M ub uc (succM M (zeroM M)) (zeroM M) d e j
      (succM M idx) idx HL1)).
    apply substitution_singleton_tail.
Qed.

Lemma source_separation_zero_map_atoms M ub uc d e j v w l :
  substitution_lookup M ub uc (succM M (zeroM M)) (zeroM M) (zeroM M) (zeroM M) ->
  substitution_lift M ub uc (succM M (zeroM M)) (zeroM M) d e j ->
  substitution_lift M d e j (succM M (zeroM M)) v w l ->
  substitution_lookup M v w l (code_numeral M 2) (code_numeral M 0) (code_numeral M 0) /\
  substitution_lookup M v w l (code_numeral M 2) (code_numeral M 1) (code_numeral M 1) /\
  substitution_lookup M v w l (code_numeral M 2) (code_numeral M 2) (code_numeral M 2).
Proof.
  intros HU HL1 HL2. split.
  - exact (proj2 (substitution_lift_head M d e j (succM M (zeroM M)) v w l (zeroM M) HL2) eq_refl).
  - split.
    + apply (proj2 (substitution_lift_tail M d e j (succM M (zeroM M)) v w l (zeroM M) (zeroM M) HL2)).
      exact (proj2 (substitution_lift_head M ub uc (succM M (zeroM M)) (zeroM M) d e j (zeroM M) HL1) eq_refl).
    + apply (proj2 (substitution_lift_tail M d e j (succM M (zeroM M)) v w l
        (succM M (zeroM M)) (succM M (zeroM M)) HL2)).
      apply (proj2 (substitution_lift_tail M ub uc (succM M (zeroM M)) (zeroM M) d e j (zeroM M) (zeroM M) HL1)).
      exact HU.
Qed.

Print Assumptions source_cutoff_one_renaming.
Print Assumptions source_separation_body_zero_substitution.
Print Assumptions source_separation_zero_map_atoms.
