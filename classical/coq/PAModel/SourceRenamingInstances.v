From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions
  NumericalContexts NumericalEnvironments NumericalContextRenaming NumericalRenamingMaps
  NumericalRenaming NumericalSubstitutionMaps NumericalSubstitution SubstitutionSource NumericalInstantiation
  RenamingSubstitution SourceBounded SourceQuantifierRules SourceRenamingSquare.
From FOL.Tennenbaum Require Import Peano.
Unset Implicit Arguments.

Theorem source_instantiation_renaming M a t g rb rc rn delta rd re rm ar tr gr k :
  source_bounded M a k -> numerical_instantiation M a t g ->
  renaming_lift M rb rc rn delta rd re rm -> numerical_renaming M a rd re rm delta ar ->
  renaming_lookup M rb rc rn delta t tr -> numerical_renaming M g rb rc rn delta gr ->
  numerical_instantiation M ar tr gr.
Proof.
  intros HA [sb [sc [HHead HSub]]] HL HAR HTR HGR.
  destruct (substitution_singleton_total M tr) as [ub [uc [HU _]]].
  exists ub,uc. split;[exact HU|].
  apply (numerical_source_renaming_square M a k sb sc (succM M (zeroM M)) (zeroM M)
    rd re rm delta rb rc rn delta ub uc (succM M (zeroM M)) (zeroM M)
    g ar gr HA HSub HAR HGR).
  intros i j l m HI HSI HTJ HRI.
  destruct (@Peano.zero_or_succ (carrier M) (raw_interpretation M)
    (fun ax H rho=>axioms M ax rho H) i) as [E|[i' E]];subst i.
  - pose proof (substitution_lookup_functional M sb sc (succM M (zeroM M)) (zeroM M)
      (zeroM M) j t HSI HHead) as E. subst j.
    pose proof (renaming_lookup_functional M rb rc rn delta t m tr HTJ HTR) as E. subst m.
    apply (proj1 (renaming_lift_head M rb rc rn delta rd re rm l HL)) in HRI. now subst l.
  - pose proof (substitution_lookup_functional M sb sc (succM M (zeroM M)) (zeroM M)
      (succM M i') j i' HSI (substitution_singleton_tail M sb sc i')) as E. subst j.
    destruct (renaming_lift_tail_inv M rb rc rn delta rd re rm i' l HL HRI) as [v [HV EL]]. subst l.
    pose proof (renaming_lookup_functional M rb rc rn delta i' m v HTJ HV) as E. subst m.
    apply substitution_singleton_tail.
Qed.

Theorem source_shift_renaming M f g rb rc rn delta rd re rm fr gr k :
  source_bounded M f k -> source_formula_shift M f g ->
  renaming_lift M rb rc rn delta rd re rm ->
  numerical_renaming M f rb rc rn delta fr -> numerical_renaming M g rd re rm delta gr ->
  source_formula_shift M fr gr.
Proof.
  intros HF HS HL HFR HGR.
  apply (proj2 (numerical_renaming_empty_substitution M fr (zeroM M) (zeroM M)
    (succM M (zeroM M)) gr)).
  apply (numerical_source_renaming_square M f k (zeroM M) (zeroM M) (zeroM M)
    (succM M (zeroM M)) rb rc rn delta rd re rm delta
    (zeroM M) (zeroM M) (zeroM M) (succM M (zeroM M)) g fr gr HF).
  - exact (proj1 (numerical_renaming_empty_substitution M f (zeroM M) (zeroM M)
      (succM M (zeroM M)) g) HS).
  - exact HFR.
  - exact HGR.
  - intros i j l m HI HSI HTJ HRI.
    assert (EJ:j=succM M i).
    { apply (proj1 (context_shift_lookup M i j)).
      apply (proj2 (renaming_substitution_lookup M (zeroM M) (zeroM M) (zeroM M)
        (succM M (zeroM M)) i j)). now rewrite Arithmetic.add_zero. }
    subst j.
    pose proof (proj2 (renaming_lift_tail M rb rc rn delta rd re rm i l HL) HRI) as HRI'.
    pose proof (renaming_lookup_functional M rd re rm delta (succM M i) m (succM M l) HTJ HRI') as E. subst m.
    pose proof (proj2 (context_shift_lookup M l (succM M l)) eq_refl) as HS'.
    apply (proj1 (renaming_substitution_lookup M (zeroM M) (zeroM M) (zeroM M)
      (succM M (zeroM M)) l (succM M l))) in HS'. now rewrite Arithmetic.add_zero in HS'.
Qed.

Theorem source_context_shift_renaming M b c n bs cs rb rc rn delta ub uc us vs rd re rm k :
  context_bounded M b c n k -> context_shift M b c n bs cs ->
  context_renaming M b c n rb rc rn delta ub uc -> context_shift M ub uc n us vs ->
  renaming_lift M rb rc rn delta rd re rm ->
  context_renaming M bs cs n rd re rm delta us vs.
Proof.
  intros HB HS HR HT HL i fs gs HI HFS HGS.
  destruct (beta_total M b c i) as [f HF].
  destruct (beta_total M ub uc i) as [fr HFR].
  pose proof (HS i f fs HI HF HFS) as HShiftF.
  pose proof (HR i f fr HI HF HFR) as HRenameF.
  pose proof (HT i fr gs HI HFR HGS) as HShiftFR.
  destruct (numerical_renaming_total M fs rd re rm delta) as [gr HGR].
  assert (HShiftGR:source_formula_shift M fr gr).
  { apply (source_shift_renaming M f fs rb rc rn delta rd re rm fr gr k);try assumption.
    apply HB. exists i. auto. }
  pose proof (numerical_renaming_functional M fr (zeroM M) (zeroM M) (zeroM M)
    (succM M (zeroM M)) gs gr HShiftFR HShiftGR) as E. now subst gr.
Qed.

Print Assumptions source_instantiation_renaming.
Print Assumptions source_shift_renaming.
Print Assumptions source_context_shift_renaming.
