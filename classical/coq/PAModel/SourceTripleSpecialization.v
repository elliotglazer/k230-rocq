(** Three actual AllE rules realize a simultaneous three-name prefix.
    Names are never subjected to accidental later singleton substitution. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions
  SetFormulaCodes SourceBounded NumericalSubstitutionMaps NumericalSubstitution
  NumericalInstantiation SubstitutionSource SourceSubstitutionComposition NumericalEnvironments SchemaConstructorBounds
  SourceRoleReopening SourceDoubleSpecialization SourceSequents NumericalSourceFull
  SourceInstantiationConstructors.
From FOL.Tennenbaum Require Import Peano.
Unset Implicit Arguments.

Definition source_triple_prefix M u d v b c :=
  substitution_lookup M b c (code_numeral M 3) (zeroM M) (zeroM M) u /\
  substitution_lookup M b c (code_numeral M 3) (zeroM M) (code_numeral M 1) d /\
  substitution_lookup M b c (code_numeral M 3) (zeroM M) (code_numeral M 2) v.

Theorem source_triple_prefix_total M u d v :exists b c,source_triple_prefix M u d v b c.
Proof.
  destruct (source_role_reopening_total M v d) as (rb&rc&HD&HV).
  destruct (environment_cons_total M rb rc (code_numeral M 2) u) as (b&c&n&HCons).
  pose proof (proj1 HCons) as EN. subst n.
  assert (HConvert:forall i x,coding_lt M i (code_numeral M 3) ->
    environment_lookup M b c (code_numeral M 3) i x ->
    substitution_lookup M b c (code_numeral M 3) (zeroM M) i x).
  { intros i x HI HE. apply (proj2 (substitution_lookup_inside M b c (code_numeral M 3)
      (zeroM M) i x HI)). exact (proj1 (environment_lookup_inside M b c (code_numeral M 3) i x HI) HE). }
  exists b,c. split.
  - apply HConvert;[schema_small_index|]. exact (proj2 (environment_cons_head M rb rc
      (code_numeral M 2) u b c (code_numeral M 3) u HCons) eq_refl).
  - split.
    + apply HConvert;[schema_small_index|].
      apply (proj2 (environment_cons_tail M rb rc (code_numeral M 2) u b c (code_numeral M 3)
        (zeroM M) d HCons)).
      apply (proj2 (environment_lookup_inside M rb rc (code_numeral M 2) (zeroM M) d
        (coding_zero_lt_succ M (code_numeral M 1)))).
      exact (proj1 (substitution_lookup_inside M rb rc (code_numeral M 2) (zeroM M)
        (zeroM M) d (coding_zero_lt_succ M (code_numeral M 1))) HD).
    + apply HConvert;[schema_small_index|].
      apply (proj2 (environment_cons_tail M rb rc (code_numeral M 2) u b c (code_numeral M 3)
        (code_numeral M 1) v HCons)).
      apply (proj2 (environment_lookup_inside M rb rc (code_numeral M 2) (code_numeral M 1) v
        (coding_lt_succ M (code_numeral M 1)))).
      exact (proj1 (substitution_lookup_inside M rb rc (code_numeral M 2) (zeroM M)
        (code_numeral M 1) v (coding_lt_succ M (code_numeral M 1))) HV).
Qed.

Lemma source_triple_prefix_tail M b c i :
  substitution_lookup M b c (code_numeral M 3) (zeroM M)
    (succM M (succM M (succM M i))) i.
Proof.
  right. split.
  - intro H. exact (coding_not_lt_zero M i
      (proj1 (coding_lt_succ_cancel M i (zeroM M))
      (proj1 (coding_lt_succ_cancel M (succM M i) (code_numeral M 1))
      (proj1 (coding_lt_succ_cancel M (succM M (succM M i)) (code_numeral M 2)) H)))).
  - exists i. split;[|symmetry;apply Arithmetic.add_zero].
    change (succM M (succM M (succM M i))=addM M (succM M (succM M (succM M (zeroM M)))) i).
    now rewrite !Arithmetic.add_succ,Arithmetic.add_zero.
Qed.

Theorem source_triple_specialization_maps M v d u ab ac ad ae am td te tm rb rc sb sc k :
  substitution_lookup M ab ac (code_numeral M 1) (zeroM M) (zeroM M) v ->
  substitution_lift M ab ac (code_numeral M 1) (zeroM M) ad ae am ->
  substitution_lift M ad ae am (code_numeral M 1) td te tm ->
  source_role_reopening M d u rb rc ->source_triple_prefix M u d v sb sc ->
  substitution_composition_agrees M td te tm (code_numeral M 2)
    rb rc (code_numeral M 2) (zeroM M) sb sc (code_numeral M 3) (zeroM M) k.
Proof.
  intros HH HL1 HL2 [HOut HMid] [HU [HD HV]] i j w _ HS HT.
  destruct (@Peano.zero_or_succ (carrier M) (raw_interpretation M)
    (fun ax H rho=>axioms M ax rho H) i) as [E|[i' E]];subst i.
  - apply (proj1 (substitution_lift_head M ad ae am (code_numeral M 1) td te tm j HL2)) in HS.
    subst j. pose proof (substitution_lookup_functional M rb rc (code_numeral M 2) (zeroM M)
      _ w u HT HOut) as EW. now subst w.
  - destruct (substitution_lift_tail_inv M ad ae am (code_numeral M 1) td te tm i' j HL2 HS)
      as (j'&HS1&EJ). subst j.
    destruct (@Peano.zero_or_succ (carrier M) (raw_interpretation M)
      (fun ax H rho=>axioms M ax rho H) i') as [E|[i'' E]];subst i'.
    + apply (proj1 (substitution_lift_head M ab ac (code_numeral M 1) (zeroM M) ad ae am j' HL1)) in HS1.
      subst j'. pose proof (substitution_lookup_functional M rb rc (code_numeral M 2) (zeroM M)
        _ w d HT HMid) as EW. now subst w.
    + destruct (substitution_lift_tail_inv M ab ac (code_numeral M 1) (zeroM M) ad ae am i'' j' HL1 HS1)
        as (j''&HS0&EJ). subst j'.
      pose proof (substitution_lookup_functional M rb rc (code_numeral M 2) (zeroM M)
        _ w j'' HT (source_role_reopening_tail M rb rc j'')) as EW. subst w.
      destruct (@Peano.zero_or_succ (carrier M) (raw_interpretation M)
        (fun ax H rho=>axioms M ax rho H) i'') as [E|[i''' E]];subst i''.
      * pose proof (substitution_lookup_functional M ab ac (code_numeral M 1) (zeroM M)
          _ j'' v HS0 HH) as EJ. now subst j''.
      * pose proof (substitution_lookup_functional M ab ac (code_numeral M 1) (zeroM M)
          _ j'' i''' HS0 (substitution_singleton_tail M ab ac i''')) as EJ. subst j''.
        apply source_triple_prefix_tail.
Qed.

Theorem source_full_triple_specialize M b c n matrix inner middle outer v d u sb sc result k :
  source_bounded M matrix k ->sf_relation M SFAll matrix (zeroM M) inner ->
  sf_relation M SFAll inner (zeroM M) middle ->sf_relation M SFAll middle (zeroM M) outer ->
  source_triple_prefix M u d v sb sc ->
  numerical_substitution M matrix sb sc (code_numeral M 3) (zeroM M) result ->
  source_full_prv M b c n outer ->source_full_prv M b c n result.
Proof.
  intros HB HI HM HO HPrefix HResult POuter.
  destruct (numerical_instantiation_total M middle v) as (first&ab&ac&HH&HFirst).
  destruct (proj1 (numerical_substitution_quantifier M true inner middle ab ac (code_numeral M 1)
    (zeroM M) first HM) HFirst) as (ad&ae&am&innerA&HL1&HInnerA&HFirstAll).
  destruct (proj1 (numerical_substitution_quantifier M true matrix inner ad ae am (code_numeral M 1)
    innerA HI) HInnerA) as (td&te&tm&matrixA&HL2&HMatrixA&HInnerAll).
  assert (HInst:numerical_instantiation M middle v first) by (exists ab,ac;auto).
  assert (WF:source_sequent_wf M b c n first).
  { exact (source_wf_quantifier_instance M b c n SFAll middle outer v first (or_introl eq_refl)
      HO (source_full_prv_wellformed M b c n outer POuter) HInst). }
  pose proof (full_source_AllE M b c n middle outer v first WF POuter HO HInst) as PFirst.
  destruct WF as (bound&HFirstBound&HCtx).
  pose proof (proj1 (source_bounded_accept_unary M SFAll innerA first bound
    (or_introl eq_refl) HFirstAll) HFirstBound) as HInnerBound.
  pose proof (proj1 (source_bounded_accept_unary M SFAll matrixA innerA (succM M bound)
    (or_introl eq_refl) HInnerAll) HInnerBound) as HMatrixBound.
  destruct (source_role_reopening_total M d u) as (rb&rc&HReopen).
  destruct (numerical_substitution_total M matrixA rb rc (code_numeral M 2) (zeroM M)) as (second&HSecond).
  assert (PSecond:source_full_prv M b c n second).
  { exact (source_full_double_specialize M b c n matrixA innerA first d u rb rc second
      (succM M (succM M bound)) HMatrixBound HInnerAll HFirstAll HReopen HSecond PFirst). }
  assert (HS:numerical_substitution M matrix sb sc (code_numeral M 3) (zeroM M) second).
  { apply (numerical_substitution_composition M matrix k td te tm (code_numeral M 2)
      rb rc (code_numeral M 2) (zeroM M) sb sc (code_numeral M 3) (zeroM M)
      matrixA second HB HMatrixA HSecond).
    exact (source_triple_specialization_maps M v d u ab ac ad ae am td te tm rb rc sb sc k
      HH HL1 HL2 HReopen HPrefix). }
  pose proof (numerical_substitution_functional M matrix sb sc (code_numeral M 3) (zeroM M)
    second result HS HResult) as E. now subst second.
Qed.

Print Assumptions source_triple_specialization_maps.
Print Assumptions source_full_triple_specialize.
Print Assumptions source_triple_prefix_total.
