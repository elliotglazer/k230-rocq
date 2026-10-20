(** Two native AllE steps realize the simultaneous prefix [output,input].
    The first singleton map is lifted through the surviving binder; names
    inserted by it are therefore not accidentally substituted a second time. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions
  NumericalProofs SetFormulaCodes SetCodeDescent SourceBounded
  NumericalSubstitutionMaps NumericalSubstitution NumericalInstantiation SubstitutionSource
  SourceSubstitutionComposition SourceRoleReopening SourceRoleAbstraction
  SourceSequents NumericalSourceFull SourceInstantiationConstructors.
From FOL.Tennenbaum Require Import Peano.
Unset Implicit Arguments.

Lemma source_double_specialization_maps M input output ab ac ad ae am rb rc sb sc k :
  substitution_lookup M ab ac (succM M (zeroM M)) (zeroM M) (zeroM M) input ->
  substitution_lift M ab ac (succM M (zeroM M)) (zeroM M) ad ae am ->
  substitution_lookup M rb rc (succM M (zeroM M)) (zeroM M) (zeroM M) output ->
  source_role_reopening M input output sb sc ->
  substitution_composition_agrees M ad ae am (succM M (zeroM M))
    rb rc (succM M (zeroM M)) (zeroM M) sb sc (code_numeral M 2) (zeroM M) k.
Proof.
  intros HA HL HR [HOut HIn] i j v _ HS HT.
  destruct (@Peano.zero_or_succ (carrier M) (raw_interpretation M)
    (fun ax H rho=>axioms M ax rho H) i) as [E|[i' E]];subst i.
  - apply (proj1 (substitution_lift_head M ab ac (succM M (zeroM M))
      (zeroM M) ad ae am j HL)) in HS. subst j.
    assert (v=output) by (eapply substitution_lookup_functional;[exact HT|exact HR]).
    subst v. exact HOut.
  - destruct (substitution_lift_tail_inv M ab ac (succM M (zeroM M))
      (zeroM M) ad ae am i' j HL HS) as (j'&HS'&EJ). subst j.
    assert (EV:v=j').
    { eapply substitution_lookup_functional;[exact HT|apply substitution_singleton_tail]. }
    subst v.
    destruct (@Peano.zero_or_succ (carrier M) (raw_interpretation M)
      (fun ax H rho=>axioms M ax rho H) i') as [E|[i'' E]];subst i'.
    + assert (j'=input) by (eapply substitution_lookup_functional;[exact HS'|exact HA]).
      subst j'. exact HIn.
    + assert (j'=i'') by (eapply substitution_lookup_functional;[exact HS'|apply substitution_singleton_tail]).
      subst j'. apply source_role_reopening_tail.
Qed.

Theorem source_full_double_specialize M b c n matrix inner outer input output sb sc result k :
  source_bounded M matrix k ->
  sf_relation M SFAll matrix (zeroM M) inner ->
  sf_relation M SFAll inner (zeroM M) outer ->
  source_role_reopening M input output sb sc ->
  numerical_substitution M matrix sb sc (code_numeral M 2) (zeroM M) result ->
  source_full_prv M b c n outer -> source_full_prv M b c n result.
Proof.
  intros HM HI HO HReopen HResult HProof.
  destruct (numerical_instantiation_total M inner input) as (first&ab&ac&HHead&HFirst).
  destruct (proj1 (numerical_substitution_quantifier M true matrix inner ab ac
    (succM M (zeroM M)) (zeroM M) first HI) HFirst)
    as (ad&ae&am&matrixA&HL&HA&HAllA).
  destruct (numerical_instantiation_total M matrixA output) as (second&rb&rc&HOut&HSecond).
  assert (HComposed:numerical_substitution M matrix sb sc (code_numeral M 2) (zeroM M) second).
  { apply (numerical_substitution_composition M matrix k ad ae am (succM M (zeroM M))
      rb rc (succM M (zeroM M)) (zeroM M) sb sc (code_numeral M 2)
      (zeroM M) matrixA second HM HA HSecond).
    exact (source_double_specialization_maps M input output ab ac ad ae am rb rc sb sc k
      HHead HL HOut HReopen). }
  assert (E:second=result) by (eapply numerical_substitution_functional; eassumption).
  subst second.
  assert (HInstFirst:numerical_instantiation M inner input first).
  { exists ab,ac. auto. }
  assert (HInstSecond:numerical_instantiation M matrixA output result).
  { exists rb,rc. auto. }
  assert (HWFirst:source_sequent_wf M b c n first).
  { exact (source_wf_quantifier_instance M b c n SFAll inner outer input first
      (or_introl eq_refl) HO (source_full_prv_wellformed M b c n outer HProof) HInstFirst). }
  assert (HPFirst:source_full_prv M b c n first).
  { exact (full_source_AllE M b c n inner outer input first HWFirst HProof HO HInstFirst). }
  apply (full_source_AllE M b c n matrixA first output result);[|exact HPFirst|exact HAllA|exact HInstSecond].
  exact (source_wf_quantifier_instance M b c n SFAll matrixA first output result
    (or_introl eq_refl) HAllA HWFirst HInstSecond).
Qed.

Corollary source_full_abstract_double_specialize M b c n input output phi abstract inner outer k :
  source_bounded M phi k -> source_role_abstraction M input output phi abstract ->
  sf_relation M SFAll abstract (zeroM M) inner ->
  sf_relation M SFAll inner (zeroM M) outer ->
  source_full_prv M b c n outer -> source_full_prv M b c n phi.
Proof.
  intros HP HA HI HO HProof.
  destruct (source_role_abstraction_reopens M input output phi abstract k HP HA)
    as (sb&sc&HReopen&HSub).
  exact (source_full_double_specialize M b c n abstract inner outer input output sb sc phi
    (succM M (succM M k)) (source_role_abstraction_bounded M input output phi abstract k HP HA)
    HI HO HReopen HSub HProof).
Qed.

Print Assumptions source_full_double_specialize.
Print Assumptions source_full_abstract_double_specialize.
