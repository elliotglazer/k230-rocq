(** Package the original four trace/closure proofs while source contexts
    are shifted or extended. All matrices are real internal syntax graphs. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions
  SetFormulaCodes SetSchemaConstructors SourceBounded SourceTraceProfileShell
  SourceTraceDeltaShift SourceUpperWitnessRecipes SourceWitnessDeltaShift SourceUpperProofHelpers
  SourceSubsetClosedPoint SourceSubsetClosedShift SourceFiniteParameters SourceFiniteParameterProofs
  NumericalRenaming NumericalRenamingMaps NumericalContextRenaming NumericalContexts
  NumericalEnvironments NumericalSourceFull SourceProofRenaming SourceContextTransport SourceQuantifierRules.
From Undecidability.FOL Require Import Syntax.Facts Sets.minZF.
Unset Implicit Arguments.

Definition source_subset_closed_graph M b f :=
  code_relation M (fun _=>b) (source_parameter_expression source_three_parameter_names
    (source_point_subset_closed $0)) f.

Lemma source_subset_closed_graph_environment M rho f :
  source_subset_closed_graph M (rho 0) f <->
  code_relation M rho (source_parameter_expression source_three_parameter_names
    (source_point_subset_closed $0)) f.
Proof. unfold source_subset_closed_graph. reflexivity. Qed.

Definition source_upper_trace_frame M cb cc cn phi k delta c b x :=
  exists profile theta atom matrix body witness subsetclosed xb,
  source_bounded M phi k /\
  numerical_renaming M phi (code_numeral M 3)(code_numeral M 1)(code_numeral M 2) delta matrix /\
  sf_relation M SFMember (zeroM M)(succM M (succM M b)) atom /\
  sf_relation M SFAnd atom matrix body /\sf_relation M SFEx body (zeroM M) theta /\
  source_trace_profile_shell M theta c b profile /\
  source_upper_witness_closed_recipe M phi delta b witness /\
  source_subset_closed_graph M b subsetclosed /\sf_relation M SFMember x b xb /\
  source_full_prv M cb cc cn subsetclosed /\source_full_prv M cb cc cn witness /\
  source_full_prv M cb cc cn profile /\source_full_prv M cb cc cn xb.

Theorem source_upper_trace_frame_weaken M cb cc cn phi k delta c b x a ub uc un :
  source_upper_trace_frame M cb cc cn phi k delta c b x ->
  environment_cons M cb cc cn a ub uc un ->source_context_finite_bound M ub uc un ->
  source_upper_trace_frame M ub uc un phi k delta c b x.
Proof.
  intros (profile&theta&atom&matrix&body&witness&sc&xb&HP&HM&HA&HB&HE&HProfile&HW&HSC&HXB&PSC&PW&PProfile&PXB)
    HCons HC.
  exists profile,theta,atom,matrix,body,witness,sc,xb.
  repeat split;try assumption;
    eapply source_full_weaken_cons_finite;eassumption.
Qed.

Theorem source_upper_trace_frame_shift M cb cc cn phi k delta c b x sb sc :
  source_upper_trace_frame M cb cc cn phi k delta c b x ->
  context_shift M cb cc cn sb sc ->
  source_upper_trace_frame M sb sc cn phi k (succM M delta)(succM M c)(succM M b)(succM M x).
Proof.
  intros (profile&theta&atom&matrix&body&witness&closed&xb&HP&HM&HA&HB&HE&HProfile&HW&HSC&HXB&PSC&PW&PProfile&PXB)
    HShift.
  destruct (numerical_renaming_total M profile (zeroM M)(zeroM M)(zeroM M)
    (code_numeral M 1)) as [profile' HPS].
  destruct (source_trace_delta_profile_shift M phi k delta c b profile theta atom matrix body profile'
    HP HM HA HB HE HProfile HPS)
    as [theta' [atom' [matrix' [body' [HM' [HA' [HB' [HE' HProfile']]]]]]]].
  destruct (source_full_upper_witness_closed_shift_total M cb cc cn phi k delta b witness sb sc
    HP HW HShift PW) as [witness' [HW' PW']].
  destruct (code_relation_total M (source_parameter_expression source_three_parameter_names
    (source_point_subset_closed $0)) (fun _=>succM M b)) as [closed' HSC'].
  pose proof (source_point_subset_closed_shift M (fun _=>b)(fun _=>succM M b) closed closed'
    eq_refl HSC HSC') as HCS.
  destruct (sf_relation_total M SFMember (succM M x)(succM M b)) as [xb' HXB'].
  assert (HXBS:source_formula_shift M xb xb').
  { apply (proj2 (numerical_renaming_member M x b xb (zeroM M)(zeroM M)(zeroM M)
      (code_numeral M 1) xb' HXB)).
    exists (succM M x),(succM M b). split;[apply context_shift_lookup;reflexivity|].
    split;[apply context_shift_lookup;reflexivity|exact HXB']. }
  exists profile',theta',atom',matrix',body',witness',closed',xb'.
  repeat split;try assumption.
  - exact (source_full_prv_renaming M cb cc cn closed (zeroM M)(zeroM M)(zeroM M)
      (code_numeral M 1) sb sc closed' PSC HShift HCS).
  - exact (source_full_prv_renaming M cb cc cn profile (zeroM M)(zeroM M)(zeroM M)
      (code_numeral M 1) sb sc profile' PProfile HShift HPS).
  - exact (source_full_prv_renaming M cb cc cn xb (zeroM M)(zeroM M)(zeroM M)
      (code_numeral M 1) sb sc xb' PXB HShift HXBS).
Qed.

Print Assumptions source_subset_closed_graph_environment.
Print Assumptions source_upper_trace_frame_weaken.
Print Assumptions source_upper_trace_frame_shift.
