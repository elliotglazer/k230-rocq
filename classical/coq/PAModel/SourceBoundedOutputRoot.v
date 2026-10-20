(** Actual KUpperCore.bounded_output_root at carrier B=free0 and parameter
    tail1. The trace container is preserved as one existential witness. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT BetaExtension CodeExpressions
  SetFormulaCodes SourceBounded SourceBoundMonotone SourceUpperTraceProfile SourceUpperTraceExists
  SourceUpperTraceFrame SourceUpperWitnessRecipes SourceEmittedClosureRecipe SourceTraceOutputPair
  SourceUpperProofHelpers SourceEmittedFrameRequest SourceRoleReopening NumericalSubstitution
  NumericalRenaming NumericalRenamingMaps NumericalContextRenaming NumericalContexts NumericalEnvironments
  SourceQuantifierRules SourceProofRenaming SourceContextTransport SourceSequents SourceExistentialMap NumericalSourceFull
  SourceSubsetClosedPoint SourceSubsetClosedShift SourceFiniteParameters SourceFiniteParameterProofs.
From Undecidability.FOL Require Import Syntax.Facts Sets.minZF.
Unset Implicit Arguments.

Definition source_trace_output_root_recipe M phi x p out :=
  exists rb rc value emitted xc root pair,
    source_role_reopening M (succM M p)(succM M x) rb rc /\
    numerical_substitution M phi rb rc (code_numeral M 2)(code_numeral M 2) value /\
    source_emitted_closure_recipe M phi emitted /\
    sf_relation M SFMember (succM M x)(zeroM M) xc /\
    sf_relation M SFImpl value xc root /\sf_relation M SFAnd root emitted pair /\
    sf_relation M SFEx pair (zeroM M) out.

Theorem source_trace_output_root_recipe_total M phi x p :
  exists out,source_trace_output_root_recipe M phi x p out.
Proof.
  destruct (source_role_reopening_total M (succM M p)(succM M x)) as [rb [rc HR]].
  destruct (numerical_substitution_total M phi rb rc (code_numeral M 2)(code_numeral M 2)) as [value HV].
  destruct (source_emitted_closure_recipe_total M phi) as [emitted HE].
  destruct (sf_relation_total M SFMember (succM M x)(zeroM M)) as [xc HX].
  destruct (sf_relation_total M SFImpl value xc) as [root HI].
  destruct (sf_relation_total M SFAnd root emitted) as [pair HA].
  destruct (sf_relation_total M SFEx pair (zeroM M)) as [out HO].
  exists out,rb,rc,value,emitted,xc,root,pair. repeat first [assumption|split].
Qed.

Theorem source_full_bounded_output_root M cb cc cn phi n profile exprofile witness subsetclosed
    x p xb pb target :
  source_bounded M phi (succM M (succM M n)) ->source_upper_trace_profile M phi profile ->
  sf_relation M SFEx profile (zeroM M) exprofile ->
  source_upper_witness_closed_recipe M phi (code_numeral M 1)(zeroM M) witness ->
  source_subset_closed_graph M (zeroM M) subsetclosed ->
  sf_relation M SFMember x (zeroM M) xb ->sf_relation M SFMember p (zeroM M) pb ->
  source_trace_output_root_recipe M phi x p target ->
  source_full_prv M cb cc cn exprofile ->source_full_prv M cb cc cn witness ->
  source_full_prv M cb cc cn subsetclosed ->source_full_prv M cb cc cn xb ->
  source_full_prv M cb cc cn pb ->source_full_prv M cb cc cn target.
Proof.
  intros HP HProfile HEx HW HSC HXB HPB
    (rb&rc&value&emitted&xc&root&pair&HMap&HValue&HEmitted&HXC&HRoot&HPair&HTarget)
    PEx PW PSC PXB PPB.
  destruct (source_full_prv_wellformed M cb cc cn exprofile PEx) as [j [BEx HC]].
  pose proof (proj1 (source_bounded_accept_unary M SFEx profile exprofile j
    (or_intror eq_refl) HEx) BEx) as BProfile.
  destruct (context_shift_total M cb cc cn) as [sb [sc HShift]].
  assert (FS:source_context_finite_bound M sb sc cn).
  { exists (succM M j). exact (context_shift_preserves_bound M cb cc cn sb sc j HShift HC). }
  destruct (environment_cons_total M sb sc cn profile) as [ub [uc [un HCons]]].
  destruct (source_full_assume M sb sc cn profile ub uc un
    (source_wf_from_finite M sb sc cn profile (succM M j) BProfile FS) HCons) as [FU PProfile].
  destruct (source_full_upper_witness_closed_shift_total M cb cc cn phi (succM M (succM M n))
    (code_numeral M 1)(zeroM M) witness sb sc HP HW HShift PW) as [witness' [HW' PW']].
  pose proof (source_full_weaken_cons_finite M sb sc cn profile ub uc un witness' HCons FU PW') as PWB.
  destruct (code_relation_total M (source_parameter_expression source_three_parameter_names
    (source_point_subset_closed $0)) (fun _=>code_numeral M 1)) as [closed' HSC'].
  pose proof (source_point_subset_closed_shift M (fun _=>zeroM M)(fun _=>code_numeral M 1)
    subsetclosed closed' eq_refl HSC HSC') as HClosedShift.
  pose proof (source_full_prv_renaming M cb cc cn subsetclosed (zeroM M)(zeroM M)(zeroM M)
    (code_numeral M 1) sb sc closed' PSC HShift HClosedShift) as PSC'.
  pose proof (source_full_weaken_cons_finite M sb sc cn profile ub uc un closed' HCons FU PSC') as PSCB.
  destruct (sf_relation_total M SFMember (succM M x)(code_numeral M 1)) as [xb' HXB'].
  destruct (sf_relation_total M SFMember (succM M p)(code_numeral M 1)) as [pb' HPB'].
  assert (Rxb:source_formula_shift M xb xb').
  { apply (proj2 (numerical_renaming_member M x (zeroM M) xb (zeroM M)(zeroM M)(zeroM M)
      (code_numeral M 1) xb' HXB)).
    exists (succM M x),(code_numeral M 1). split;[apply context_shift_lookup;reflexivity|].
    split;[apply context_shift_lookup;reflexivity|exact HXB']. }
  assert (Rpb:source_formula_shift M pb pb').
  { apply (proj2 (numerical_renaming_member M p (zeroM M) pb (zeroM M)(zeroM M)(zeroM M)
      (code_numeral M 1) pb' HPB)).
    exists (succM M p),(code_numeral M 1). split;[apply context_shift_lookup;reflexivity|].
    split;[apply context_shift_lookup;reflexivity|exact HPB']. }
  pose proof (source_full_prv_renaming M cb cc cn xb (zeroM M)(zeroM M)(zeroM M)
    (code_numeral M 1) sb sc xb' PXB HShift Rxb) as PXB'.
  pose proof (source_full_prv_renaming M cb cc cn pb (zeroM M)(zeroM M)(zeroM M)
    (code_numeral M 1) sb sc pb' PPB HShift Rpb) as PPB'.
  pose proof (source_full_weaken_cons_finite M sb sc cn profile ub uc un xb' HCons FU PXB') as PXBB.
  pose proof (source_full_weaken_cons_finite M sb sc cn profile ub uc un pb' HCons FU PPB') as PPBB.
  pose proof (source_full_trace_output_pair M ub uc un phi n profile witness' closed'
    (succM M x)(succM M p) xc xb' pb' rb rc value emitted root pair
    HP HProfile HW' HSC' HXC HXB' HPB' HMap HValue HEmitted HRoot HPair
    PSCB PWB PProfile PXBB PPBB) as PPair.
  destruct (source_full_prv_wellformed M ub uc un pair PPair) as [k [BPair _]].
  assert (WTarget:source_sequent_wf M cb cc cn target).
  { apply (source_wf_from_finite M cb cc cn target k);[|now exists j].
    apply (proj2 (source_bounded_accept_unary M SFEx pair target k (or_intror eq_refl) HTarget)).
    apply (source_bounded_monotone M pair k (succM M k) BPair).
    exact (coding_lt_trans M k (succM M k)(succM M (succM M k))
      (coding_lt_succ M k)(coding_lt_succ M (succM M k))). }
  destruct (numerical_renaming_total M target (zeroM M)(zeroM M)(zeroM M)
    (code_numeral M 1)) as [shifted HTargetShift].
  exact (source_full_exists_map M cb cc cn profile pair exprofile target sb sc ub uc un shifted
    WTarget HEx HTarget HShift HCons HTargetShift PEx PPair).
Qed.

Print Assumptions source_trace_output_root_recipe_total.
Print Assumptions source_full_bounded_output_root.
