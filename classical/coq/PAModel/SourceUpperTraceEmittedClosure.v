(** Actual arbitrary-code trace_emitted_closure. Subset closure and witness
    closure of B, together with its actual Separation trace, produce the
    literal KPrimeCore emitted closure of C. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions SetFormulaCodes
  SetSchemaConstructors SourceBounded SourceNativeKMatrixMaps SourceEmittedClosureRecipe
  SourceUpperTraceProfile SourceUpperProfileExpansion SourceEmittedClosureShell
  SourceTraceProfileShell SourceTraceDeltaShift SourceUpperTraceFrame SourceUpperProofHelpers
  SourceEmittedFrameRequest SourceEmittedInnerUniversals SourceSubsetGuardShift
  SourceSubsetClosedPoint SourceSubsetClosedShift SourceFiniteParameters SourceFiniteParameterProofs
  SourceUpperWitnessRecipes SourceTracePointRules SourceSeparationSubset SourcePropositionalTemplates
  SourceDerivedRules SourceConjunctionRules SourceUniversalPropositional SourceExistentialMap
  NumericalContexts NumericalEnvironments NumericalContextRenaming NumericalRenaming
  SourceProofRenaming SourceQuantifierRules SourceContextTransport NumericalSourceFull SourceSequents.
From Undecidability.FOL Require Import Syntax.Facts Sets.minZF.
Unset Implicit Arguments.

Theorem source_full_upper_trace_emitted_closure M cb cc cn phi n profile witness subsetclosed target :
  source_bounded M phi (succM M (succM M n)) ->source_upper_trace_profile M phi profile ->
  source_upper_witness_closed_recipe M phi (code_numeral M 2)(code_numeral M 1) witness ->
  source_subset_closed_graph M (code_numeral M 1) subsetclosed ->
  source_emitted_closure_recipe M phi target ->
  source_full_prv M cb cc cn subsetclosed ->source_full_prv M cb cc cn witness ->
  source_full_prv M cb cc cn profile ->source_full_prv M cb cc cn target.
Proof.
  intros HP HSource HW HSC HRecipe PSC PW PProfile.
  pose proof (source_emitted_closure_recipe_bound M phi target n HP HRecipe) as BTarget.
  destruct HRecipe as (ma&mb&mc&HKA&HKB&HKC&HTargetCode).
  destruct (source_upper_profile_expansion M phi (succM M (succM M n)) profile HP HSource)
    as (theta&atom&matrix&pbody&left&right&point&HM&HA&HB&HE&HL&HR&HPoint&HAllProfile&HProfile).
  pose proof (source_native_k_matrix_functional M NativeKA phi matrix ma HM HKA) as EM. subst matrix.
  destruct (source_emitted_closure_shell M (schema_env3 ma mb mc) ma mb mc target
    eq_refl eq_refl eq_refl HTargetCode)
    as (xc&exP&pair&allU&subset&uimp&allY&yimp&exZ&final&selected&outerimp&
      HXC&HSelected&HFinal&HExZ&HImpY&HAllY&HSubset&HImpU&HAllU&HAnd&HExP&HOuter&HAllTarget).
  pose proof (sf_relation_functional M SFMember (zeroM M)(code_numeral M 1) left xc HL HXC) as EL.
  subst left.
  pose proof (proj1 (source_bounded_accept_unary M SFAll outerimp target
    (succM M (succM M n))(or_introl eq_refl) HAllTarget) BTarget) as BOuter.
  pose proof (proj1 (source_bounded_accept_binary M SFImpl xc exP outerimp
    (succM M (succM M (succM M n)))(or_intror (or_intror eq_refl)) HOuter) BOuter) as BOuterParts.
  destruct BOuterParts as [BXC BExP].
  pose proof (proj1 (source_bounded_accept_unary M SFEx pair exP
    (succM M (succM M (succM M n)))(or_intror eq_refl) HExP) BExP) as BPair.
  pose proof (proj2 (proj1 (source_bounded_accept_binary M SFAnd ma allU pair
    (succM M (succM M (succM M (succM M n))))(or_introl eq_refl) HAnd) BPair)) as BAllU.
  destruct (source_full_prv_wellformed M cb cc cn profile PProfile) as [j [_ HC]].
  assert (FC:source_context_finite_bound M cb cc cn) by now exists j.
  destruct (context_shift_total M cb cc cn) as [xb [xcx HShiftX]].
  pose proof (source_context_finite_bound_shift M cb cc cn xb xcx FC HShiftX) as FX.
  pose proof (source_full_all_shift M cb cc cn point profile xb xcx HAllProfile PProfile HShiftX) as PPoint.
  destruct (environment_cons_total M xb xcx cn xc) as [ib [ic [il HConsX]]].
  destruct (source_full_assume M xb xcx cn xc ib ic il
    (source_wf_from_finite M xb xcx cn xc _ BXC FX) HConsX) as [FI PXC].
  pose proof (source_full_weaken_cons_finite M xb xcx cn xc ib ic il point HConsX FI PPoint) as PPointI.
  destruct (source_trace_point_unpack M xc right theta point HPoint)
    as (rhs&forward&reverse&HAndR&HFwd&HRev&HIff).
  pose proof (source_full_conjunction_left M ib ic il forward reverse point HIff PPointI) as PFwd.
  pose proof (source_full_modus_ponens M ib ic il xc rhs forward HFwd PFwd PXC) as PRhs.
  pose proof (source_full_conjunction_left M ib ic il right theta rhs HAndR PRhs) as PXB.
  pose proof (source_full_conjunction_right M ib ic il right theta rhs HAndR PRhs) as PTheta.
  destruct (numerical_renaming_total M profile (zeroM M)(zeroM M)(zeroM M)
    (code_numeral M 1)) as [profileX HProfileShift].
  destruct (source_trace_delta_profile_shift M phi (succM M (succM M n)) (code_numeral M 2)
    (zeroM M)(code_numeral M 1) profile theta atom ma pbody profileX
    HP HM HA HB HE HProfile HProfileShift)
    as (thetaX&atomX&matrixX&bodyX&HMX&HAX&HBX&HEX&HProfileX).
  pose proof (source_full_prv_renaming M cb cc cn profile (zeroM M)(zeroM M)(zeroM M)
    (code_numeral M 1) xb xcx profileX PProfile HShiftX HProfileShift) as PProfileX.
  destruct (source_full_upper_witness_closed_shift_total M cb cc cn phi (succM M (succM M n))
    (code_numeral M 2)(code_numeral M 1) witness xb xcx HP HW HShiftX PW)
    as (witnessX&HWX&PWX).
  destruct (code_relation_total M (source_parameter_expression source_three_parameter_names
    (source_point_subset_closed $0)) (fun _=>code_numeral M 2)) as [scX HSCX].
  pose proof (source_point_subset_closed_shift M (fun _=>code_numeral M 1)
    (fun _=>code_numeral M 2) subsetclosed scX eq_refl HSC HSCX) as HSCShift.
  pose proof (source_full_prv_renaming M cb cc cn subsetclosed (zeroM M)(zeroM M)(zeroM M)
    (code_numeral M 1) xb xcx scX PSC HShiftX HSCShift) as PScX.
  assert (FrameI:source_upper_trace_frame M ib ic il phi (succM M (succM M n))
      (code_numeral M 3)(code_numeral M 1)(code_numeral M 2)(zeroM M)).
  { exists profileX,thetaX,atomX,matrixX,bodyX,witnessX,scX,right.
    repeat split;try assumption;
      eapply source_full_weaken_cons_finite;eassumption. }
  destruct (context_shift_total M ib ic il) as [pb [pc HShiftP]].
  pose proof (source_context_finite_bound_shift M ib ic il pb pc FI HShiftP) as FP.
  destruct (source_full_prv_wellformed M ib ic il theta PTheta) as [kt [BT _]].
  pose proof (proj1 (source_bounded_accept_unary M SFEx pbody theta kt
    (or_intror eq_refl) HE) BT) as BBody.
  destruct (environment_cons_total M pb pc il pbody) as [qb [qc [ql HConsP]]].
  destruct (source_full_assume M pb pc il pbody qb qc ql
    (source_wf_from_finite M pb pc il pbody (succM M kt) BBody FP) HConsP) as [FQ PBody].
  pose proof (source_full_conjunction_right M qb qc ql atom ma pbody HB PBody) as PMa.
  pose proof (source_upper_trace_frame_shift M ib ic il phi (succM M (succM M n))
    (code_numeral M 3)(code_numeral M 1)(code_numeral M 2)(zeroM M) pb pc FrameI HShiftP) as FrameP.
  pose proof (source_upper_trace_frame_weaken M pb pc il phi (succM M (succM M n))
    (code_numeral M 4)(code_numeral M 2)(code_numeral M 3)(code_numeral M 1)
    pbody qb qc ql FrameP HConsP FQ) as FrameQ.
  destruct (numerical_renaming_total M subset (zeroM M)(zeroM M)(zeroM M)
    (code_numeral M 1)) as [subset' HSubShift].
  pose proof (source_emitted_subset_guard_shift M (schema_env3 ma mb mc) subset subset'
    HSubset HSubShift) as HSubCode.
  pose proof (source_full_emitted_inner_universals M qb qc ql phi n allU subset uimp allY yimp
    mb mc selected final exZ subset' (succM M (succM M (succM M (succM M n))))
    FrameQ BAllU HAllU HImpU HAllY HImpY HKB HKC HFinal HSelected HExZ HSubShift HSubCode) as PAllU.
  pose proof (source_full_conjunction M qb qc ql ma allU pair HAnd PMa PAllU) as PPair.
  destruct (numerical_renaming_total M exP (zeroM M)(zeroM M)(zeroM M)
    (code_numeral M 1)) as [exP' HExPShift].
  pose proof (source_full_exists_map M ib ic il pbody pair theta exP pb pc qb qc ql exP'
    (source_wf_from_finite M ib ic il exP _ BExP FI)
    HE HExP HShiftP HConsP HExPShift PTheta PPair) as PExP.
  pose proof (source_full_implication_intro M xb xcx cn xc exP outerimp ib ic il HConsX HOuter PExP) as POuter.
  exact (source_full_all_intro M cb cc cn outerimp target xb xcx FC HShiftX HAllTarget POuter).
Qed.

Print Assumptions source_full_upper_trace_emitted_closure.
