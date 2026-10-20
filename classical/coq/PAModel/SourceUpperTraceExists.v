(** Actual trace existence from the exact Separation instance. The proof
    is uniform over internal matrices and uses literal source AllE. *)
From PAModel Require Import Model FiniteCoding CodeExpressions NumericalProofs
  SetFormulaCodes SourceBounded SourceUpperTraceRecipe SourceUpperTraceProfile
  SourceFiniteCutoffShift SourceSeparationZeroSpecialization SetSchemaConstructors
  SchemaRenamingDescriptors SchemaConstructorBounds SourceInstantiationConstructors
  SourceZFRSeparationUse SourceZFRProvability NumericalSourceFull SourceSequents.
Unset Implicit Arguments.

Theorem source_full_upper_trace_exists M cb cc cn phi count trace shifted body raw profile exprofile :
  source_bounded M phi (succM M (succM M count)) ->
  source_upper_trace M phi trace -> source_cutoff_shift M 1 trace shifted ->
  schema_renaming M SepBody trace body -> sf_separation_constructor M body raw ->
  code_relation M (fun _=>shifted) (E_upper_trace_profile (CEvar 0)) profile ->
  sf_relation M SFEx profile (zeroM M) exprofile ->
  source_full_prv M cb cc cn raw -> source_full_prv M cb cc cn exprofile.
Proof.
  intros HP HT HS HB HR HProfile HEx PR.
  pose proof (source_upper_trace_bounded M phi trace count HP HT) as HTraceBound.
  destruct (source_separation_zero_specialization M trace body raw shifted
    (succM M (succM M count)) HTraceBound HB HR HS)
    as [rawbody [specialized [HAll [HInst HSpecialized]]]].
  assert (HE:code_relation M (fun _=>shifted) (E_separation_zero (CEvar 0)) exprofile).
  { unfold E_separation_zero. change (code_relation M (fun _=>shifted)
      (E_sf SFEx (E_upper_trace_profile (CEvar 0)) (CEconst 0)) exprofile).
    exact (proj2 (schema_expression_graph M (fun _=>shifted) SFEx
      (E_upper_trace_profile (CEvar 0)) (CEconst 0) profile (zeroM M) exprofile
      HProfile eq_refl) HEx). }
  pose proof (code_relation_functional M _ _ specialized exprofile HSpecialized HE) as E.
  subst specialized.
  apply (full_source_AllE M cb cc cn rawbody raw (zeroM M) exprofile).
  - exact (source_wf_quantifier_instance M cb cc cn SFAll rawbody raw
      (zeroM M) exprofile (or_introl eq_refl) HAll
      (source_full_prv_wellformed M cb cc cn raw PR) HInst).
  - exact PR.
  - exact HAll.
  - exact HInst.
Qed.

Theorem source_zfr_upper_trace_exists M phi count profile exprofile :
  source_bounded M phi (succM M (succM M count)) ->
  source_upper_trace_profile M phi profile ->
  sf_relation M SFEx profile (zeroM M) exprofile ->
  source_zfr_provable M exprofile.
Proof.
  intros HP [trace [shifted [HT [HS HProfile]]]] HEx.
  destruct (source_zfr_separation_open_total M trace (succM M count)
    (source_upper_trace_bounded M phi trace count HP HT))
    as [body [raw [HB [HR [cb [cc [cn [HC PR]]]]]]]].
  exists cb,cc,cn. split;[exact HC|].
  exact (source_full_upper_trace_exists M cb cc cn phi count trace shifted body raw
    profile exprofile HP HT HS HB HR HProfile HEx PR).
Qed.

Theorem source_zfr_upper_trace_exists_total M phi count :
  source_bounded M phi (succM M (succM M count)) ->
  exists profile exprofile,source_upper_trace_profile M phi profile /\
    sf_relation M SFEx profile (zeroM M) exprofile /\ source_zfr_provable M exprofile.
Proof.
  intro HP. destruct (source_upper_trace_profile_total M phi) as [profile HProfile].
  destruct (sf_relation_total M SFEx profile (zeroM M)) as [exprofile HEx].
  exists profile,exprofile. split;[exact HProfile|]. split;[exact HEx|].
  exact (source_zfr_upper_trace_exists M phi count profile exprofile HP HProfile HEx).
Qed.

Print Assumptions source_full_upper_trace_exists.
Print Assumptions source_zfr_upper_trace_exists.
Print Assumptions source_zfr_upper_trace_exists_total.
