(** Exact image-member introduction for the literal RepC range profile.
    The relation premise is the actual simultaneous [input,output]
    substitution into the original matrix, with its parameter tail fixed. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SetSchemaConstructors
  SchemaConstructorBounds SourceBounded NumericalSubstitutionMaps NumericalSubstitution
  NumericalInstantiation SubstitutionSource SourceInstantiationConstructors NumericalSourceFull
  SchemaRenamingDescriptors SourceRoleReopening SourceReplacementWitnessMaps
  SourceReplacementCollector SourcePropositionalRebase SourceWFSeparationConstructor
  SourceOrdinalRangeMembers SourceFilterMemberIntroduction SourceRangeMemberIntroduction SourceOrdinalMemberShell.
Unset Implicit Arguments.

Definition replacement_profile_at_environment {A} (s x matrix:A) i :=
  match i with 0=>s|1=>x|_=>matrix end.
Definition E_replacement_profile_at := E_sf_all
  (E_sf_iff (E_sf SFMember (CEconst 0) (CEadd (CEvar 0) (CEconst 1)))
    (E_sf_ex (E_sf SFAnd
      (E_sf SFMember (CEconst 0) (CEadd (CEadd (CEvar 1) (CEconst 1)) (CEconst 1))) (CEvar 2)))).
Definition source_replacement_profile_at_graph M s x matrix profile :=
  code_relation M (replacement_profile_at_environment s x matrix) E_replacement_profile_at profile.

Theorem source_full_replacement_member_at M b c n phi matrix profile count
    s x d v sb sc relation input member :
  source_bounded M phi (succM M (succM M count)) ->schema_renaming M RepC phi matrix ->
  source_replacement_profile_at_graph M s x matrix profile ->source_role_reopening M d v sb sc ->
  numerical_substitution M phi sb sc (code_numeral M 2) (code_numeral M 2) relation ->
  sf_relation M SFMember v x input ->sf_relation M SFMember d s member ->
  source_full_prv M b c n profile ->source_full_prv M b c n input ->source_full_prv M b c n relation ->
  source_full_prv M b c n member.
Proof.
  intros HB HR HP HReopen HRelation HInput HMember PProfile PInput PRelation.
  unfold source_replacement_profile_at_graph,E_replacement_profile_at in HP.
  destruct (schema_expression_quantifier_split M _ SFAll _ profile HP) as (point&HPoint&HAll).
  destruct (code_relation_total M (E_sf SFMember (CEconst 0) (CEadd (CEvar 0) (CEconst 1))) (replacement_profile_at_environment s x matrix)) as (left&HLeftCode).
  destruct (code_relation_total M (E_sf_ex (E_sf SFAnd
      (E_sf SFMember (CEconst 0) (CEadd (CEadd (CEvar 1) (CEconst 1)) (CEconst 1))) (CEvar 2)))
    (replacement_profile_at_environment s x matrix)) as (ex&HExCode).
  destruct (source_range_iff_split M (replacement_profile_at_environment s x matrix) _ _ left ex point HLeftCode HExCode HPoint)
    as (forward&reverse&HForward&HReverse&HPointPair).
  destruct (schema_expression_quantifier_split M _ SFEx _ ex HExCode) as (body&HBodyCode&HEx).
  destruct (schema_expression_split M _ SFAnd _ _ body HBodyCode) as (rawinput&rawmatrix&HIR&HMR&HBody).
  change (rawmatrix=matrix) in HMR. subst rawmatrix.
  assert (HRawInput:sf_relation M SFMember (zeroM M) (succM M (succM M x)) rawinput).
  { exact (proj1 (schema_expression_graph M (replacement_profile_at_environment s x matrix)
      SFMember (CEconst 0) (CEadd (CEadd (CEvar 1) (CEconst 1)) (CEconst 1))
      (zeroM M) (succM M (succM M x)) rawinput eq_refl
      (source_code_successor_graph M (replacement_profile_at_environment s x matrix)
        (CEadd (CEvar 1) (CEconst 1)) (succM M x)
        (source_code_successor_graph M (replacement_profile_at_environment s x matrix) (CEvar 1) x eq_refl))) HIR). }
  assert (HLeft:sf_relation M SFMember (zeroM M) (succM M s) left).
  { exact (proj1 (schema_expression_graph M (replacement_profile_at_environment s x matrix) SFMember
      (CEconst 0) (CEadd (CEvar 0) (CEconst 1)) (zeroM M) (succM M s) left eq_refl
      (source_code_successor_graph M (replacement_profile_at_environment s x matrix) (CEvar 0) s eq_refl)) HLeftCode). }
  destruct (numerical_instantiation_total M ex d) as (exd&ab&ac&HHead&HSubEx).
  destruct (proj1 (numerical_substitution_quantifier M false body ex ab ac (code_numeral M 1)
    (zeroM M) exd HEx) HSubEx) as (ad&ae&am&firstbody&HL&HSubBody&HExD).
  destruct (proj1 (numerical_substitution_binary M SFAnd rawinput matrix body ad ae am (code_numeral M 1)
    firstbody (or_introl eq_refl) HBody) HSubBody)
    as (firstinput&firstmatrix&HSubInput&HSubMatrix&HFirstBody).
  destruct (proj1 (numerical_substitution_member M (zeroM M) (succM M (succM M x)) rawinput ad ae am
    (code_numeral M 1) firstinput HRawInput) HSubInput)
    as (ix&iy&HIX&HIY&HFirstInput).
  pose proof (substitution_lookup_functional M ad ae am (code_numeral M 1) _ ix (zeroM M)
    HIX (proj1 (proj2 HL))) as EX. subst ix.
  pose proof (proj2 (proj2 HL) (succM M x) x
    (substitution_singleton_tail M ab ac x)) as HLookupThree.
  pose proof (substitution_lookup_functional M ad ae am (code_numeral M 1) _ iy (succM M x)
    HIY HLookupThree) as EY. subst iy.
  destruct (numerical_instantiation_total M firstbody v) as (witness&rb&rc&HHeadV&HSubWitness).
  destruct (proj1 (numerical_substitution_binary M SFAnd firstinput firstmatrix firstbody rb rc
    (code_numeral M 1) (zeroM M) witness (or_introl eq_refl) HFirstBody) HSubWitness)
    as (finalinput&finalmatrix&HSubInputV&HSubMatrixV&HWitness).
  destruct (proj1 (numerical_substitution_member M (zeroM M) (succM M x) firstinput rb rc
    (code_numeral M 1) (zeroM M) finalinput HFirstInput) HSubInputV)
    as (vx&vy&HVX&HVY&HFinalInput).
  pose proof (substitution_lookup_functional M rb rc (code_numeral M 1) (zeroM M) _ vx v HVX HHeadV) as EX.
  subst vx.
  pose proof (substitution_lookup_functional M rb rc (code_numeral M 1) (zeroM M) _ vy x
    HVY (substitution_singleton_tail M rb rc x)) as EY. subst vy.
  pose proof (sf_relation_functional M SFMember _ _ finalinput input HFinalInput HInput) as EI.
  subst finalinput.
  assert (HMatrixInst:numerical_instantiation M firstmatrix v finalmatrix).
  { exists rb,rc. auto. }
  pose proof (source_repc_double_specialization M phi matrix count d v ab ac ad ae am firstmatrix finalmatrix sb sc
    HB HR HHead HL HSubMatrix HMatrixInst HReopen) as HFinalMatrix.
  pose proof (numerical_substitution_functional M phi sb sc (code_numeral M 2) (code_numeral M 2)
    finalmatrix relation HFinalMatrix HRelation) as EM. subst finalmatrix.
  assert (HExInst:numerical_instantiation M ex d exd).
  { exists ab,ac. auto. }
  pose proof (source_member_zero_successor_instantiation M s d left member HLeft HMember) as HLeftInst.
  destruct (sf_relation_total M SFImpl member exd) as (forwardD&HForwardD).
  destruct (sf_relation_total M SFImpl exd member) as (reverseD&HReverseD).
  destruct (sf_relation_total M SFAnd forwardD reverseD) as (instance&HInstance).
  pose proof (source_instantiation_binary M SFImpl left ex forward d member exd forwardD
    (or_intror (or_intror eq_refl)) HForward HLeftInst HExInst HForwardD) as HForwardInst.
  pose proof (source_instantiation_binary M SFImpl ex left reverse d exd member reverseD
    (or_intror (or_intror eq_refl)) HReverse HExInst HLeftInst HReverseD) as HReverseInst.
  pose proof (source_instantiation_binary M SFAnd forward reverse point d forwardD reverseD instance
    (or_introl eq_refl) HPointPair HForwardInst HReverseInst HInstance) as HPointInst.
  assert (HBodyInst:numerical_instantiation M firstbody v witness).
  { exists rb,rc. auto. }
  exact (source_full_range_member_introduction M b c n point profile d instance
    firstbody exd v witness input relation forwardD reverseD member
    HAll HPointInst HInstance HReverseD HExD HBodyInst HWitness PProfile PInput PRelation).
Qed.

Print Assumptions source_full_replacement_member_at.
