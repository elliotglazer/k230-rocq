(** Exact named witness for an environment-carrier point. The witness
 is allocated above the whole formula bound, including its carrier name. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SourceBounded
 SourceFiniteCutoffShift SourceCutoffShiftCommutation SourceCutoffShiftConstructors SourceQfFunctionality
 NumericalSubstitutionMaps NumericalSubstitution NumericalRenamingMaps NumericalRenaming
 SourceRepresentativeRenaming SourceNamedCutoffQuantifiers SourceNamedQuantifierRules.
Unset Implicit Arguments.
Lemma environment_cutoff_member M r atom shifted:
 sf_relation M SFMember(zeroM M)(succM M r)atom ->
 sf_relation M SFMember(zeroM M)(succM M(succM M r))shifted ->source_cutoff_shift M 1 atom shifted.
Proof.
 intros HA HS. destruct(source_cutoff_shift_map_total M 1)as(b&c&n&HM).
 exists b,c,n. split;[exact HM|].
 apply(proj2(numerical_substitution_member M(zeroM M)(succM M r)atom b c n(code_numeral M 2)shifted HA)).
 exists(zeroM M),(succM M(succM M r)). split.
 - exact(source_cutoff_shift_map_fixed_lookup M 1 b c n HM 0).
 - exact(conj(source_cutoff_shift_map_tail_lookup M 1 b c n r HM)HS).
Qed.
Theorem source_environment_coverage_witness_total M first guard r witness k:
 source_bounded M first k ->source_cutoff_shift M 1 first guard ->coding_lt M(succM M r)k ->
 ~coding_lt M witness k ->
 exists named member namedmember shiftedmember body namedbody shiftedbody point,
 source_representative_renaming M witness first named /\
 sf_relation M SFMember(zeroM M)(succM M r)member /\
 sf_relation M SFMember witness(succM M r)namedmember /\
 sf_relation M SFMember(zeroM M)(succM M(succM M r))shiftedmember /\
 sf_relation M SFImpl first member body /\sf_relation M SFImpl named namedmember namedbody /\
 sf_relation M SFImpl guard shiftedmember shiftedbody /\sf_relation M SFAll shiftedbody(zeroM M)point /\
 source_representative_renaming M witness body namedbody /\
 source_named_quantifier M true witness namedbody point /\source_bounded M body k.
Proof.
 intros BF HGuard HR HW.
 destruct(source_representative_renaming_total M witness first)as(named&HNamed).
 destruct(sf_relation_total M SFMember(zeroM M)(succM M r))as(member&HM).
 destruct(sf_relation_total M SFMember witness(succM M r))as(namedmember&HNM).
 destruct(sf_relation_total M SFMember(zeroM M)(succM M(succM M r)))as(shiftedmember&HSM).
 destruct(sf_relation_total M SFImpl first member)as(body&HB).
 destruct(sf_relation_total M SFImpl named namedmember)as(namedbody&HNB).
 destruct(sf_relation_total M SFImpl guard shiftedmember)as(shiftedbody&HSB).
 destruct(sf_relation_total M SFAll shiftedbody(zeroM M))as(point&HP).
 assert(BM:source_bounded M member k).
 { apply(proj2(source_bounded_accept_atom M SFMember(zeroM M)(succM M r)member k(or_introl eq_refl)HM)).
   split;[|exact HR]. exact(coding_lt_trans M(zeroM M)(succM M r)k(coding_zero_lt_succ M r)HR). }
 assert(BBody:source_bounded M body k).
 { exact(proj2(source_bounded_accept_binary M SFImpl first member body k(or_intror(or_intror eq_refl))HB)(conj BF BM)). }
 assert(HMember:source_representative_renaming M witness member namedmember).
 { apply(proj2(numerical_renaming_member M(zeroM M)(succM M r)member witness witness(code_numeral M 1)(zeroM M)namedmember HM)).
   exists witness,(succM M r). split;[apply representative_lookup_zero|]. split;[|exact HNM].
   apply representative_lookup_nonzero. intro E. exact(Model.zero_ne_succ M r(eq_sym E)). }
 assert(HBody:source_representative_renaming M witness body namedbody).
 { apply(proj2(numerical_renaming_binary M SFImpl first member body witness witness(code_numeral M 1)(zeroM M)namedbody
    (or_intror(or_intror eq_refl))HB)). exists named,namedmember. exact(conj HNamed(conj HMember HNB)). }
 assert(HCut:source_cutoff_shift M 1 body shiftedbody).
 { exact(source_cutoff_shift_binary M 1 SFImpl first member body guard shiftedmember shiftedbody
   (or_intror(or_intror eq_refl))HB HSB HGuard(environment_cutoff_member M r member shiftedmember HM HSM)). }
 exists named,member,namedmember,shiftedmember,body,namedbody,shiftedbody,point.
 exact(conj HNamed(conj HM(conj HNM(conj HSM(conj HB(conj HNB(conj HSB(conj HP(conj HBody(conj
  (source_named_fresh_quantifier_cutoff M true body namedbody witness k shiftedbody point BBody HW HBody HCut HP)BBody)))))))))).
Qed.
Print Assumptions environment_cutoff_member.
Print Assumptions source_environment_coverage_witness_total.
