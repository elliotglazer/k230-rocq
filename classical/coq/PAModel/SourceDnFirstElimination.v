(** Literal AllE and implication elimination for the first guarded Dn step. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions NumericalProofs
 SetFormulaCodes SourceBounded NumericalEnvironments NumericalSourceFull NumericalInstantiation
 NumericalSubstitution NumericalSubstitutionMaps SubstitutionSource SourceInstantiationConstructors SourceDerivedRules
 SourceDnStep SourceDnAssignments SourceDnAssignmentStep.
Unset Implicit Arguments.
Theorem source_full_dn_first_parameter M count pb pc head tb tc d X ab ac fb fc
 body first instance result gb gc gn:
 environment_cons M tb tc count head pb pc(succM M count) ->
 source_dn_assignment M count tb tc d X ab ac ->source_dn_assignment M(succM M count)pb pc d X fb fc ->
 source_bounded M body(succM M(succM M(succM M count))) ->source_dn_successor M body first ->
 numerical_substitution M first ab ac(succM M(succM M count))(zeroM M)instance ->
 numerical_substitution M body fb fc(succM M(succM M(succM M count)))(zeroM M)result ->
 source_full_prv M gb gc gn instance ->
 (forall member,sf_relation M SFMember head X member ->source_full_prv M gb gc gn member) ->
 source_full_prv M gb gc gn result.
Proof.
 intros HT HA HF HB(rot&atom&point&HR&HAtom&HPoint&HAll)HInstance HResult PAll PMember.
 apply(proj1(numerical_substitution_quantifier M true point first ab ac
  (succM M(succM M count))(zeroM M)instance HAll))in HInstance.
 destruct HInstance as(lb&lc&ln&p&HL&HP&HQ).
 apply(proj1(numerical_substitution_binary M SFImpl atom rot point lb lc ln(code_numeral M 1)p
  (or_intror(or_intror eq_refl))HPoint))in HP.
 destruct HP as(am&rotated&HAM&HRSub&HImpl).
 apply(proj1(numerical_substitution_member M(zeroM M)(code_numeral M 2)atom lb lc ln(code_numeral M 1)am HAtom))in HAM.
 destruct HAM as(ax&ay&HX&HY&HAm).
 assert(E:ax=zeroM M)by(exact(proj1(substitution_lift_head M _ _ _ _ _ _ _ _ HL)HX)). subst ax.
 assert(E:ay=succM M X).
 { eapply substitution_lookup_functional;[exact HY|].
   apply(proj2(substitution_lift_tail M _ _ _ _ _ _ _ _ _ HL)).
   exact(source_dn_assignment_one M _ _ _ _ _ _ _ HA). } subst ay.
 destruct(numerical_instantiation_total M p head)as(ip&ib&ic&HHead&HInst).
 apply(proj1(numerical_substitution_binary M SFImpl am rotated p ib ic(code_numeral M 1)(zeroM M)ip
  (or_intror(or_intror eq_refl))HImpl))in HInst.
 destruct HInst as(member&value&HMSub&HValue&HImp).
 apply(proj1(numerical_substitution_member M(zeroM M)(succM M X)am ib ic(code_numeral M 1)(zeroM M)member HAm))in HMSub.
 destruct HMSub as(x&y&HX2&HY2&HM).
 assert(E:x=head)by(eapply substitution_lookup_functional;[exact HX2|exact HHead]). subst x.
 assert(E:y=X)by(eapply substitution_lookup_functional;[exact HY2|apply substitution_singleton_tail]). subst y.
 assert(HSub:numerical_substitution M body fb fc(succM M(succM M(succM M count)))(zeroM M)value).
 { exact(source_dn_assignment_step_substitution M count pb pc head tb tc d X ab ac fb fc lb lc ln ib ic
   body rot rotated value HT HA HF HL HHead HB HR HRSub HValue). }
 assert(E:value=result)by(eapply numerical_substitution_functional;eassumption). subst value.
 assert(HIP:numerical_instantiation M p head ip).
 { exists ib,ic. split;[exact HHead|].
   apply(proj2(numerical_substitution_binary M SFImpl am rotated p ib ic(code_numeral M 1)(zeroM M)ip
    (or_intror(or_intror eq_refl))HImpl)). exists member,result. repeat split;try assumption.
   apply(proj2(numerical_substitution_member M(zeroM M)(succM M X)am ib ic(code_numeral M 1)(zeroM M)member HAm)).
   exists head,X. repeat split;assumption. }
 pose proof(full_source_AllE M gb gc gn p instance head ip
  (source_wf_quantifier_instance M gb gc gn SFAll p instance head ip(or_introl eq_refl)HQ
   (source_full_prv_wellformed M gb gc gn instance PAll)HIP)PAll HQ HIP)as PImp.
 exact(source_full_modus_ponens M gb gc gn member result ip HImp PImp(PMember member HM)).
Qed.
Print Assumptions source_full_dn_first_parameter.
