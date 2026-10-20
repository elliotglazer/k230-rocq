(** The literal RR Replacement profile, with actual syntax transport and AllE. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SourceBounded
 SourcePropositionalTemplates SourcePropositionalRebase SourcePropositionalSubstitution SourceFunctionalityShells
 SourceRecursionPrimitiveRelations SourceRecursionRangeFibre NumericalSubstitutionMaps NumericalSubstitution NumericalRenaming RenamingSubstitution
 NumericalInstantiation SubstitutionSource SourceInstantiationConstructors NumericalContexts NumericalSourceFull SourceTraceBounds SourceQuantifierRules SourceRecursionShiftGraphs.
Unset Implicit Arguments.
Definition source_rec_range_point_template:=SPTAnd(SPTImpl(SPTSlot 0)(SPTSlot 1))(SPTImpl(SPTSlot 1)(SPTSlot 0)).
Definition source_rec_range_point M phi o a N Y v out:=exists member fibre,
 sf_relation M SFMember v Y member /\source_rec_range_fibre M phi o a N v fibre /\
 code_relation M(source_rec_env2 member fibre)(source_prop_expression source_rec_range_point_template)out.
Definition source_rec_range_chart M phi o a N Y out:=exists point,
 source_rec_range_point M phi(succM M o)(succM M a)(succM M N)(succM M Y)(zeroM M)point /\sf_relation M SFAll point(zeroM M)out.
Theorem source_rec_range_point_total M phi o a N Y v:exists out,source_rec_range_point M phi o a N Y v out.
Proof.
 destruct(sf_relation_total M SFMember v Y)as(member&HM).
 destruct(source_rec_range_fibre_total M phi o a N v)as(fibre&HF).
 destruct(code_relation_total M(source_prop_expression source_rec_range_point_template)(source_rec_env2 member fibre))as(out&HO).
 exists out,member,fibre. auto.
Qed.
Theorem source_rec_range_chart_total M phi o a N Y:exists out,source_rec_range_chart M phi o a N Y out.
Proof.
 destruct(source_rec_range_point_total M phi(succM M o)(succM M a)(succM M N)(succM M Y)(zeroM M))as(point&HP).
 destruct(sf_relation_total M SFAll point(zeroM M))as(out&HO). exists out,point. auto.
Qed.
Theorem source_rec_range_point_bounded M phi o a N Y v out k:
 source_bounded M phi(code_numeral M 2) ->coding_lt M o k ->coding_lt M a k ->coding_lt M N k ->coding_lt M Y k ->coding_lt M v k ->
 source_rec_range_point M phi o a N Y v out ->source_bounded M out k.
Proof.
 intros BP BO BA BN BY BV(member&fibre&HM&HF&HO).
 apply(source_prop_template_bound M(source_rec_env2 member fibre)source_rec_range_point_template k);[|exact HO].
 intros[|i];cbn[source_rec_env2].
 - exact(proj2(source_bounded_accept_atom M SFMember v Y member k(or_introl eq_refl)HM)(conj BV BY)).
 - exact(source_rec_range_fibre_bounded M phi o a N v fibre k BP BO BA BN BV HF).
Qed.
Theorem source_rec_range_chart_bounded M phi o a N Y out k:
 source_bounded M phi(code_numeral M 2) ->coding_lt M o k ->coding_lt M a k ->coding_lt M N k ->coding_lt M Y k ->source_rec_range_chart M phi o a N Y out ->source_bounded M out k.
Proof.
 intros BP BO BA BN BY(point&HP&HO). apply(proj2(source_bounded_accept_unary M SFAll point out k(or_introl eq_refl)HO)).
 exact(source_rec_range_point_bounded M phi(succM M o)(succM M a)(succM M N)(succM M Y)(zeroM M)point(succM M k)BP
  (proj2(coding_lt_succ_cancel M o k)BO)(proj2(coding_lt_succ_cancel M a k)BA)(proj2(coding_lt_succ_cancel M N k)BN)(proj2(coding_lt_succ_cancel M Y k)BY)(coding_zero_lt_succ M k)HP).
Qed.
Theorem source_rec_range_point_substitution M phi o a N Y v old o' a' N' Y' v' new rb rc rn base:
 source_bounded M phi(code_numeral M 2) ->source_rec_range_point M phi o a N Y v old ->source_rec_range_point M phi o' a' N' Y' v' new ->
 substitution_lookup M rb rc rn base o o' ->substitution_lookup M rb rc rn base a a' ->substitution_lookup M rb rc rn base N N' ->
 substitution_lookup M rb rc rn base Y Y' ->substitution_lookup M rb rc rn base v v' ->numerical_substitution M old rb rc rn base new.
Proof.
 intros BP(member&fibre&HM&HF&HO)(member'&fibre'&HM'&HF'&HO')HOO HAA HNN HYY HV.
 apply(source_prop_expression_substitution M(source_rec_env2 member fibre)(source_rec_env2 member' fibre')rb rc rn base source_rec_range_point_template);[|exact HO|exact HO'].
 intros[|i];cbn[source_rec_env2].
 - apply(proj2(numerical_substitution_member M v Y member rb rc rn base member' HM)). exists v',Y'. auto.
 - exact(source_rec_range_fibre_substitution M phi o a N v fibre o' a' N' v' fibre' rb rc rn base BP HF HF' HOO HAA HNN HV).
Qed.
Theorem source_rec_range_chart_substitution M phi o a N Y old o' a' N' Y' new rb rc rn base:
 source_bounded M phi(code_numeral M 2) ->source_rec_range_chart M phi o a N Y old ->source_rec_range_chart M phi o' a' N' Y' new ->
 substitution_lookup M rb rc rn base o o' ->substitution_lookup M rb rc rn base a a' ->substitution_lookup M rb rc rn base N N' ->
 substitution_lookup M rb rc rn base Y Y' ->numerical_substitution M old rb rc rn base new.
Proof.
 intros BP(point&HP&HO)(point'&HP'&HO')HOO HAA HNN HYY.
 destruct(substitution_lift_total M rb rc rn base)as(lb&lc&ln&HL).
 apply(proj2(numerical_substitution_quantifier M true point old rb rc rn base new HO)). exists lb,lc,ln,point'. split;[exact HL|]. split;[|exact HO'].
 exact(source_rec_range_point_substitution M phi _ _ _ _ _ point _ _ _ _ _ point' lb lc ln(succM M base)BP HP HP'
  (proj2(proj2 HL)o o' HOO)(proj2(proj2 HL)a a' HAA)(proj2(proj2 HL)N N' HNN)(proj2(proj2 HL)Y Y' HYY)(proj1(proj2 HL))).
Qed.
Theorem source_rec_range_chart_shift M phi o a N Y old new:
 source_bounded M phi(code_numeral M 2) ->source_rec_range_chart M phi o a N Y old ->source_rec_range_chart M phi(succM M o)(succM M a)(succM M N)(succM M Y)new ->source_formula_shift M old new.
Proof.
 intros BP HO HN. apply(proj2(numerical_renaming_substitution M old(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)new)). rewrite Arithmetic.add_zero.
 exact(source_rec_range_chart_substitution M phi o a N Y old(succM M o)(succM M a)(succM M N)(succM M Y)new
  (zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)BP HO HN(source_rec_shift_lookup M o)(source_rec_shift_lookup M a)(source_rec_shift_lookup M N)(source_rec_shift_lookup M Y)).
Qed.
Theorem source_full_rec_range_chart_use M cb cc cn phi o a N Y chart v result:
 source_bounded M phi(code_numeral M 2) ->source_rec_range_chart M phi o a N Y chart ->source_rec_range_point M phi o a N Y v result ->
 source_full_prv M cb cc cn chart ->source_full_prv M cb cc cn result.
Proof.
 intros BP(point&HP&HO)HR PC.
 destruct(substitution_singleton_total M v)as(rb&rc&HHead&_).
 assert(HInst:numerical_instantiation M point v result).
 { exists rb,rc. split;[exact HHead|]. exact(source_rec_range_point_substitution M phi _ _ _ _ _ point o a N Y v result rb rc(code_numeral M 1)(zeroM M)BP HP HR
  (substitution_singleton_tail M rb rc o)(substitution_singleton_tail M rb rc a)(substitution_singleton_tail M rb rc N)(substitution_singleton_tail M rb rc Y)HHead). }
 exact(full_source_AllE M cb cc cn point chart v result
  (source_wf_quantifier_instance M cb cc cn SFAll point chart v result(or_introl eq_refl)HO(source_full_prv_wellformed M cb cc cn chart PC)HInst)PC HO HInst).
Qed.
Theorem source_rec_range_point_shell M phi o a N Y v out:
 source_rec_range_point M phi o a N Y v out ->exists member fibre forward backward,
 sf_relation M SFMember v Y member /\source_rec_range_fibre M phi o a N v fibre /\sf_relation M SFImpl member fibre forward /\
 sf_relation M SFImpl fibre member backward /\sf_relation M SFAnd forward backward out.
Proof.
 intros(member&fibre&HM&HF&HO).
 destruct(sf_relation_total M SFImpl member fibre)as(forward&HForward).
 destruct(sf_relation_total M SFImpl fibre member)as(backward&HBackward).
 destruct(sf_relation_total M SFAnd forward backward)as(target&HTarget).
 assert(HG:code_relation M(source_rec_env2 member fibre)(source_prop_expression source_rec_range_point_template)target).
 { unfold source_rec_range_point_template. cbn[source_prop_expression]. functionality_graph. }
 rewrite(code_relation_functional M _ _ out target HO HG). exists member,fibre,forward,backward. auto.
Qed.
Print Assumptions source_rec_range_point_total.
Print Assumptions source_rec_range_chart_total.
Print Assumptions source_rec_range_point_bounded.
Print Assumptions source_rec_range_chart_bounded.
Print Assumptions source_rec_range_point_substitution.
Print Assumptions source_rec_range_chart_substitution.
Print Assumptions source_rec_range_chart_shift.
Print Assumptions source_full_rec_range_chart_use.
Print Assumptions source_rec_range_point_shell.
