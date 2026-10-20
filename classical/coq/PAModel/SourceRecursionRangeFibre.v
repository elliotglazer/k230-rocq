(** The literal existential fibre of the recursion Replacement range. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SourceBounded
 NumericalSubstitutionMaps NumericalSubstitution NumericalRenaming RenamingSubstitution NumericalInstantiation SubstitutionSource
 SourceQuantifierRules SourceRecursionRangeRelation SourceRecursionShiftGraphs SourceInstantiationConstructors SourceTracePointRules
 NumericalContexts NumericalSourceFull SourceTraceBounds.
Unset Implicit Arguments.
Definition source_rec_range_fibre M phi o a N v out:=exists member rr body,
 sf_relation M SFMember(zeroM M)(succM M N)member /\source_rec_rr M phi(zeroM M)(succM M v)(succM M o)(succM M a)(succM M N)rr /\
 sf_relation M SFAnd member rr body /\sf_relation M SFEx body(zeroM M)out.
Theorem source_rec_range_fibre_total M phi o a N v:exists out,source_rec_range_fibre M phi o a N v out.
Proof.
 destruct(sf_relation_total M SFMember(zeroM M)(succM M N))as(member&HM).
 destruct(source_rec_rr_total M phi(zeroM M)(succM M v)(succM M o)(succM M a)(succM M N))as(rr&HR).
 destruct(sf_relation_total M SFAnd member rr)as(body&HB).
 destruct(sf_relation_total M SFEx body(zeroM M))as(out&HO). exists out,member,rr,body. auto.
Qed.
Theorem source_rec_range_fibre_functional M phi o a N v x y:
 source_rec_range_fibre M phi o a N v x ->source_rec_range_fibre M phi o a N v y ->x=y.
Proof.
 intros(member&rr&body&HM&HR&HB&HX)(member'&rr'&body'&HM'&HR'&HB'&HY).
 pose proof(sf_relation_functional M SFMember(zeroM M)(succM M N)member' member HM' HM)as E. subst member'.
 pose proof(source_rec_rr_functional M phi(zeroM M)(succM M v)(succM M o)(succM M a)(succM M N)rr' rr HR' HR)as E. subst rr'.
 pose proof(sf_relation_functional M SFAnd member rr body' body HB' HB)as E. subst body'.
 exact(sf_relation_functional M SFEx body(zeroM M)x y HX HY).
Qed.
Theorem source_rec_range_fibre_bounded M phi o a N v out k:
 source_bounded M phi(code_numeral M 2) ->coding_lt M o k ->coding_lt M a k ->coding_lt M N k ->coding_lt M v k ->
 source_rec_range_fibre M phi o a N v out ->source_bounded M out k.
Proof.
 intros BP BO BA BN BV(member&rr&body&HM&HR&HB&HO).
 pose proof(proj2(source_bounded_accept_atom M SFMember(zeroM M)(succM M N)member(succM M k)(or_introl eq_refl)HM)
  (conj(coding_zero_lt_succ M k)(proj2(coding_lt_succ_cancel M N k)BN)))as BM.
 pose proof(source_rec_rr_bounded M phi(zeroM M)(succM M v)(succM M o)(succM M a)(succM M N)rr(succM M k)BP(coding_zero_lt_succ M k)
  (proj2(coding_lt_succ_cancel M v k)BV)(proj2(coding_lt_succ_cancel M o k)BO)(proj2(coding_lt_succ_cancel M a k)BA)(proj2(coding_lt_succ_cancel M N k)BN)HR)as BR.
 exact(proj2(source_bounded_accept_unary M SFEx body out k(or_intror eq_refl)HO)(proj2(source_bounded_accept_binary M SFAnd member rr body(succM M k)(or_introl eq_refl)HB)(conj BM BR))).
Qed.
Theorem source_rec_range_fibre_substitution M phi o a N v old o' a' N' v' new rb rc rn base:
 source_bounded M phi(code_numeral M 2) ->source_rec_range_fibre M phi o a N v old ->source_rec_range_fibre M phi o' a' N' v' new ->
 substitution_lookup M rb rc rn base o o' ->substitution_lookup M rb rc rn base a a' ->substitution_lookup M rb rc rn base N N' ->substitution_lookup M rb rc rn base v v' ->
 numerical_substitution M old rb rc rn base new.
Proof.
 intros BP(member&rr&body&HM&HR&HB&HO)(member'&rr'&body'&HM'&HR'&HB'&HO')HOO HAA HNN HV.
 destruct(substitution_lift_total M rb rc rn base)as(lb&lc&ln&HL).
 apply(proj2(numerical_substitution_quantifier M false body old rb rc rn base new HO)). exists lb,lc,ln,body'. split;[exact HL|]. split;[|exact HO'].
 apply(proj2(numerical_substitution_binary M SFAnd member rr body lb lc ln(succM M base)body'(or_introl eq_refl)HB)). exists member',rr'.
 split;[|split;[|exact HB']].
 - apply(proj2(numerical_substitution_member M _ _ member lb lc ln(succM M base)member' HM)). exists(zeroM M),(succM M N'). exact(conj(proj1(proj2 HL))(conj(proj2(proj2 HL)N N' HNN)HM')).
 - exact(source_rec_rr_substitution M phi(zeroM M)(succM M v)(succM M o)(succM M a)(succM M N)rr(zeroM M)(succM M v')(succM M o')(succM M a')(succM M N')rr'
    lb lc ln(succM M base)BP HR HR'(proj1(proj2 HL))(proj2(proj2 HL)v v' HV)(proj2(proj2 HL)o o' HOO)(proj2(proj2 HL)a a' HAA)(proj2(proj2 HL)N N' HNN)).
Qed.
Theorem source_rec_range_fibre_shift M phi o a N v old new:
 source_bounded M phi(code_numeral M 2) ->source_rec_range_fibre M phi o a N v old ->source_rec_range_fibre M phi(succM M o)(succM M a)(succM M N)(succM M v)new ->source_formula_shift M old new.
Proof.
 intros BP HO HN. apply(proj2(numerical_renaming_substitution M old(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)new)). rewrite Arithmetic.add_zero.
 exact(source_rec_range_fibre_substitution M phi o a N v old(succM M o)(succM M a)(succM M N)(succM M v)new
  (zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)BP HO HN(source_rec_shift_lookup M o)(source_rec_shift_lookup M a)(source_rec_shift_lookup M N)(source_rec_shift_lookup M v)).
Qed.
Theorem source_full_rec_range_fibre_intro M cb cc cn phi o a N v z member rr target k:
 source_bounded M phi(code_numeral M 2) ->coding_lt M o k ->coding_lt M a k ->coding_lt M N k ->coding_lt M v k ->context_bounded M cb cc cn k ->
 sf_relation M SFMember z N member ->source_rec_rr M phi z v o a N rr ->source_rec_range_fibre M phi o a N v target ->
 source_full_prv M cb cc cn member ->source_full_prv M cb cc cn rr ->source_full_prv M cb cc cn target.
Proof.
 intros BP BO BA BN BV BC HM HR HT PM PR.
 pose proof(source_rec_range_fibre_bounded M phi o a N v target k BP BO BA BN BV HT)as BT.
 destruct HT as(member0&rr0&body&HM0&HR0&HB0&HEx).
 destruct(sf_relation_total M SFAnd member rr)as(instance&HInstance).
 destruct(substitution_singleton_total M z)as(rb&rc&HHead&_).
 assert(HInstRR:numerical_instantiation M rr0 z rr).
 { exists rb,rc. split;[exact HHead|]. exact(source_rec_rr_substitution M phi(zeroM M)(succM M v)(succM M o)(succM M a)(succM M N)rr0 z v o a N rr
    rb rc(code_numeral M 1)(zeroM M)BP HR0 HR HHead(substitution_singleton_tail M rb rc v)(substitution_singleton_tail M rb rc o)(substitution_singleton_tail M rb rc a)(substitution_singleton_tail M rb rc N)). }
 pose proof(source_instantiation_binary M SFAnd member0 rr0 body z member rr instance(or_introl eq_refl)HB0
  (source_instantiation_head_member M N member0 z member HM0 HM)HInstRR HInstance)as HInst.
 assert(PInstance:source_full_prv M cb cc cn instance).
 { exact(full_source_CI M cb cc cn member rr instance(source_wf_binary M cb cc cn SFAnd member rr instance(or_introl eq_refl)HInstance
  (source_full_prv_wellformed M cb cc cn member PM)(source_full_prv_wellformed M cb cc cn rr PR))PM PR HInstance). }
 exact(full_source_ExI M cb cc cn body target z instance(ex_intro _ k(conj BT BC))PInstance HEx HInst).
Qed.
Print Assumptions source_rec_range_fibre_total.
Print Assumptions source_rec_range_fibre_functional.
Print Assumptions source_rec_range_fibre_bounded.
Print Assumptions source_rec_range_fibre_substitution.
Print Assumptions source_rec_range_fibre_shift.
Print Assumptions source_full_rec_range_fibre_intro.
