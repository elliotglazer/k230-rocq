(** Exact member/NumF pair syntax, binder shifts and witness instantiations. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SourceNumeralLift
 SourceBounded SourceBoundMonotone SourceQuantifierRules NumericalSubstitutionMaps NumericalSubstitution
 NumericalInstantiation SubstitutionSource SourceInstantiationConstructors SourceDefinabilityLogicalStep
 SourceFiniteCutoffShift SourceCutoffQuantifiers SourceCutoffPropositional SourcePropositionalTemplates.
Unset Implicit Arguments.
Definition source_numf_closure_member M r :=code_numeral M(sf_make SFMember 0 r).
Definition source_numf_member_shell M f r body ex :=
 sf_relation M SFAnd f(source_numf_closure_member M r)body /\sf_relation M SFEx body(zeroM M)ex.
Theorem source_numf_member_shell_total M f r :exists body ex,source_numf_member_shell M f r body ex.
Proof.
 destruct(sf_relation_total M SFAnd f(source_numf_closure_member M r))as(body&HB).
 destruct(sf_relation_total M SFEx body(zeroM M))as(ex&HE). exists body,ex. exact(conj HB HE).
Qed.
Lemma source_numf_closure_member_graph M r :sf_relation M SFMember(zeroM M)(code_numeral M r)(source_numf_closure_member M r).
Proof. exact(sf_make_numeral M SFMember 0 r). Qed.
Lemma source_numf_closure_member_cutoff M r :source_cutoff_shift M 1
 (source_numf_closure_member M(S r))(source_numf_closure_member M(S(S r))).
Proof.
 destruct(source_cutoff_shift_map_total M 1)as(b&c&n&HM). exists b,c,n. split;[exact HM|].
 apply(proj2(numerical_substitution_member M _ _ _ b c n(code_numeral M 2)_
  (source_numf_closure_member_graph M(S r)))).
 exists(zeroM M),(code_numeral M(S(S r))). split.
 - exact(source_cutoff_shift_map_fixed_lookup M 1 b c n HM 0).
 - split;[exact(source_cutoff_shift_map_fixed_lookup M 1 b c n HM(S r))|apply source_numf_closure_member_graph].
Qed.
Lemma source_numf_closure_member_instance M r :numerical_instantiation M
 (source_numf_closure_member M(S r))(zeroM M)(source_numf_closure_member M r).
Proof.
 destruct(substitution_singleton_total M(zeroM M))as(b&c&HH&HT). exists b,c. split;[exact HH|].
 apply(proj2(numerical_substitution_member M _ _ _ b c(code_numeral M 1)(zeroM M)_
  (source_numf_closure_member_graph M(S r)))).
 exists(zeroM M),(code_numeral M r). split;[exact HH|].
 split;[apply substitution_singleton_tail|apply source_numf_closure_member_graph].
Qed.
Theorem source_numf_member_body_instance M f r body other :
 source_bounded M f(code_numeral M 1) ->
 sf_relation M SFAnd f(source_numf_closure_member M(S r))body ->
 sf_relation M SFAnd f(source_numf_closure_member M r)other ->numerical_instantiation M body(zeroM M)other.
Proof.
 intros HF HB HO. exact(source_instantiation_binary M SFAnd f _ body(zeroM M)f _ other
  (or_introl eq_refl) HB(source_unit_instantiation_self M f HF)(source_numf_closure_member_instance M r)HO).
Qed.
Theorem source_numf_member_exists_shift M f r body ex other nex :
 source_bounded M f(code_numeral M 1) ->source_numf_member_shell M f(S r)body ex ->
 source_numf_member_shell M f(S(S r))other nex ->source_formula_shift M ex nex.
Proof.
 intros HF(HB&HE)(HO&HN). apply source_cutoff_zero_is_shift.
 apply(source_cutoff_quantifier_join M 0 false body other ex nex HE HN).
 set(env:=fun idx:nat=>match idx with 0=>f|_=>source_numf_closure_member M(S r)end).
 set(nextenv:=fun idx:nat=>match idx with 0=>f|_=>source_numf_closure_member M(S(S r))end).
 apply(source_cutoff_shift_propositional M 1 env nextenv(SPTAnd(SPTSlot 0)(SPTSlot 1))body other).
 - intros[|idx];cbn[env nextenv].
   + exact(source_cutoff_shift_fixes_domain M 0 f HF).
   + apply source_numf_closure_member_cutoff.
 - eapply source_prop_template_join;[reflexivity|reflexivity|exact HB].
 - eapply source_prop_template_join;[reflexivity|reflexivity|exact HO].
Qed.
Theorem source_numf_closure_member_bounded M r k :coding_lt M(zeroM M) k ->coding_lt M(code_numeral M r)k ->
 source_bounded M(source_numf_closure_member M r)k.
Proof.
 intros HZ HR. exact(proj2(source_bounded_accept_atom M SFMember _ _ _ k(or_introl eq_refl)
  (source_numf_closure_member_graph M r))(conj HZ HR)).
Qed.
Print Assumptions source_numf_member_body_instance.
Print Assumptions source_numf_member_exists_shift.
