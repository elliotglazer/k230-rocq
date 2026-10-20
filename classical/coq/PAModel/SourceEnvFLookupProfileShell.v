(** Exact fixed-role head/tail profile laws for the two-witness EnvF step. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SetSchemaConstructors SchemaConstructorBounds
 OldNamedSyntaxBridge SourceFiniteParameters SourceFiniteNameParameters SourceEnvFLookupFixedRoles
 SourceEnvFLookupProfile SourceEnvFLookupProfileCalibration SourceEnvFLookupProfileOld SourceEnvFLookupProfileFixed
 SourceEnvFDomainWitnessFixed SourceZFRProvability SourceAtomLookupOld.
Unset Implicit Arguments.
Local Opaque code_numeral source_env_profile.
Theorem source_zfr_env_lookup_profile_head_shell M profile:
 source_env_profile M(code_numeral M 3)(code_numeral M 2)(code_numeral M 4)profile ->
 exists equal inner tail law,
 sf_relation M SFEqual(code_numeral M 2)(zeroM M)equal /\
 sf_relation M SFImpl equal profile inner /\
 sf_relation M SFImpl(code_numeral M(sf_encode ew_extension143))inner tail /\
 sf_relation M SFImpl(ew_domain_code M 1 0)tail law /\source_zfr_provable M law.
Proof.
 intro HP. set(rho:=lookup_fixed_roles M(zeroM M)).
 set(names:=source_finite_parameter_names 6).
 destruct(code_relation_total M(source_parameter_expression names lookup_domain_source)rho)as(d&HD).
 pose proof(source_parameter_lookup_fixed M(zeroM M)lookup_domain_source d lookup_domain_source_bound HD)as ED.
 rewrite lookup_domain_source_shape in ED. change(d=ew_domain_code M 1 0)in ED. subst d.
 destruct(code_relation_total M(source_parameter_expression names lookup_extension_source)rho)as(e&HE).
 pose proof(source_parameter_lookup_fixed M(zeroM M)lookup_extension_source e lookup_extension_source_bound HE)as EE.
 rewrite lookup_extension_source_shape in EE. subst e.
 destruct(code_relation_total M(source_parameter_expression names(isolated_formula(old_atom_app_profile
  (@OC.var OB.sig_empty 3)(@OC.var OB.sig_empty 4)(@OC.var OB.sig_empty 2))))rho)as(p&HG).
 pose proof(source_parameter_env_profile_instance M names rho 3 4 2(code_numeral M 3)(code_numeral M 2)(code_numeral M 4)p
  eq_refl eq_refl eq_refl HG)as HProfile.
 assert(E:p=profile)by(eapply source_env_profile_functional;eassumption). subst p.
 destruct(sf_relation_total M SFEqual(code_numeral M 2)(zeroM M))as(equal&HEq).
 destruct(sf_relation_total M SFImpl equal profile)as(inner&HInner).
 destruct(sf_relation_total M SFImpl(code_numeral M(sf_encode ew_extension143))inner)as(tail&HTail).
 destruct(sf_relation_total M SFImpl(ew_domain_code M 1 0)tail)as(law&HLaw).
 exists equal,inner,tail,law. refine(conj HEq(conj HInner(conj HTail(conj HLaw _)))).
 apply(source_zfr_env_lookup_profile_named M true rho law).
 change(code_relation M rho(E_sf SFImpl(source_parameter_expression names lookup_domain_source)
  (E_sf SFImpl(source_parameter_expression names lookup_extension_source)
   (E_sf SFImpl(E_sf SFEqual(names 4)(names 1))
    (source_parameter_expression names(isolated_formula(old_atom_app_profile
     (@OC.var OB.sig_empty 3)(@OC.var OB.sig_empty 4)(@OC.var OB.sig_empty 2)))))))law).
 assert(GEq:code_relation M rho(E_sf SFEqual(names 4)(names 1))equal).
 { exact(proj2(schema_expression_graph M rho SFEqual(names 4)(names 1)(code_numeral M 2)(zeroM M)equal eq_refl eq_refl)HEq). }
 exact(proj2(schema_expression_graph M rho SFImpl _ _(ew_domain_code M 1 0)tail law HD
  (proj2(schema_expression_graph M rho SFImpl _ _(code_numeral M(sf_encode ew_extension143))inner tail HE
   (proj2(schema_expression_graph M rho SFImpl _ _ equal profile inner GEq HG)HInner))HTail))HLaw).
Qed.
Print Assumptions source_zfr_env_lookup_profile_head_shell.

Theorem source_zfr_env_lookup_profile_tail_shell M value old new:
 source_env_profile M(code_numeral M 1)(code_numeral M 2)value old ->
 source_env_profile M(code_numeral M 3)(code_numeral M 2)value new ->
 exists equal neg last inner tail law,
 sf_relation M SFEqual(code_numeral M 2)(zeroM M)equal /\
 sf_relation M SFImpl equal(zeroM M)neg /\sf_relation M SFImpl old new last /\
 sf_relation M SFImpl neg last inner /\
 sf_relation M SFImpl(code_numeral M(sf_encode ew_extension143))inner tail /\
 sf_relation M SFImpl(ew_domain_code M 1 0)tail law /\source_zfr_provable M law.
Proof.
 intros HOld HNew. set(rho:=lookup_fixed_roles M value).
 set(names:=source_finite_parameter_names 6).
 destruct(code_relation_total M(source_parameter_expression names lookup_domain_source)rho)as(d&HD).
 pose proof(source_parameter_lookup_fixed M value lookup_domain_source d lookup_domain_source_bound HD)as ED.
 rewrite lookup_domain_source_shape in ED. change(d=ew_domain_code M 1 0)in ED. subst d.
 destruct(code_relation_total M(source_parameter_expression names lookup_extension_source)rho)as(e&HE).
 pose proof(source_parameter_lookup_fixed M value lookup_extension_source e lookup_extension_source_bound HE)as EE.
 rewrite lookup_extension_source_shape in EE. subst e.
 destruct(code_relation_total M(source_parameter_expression names(isolated_formula(old_atom_app_profile
  (@OC.var OB.sig_empty 0)(@OC.var OB.sig_empty 4)(@OC.var OB.sig_empty 5))))rho)as(p&GP).
 pose proof(source_parameter_env_profile_instance M names rho 0 4 5(code_numeral M 1)(code_numeral M 2)value p
  eq_refl eq_refl eq_refl GP)as HP.
 assert(E:p=old)by(eapply source_env_profile_functional;eassumption). subst p.
 destruct(code_relation_total M(source_parameter_expression names(isolated_formula(old_atom_app_profile
  (@OC.var OB.sig_empty 3)(@OC.var OB.sig_empty 4)(@OC.var OB.sig_empty 5))))rho)as(q&GQ).
 pose proof(source_parameter_env_profile_instance M names rho 3 4 5(code_numeral M 3)(code_numeral M 2)value q
  eq_refl eq_refl eq_refl GQ)as HQ.
 assert(E:q=new)by(eapply source_env_profile_functional;eassumption). subst q.
 destruct(sf_relation_total M SFEqual(code_numeral M 2)(zeroM M))as(equal&HEq).
 destruct(sf_relation_total M SFImpl equal(zeroM M))as(neg&HNeg).
 destruct(sf_relation_total M SFImpl old new)as(last&HLast).
 destruct(sf_relation_total M SFImpl neg last)as(inner&HInner).
 destruct(sf_relation_total M SFImpl(code_numeral M(sf_encode ew_extension143))inner)as(tail&HTail).
 destruct(sf_relation_total M SFImpl(ew_domain_code M 1 0)tail)as(law&HLaw).
 exists equal,neg,last,inner,tail,law.
 refine(conj HEq(conj HNeg(conj HLast(conj HInner(conj HTail(conj HLaw _)))))).
 apply(source_zfr_env_lookup_profile_named M false rho law).
 change(code_relation M rho(E_sf SFImpl(source_parameter_expression names lookup_domain_source)
  (E_sf SFImpl(source_parameter_expression names lookup_extension_source)
   (E_sf SFImpl(E_sf SFImpl(E_sf SFEqual(names 4)(names 1))(CEconst 0))
    (E_sf SFImpl(source_parameter_expression names(isolated_formula(old_atom_app_profile
     (@OC.var OB.sig_empty 0)(@OC.var OB.sig_empty 4)(@OC.var OB.sig_empty 5))))
     (source_parameter_expression names(isolated_formula(old_atom_app_profile
      (@OC.var OB.sig_empty 3)(@OC.var OB.sig_empty 4)(@OC.var OB.sig_empty 5))))))))law).
 assert(GEq:code_relation M rho(E_sf SFEqual(names 4)(names 1))equal).
 { exact(proj2(schema_expression_graph M rho SFEqual(names 4)(names 1)(code_numeral M 2)(zeroM M)equal eq_refl eq_refl)HEq). }
 assert(GNeg:code_relation M rho(E_sf SFImpl(E_sf SFEqual(names 4)(names 1))(CEconst 0))neg).
 { exact(proj2(schema_expression_graph M rho SFImpl(E_sf SFEqual(names 4)(names 1))(CEconst 0)
    equal(zeroM M)neg GEq eq_refl)HNeg). }
 exact(proj2(schema_expression_graph M rho SFImpl _ _(ew_domain_code M 1 0)tail law HD
  (proj2(schema_expression_graph M rho SFImpl _ _(code_numeral M(sf_encode ew_extension143))inner tail HE
   (proj2(schema_expression_graph M rho SFImpl _ _ neg last inner GNeg
    (proj2(schema_expression_graph M rho SFImpl _ _ old new last GP GQ)HLast))HInner))HTail))HLaw).
Qed.
Print Assumptions source_zfr_env_lookup_profile_tail_shell.
