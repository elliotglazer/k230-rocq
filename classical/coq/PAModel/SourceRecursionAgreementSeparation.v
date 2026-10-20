(** The actual fixed Agr Separation certificate has the shared subset graph. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes OldNamedSyntaxBridge OldFullNDSourceBridge
 SourceAgreementSeparationOld SourceAgreementSeparation SourceFiniteParameters SourceFiniteNameParameters SourcePropositionalRebase
 SourceRecursionPrimitiveRelations SourceRecursionAgreementSubset SourceRecursionParameterCalibration SourcePropositionalTemplates
 SetSchemaConstructors SchemaConstructorBounds SourceFunctionalityShells SourceZFRProvability.
From OldZF Require Std_setrec.
Unset Implicit Arguments.
Ltac recursion_subset_graph:=first[assumption|reflexivity|match goal with
 | H:sf_relation ?M ?h ?a ?b ?out |-code_relation ?M ?rho(E_sf ?h ?A ?B)?out =>
   refine(proj2(schema_expression_graph M rho h A B a b out _ _)H);recursion_subset_graph
 end].
Theorem source_rec_agreement_separation_shell M f g N out:
 source_agreement_separation_graph M(source_rec_env3 f g N)out ->exists body,
 source_rec_subset_chart M(succM M f)(succM M g)(succM M N)(zeroM M)body /\sf_relation M SFEx body(zeroM M)out.
Proof.
 intro HO. set(rho:=source_rec_env3 f g N).
 set(names:=source_parameter_up(source_parameter_up(source_finite_parameter_names 3))).
 set(MX:=E_sf SFMember(names 0)(names 1)).
 set(MN:=E_sf SFMember(names 0)(names 4)).
 set(AGR:=source_parameter_expression names(isolated_formula(OldZF.Std_setrec.Agr
  (@OC.var OB.sig_empty 2)(@OC.var OB.sig_empty 3)(@OC.var OB.sig_empty 0)))).
 change(code_relation M rho(E_sf SFEx(E_sf SFAll(E_sf SFAnd(E_sf SFImpl MX(E_sf SFAnd MN AGR))
  (E_sf SFImpl(E_sf SFAnd MN AGR)MX))(CEconst 0))(CEconst 0))out)in HO.
 destruct(schema_expression_split M rho SFEx _ _ out HO)as(body&z0&HBody&HZ&HEx).
 change(z0=zeroM M)in HZ. subst z0.
 destruct(schema_expression_split M rho SFAll _ _ body HBody)as(point&z0&HPoint&HZ&HAll).
 change(z0=zeroM M)in HZ. subst z0.
 assert(N0:code_relation M rho(names 0)(zeroM M))by reflexivity.
 assert(N1:code_relation M rho(names 1)(code_numeral M 1)).
 { exact(source_parameter_up_name M(source_parameter_up(source_finite_parameter_names 3))rho 0(zeroM M)eq_refl). }
 assert(N2:code_relation M rho(names 2)(succM M(succM M f))).
 { apply(source_parameter_up_name M _ rho 1(succM M f)). apply(source_parameter_up_name M _ rho 0 f). reflexivity. }
 assert(N3:code_relation M rho(names 3)(succM M(succM M g))).
 { apply(source_parameter_up_name M _ rho 2(succM M g)). apply(source_parameter_up_name M _ rho 1 g). reflexivity. }
 assert(N4:code_relation M rho(names 4)(succM M(succM M N))).
 { apply(source_parameter_up_name M _ rho 3(succM M N)). apply(source_parameter_up_name M _ rho 2 N). reflexivity. }
 destruct(code_relation_total M MX rho)as(mx&HMX).
 destruct(code_relation_total M MN rho)as(mn&HMN).
 destruct(code_relation_total M AGR rho)as(agr&HAGR).
 pose proof(proj1(schema_expression_graph M rho SFMember _ _ (zeroM M)(code_numeral M 1)mx N0 N1)HMX)as HX.
 pose proof(proj1(schema_expression_graph M rho SFMember _ _ (zeroM M)(succM M(succM M N))mn N0 N4)HMN)as HN.
 pose proof(source_parameter_rec_agreement M names rho 2 3 0 _ _ _ agr N2 N3 N0 HAGR)as HA.
 destruct(sf_relation_total M SFAnd mn agr)as(both&HB).
 destruct(sf_relation_total M SFImpl mx both)as(forward&HF).
 destruct(sf_relation_total M SFImpl both mx)as(backward&HR).
 destruct(sf_relation_total M SFAnd forward backward)as(target&HT).
 assert(HSource:code_relation M rho(E_sf SFAnd(E_sf SFImpl MX(E_sf SFAnd MN AGR))(E_sf SFImpl(E_sf SFAnd MN AGR)MX))target).
 { recursion_subset_graph. }
 pose proof(code_relation_functional M _ rho point target HPoint HSource)as E. subst target.
 exists body. split;[exists point;split;[|exact HAll]|exact HEx].
 exists mx,mn,agr. split;[exact HX|]. split;[exact HN|]. split;[exact HA|].
 unfold source_rec_subset_template. cbn[source_prop_expression]. functionality_graph.
Qed.
Theorem source_zfr_rec_agreement_subset_exists M f g N:exists out body,
 source_rec_subset_chart M(succM M f)(succM M g)(succM M N)(zeroM M)body /\
 sf_relation M SFEx body(zeroM M)out /\source_zfr_provable M out.
Proof.
 destruct(source_zfr_agreement_separation_total M(source_rec_env3 f g N))as(out&HO&PO).
 destruct(source_rec_agreement_separation_shell M f g N out HO)as(body&HB&HE).
 exists out,body. auto.
Qed.
Print Assumptions source_rec_agreement_separation_shell.
Print Assumptions source_zfr_rec_agreement_subset_exists.
