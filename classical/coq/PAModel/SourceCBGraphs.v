(** Determinacy and construction of the literal CB ordinal-collection
    hypotheses. All witnesses are numerical syntax, not proof assumptions. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded
  NumericalRenaming NumericalInstantiation SourceCBTotality SourceCBMonotoneMaps SourceCBMonotoneCollapse
  SourceCBMonotonicity SourceOrdinalPredicate SourceOrdinalMonotoneUse SourcePropositionalTemplates
  SourceOrdinalCollectionActual.
Unset Implicit Arguments.
Local Opaque source_ordinal_predicate_code.

Theorem source_cb_totality_functional M q a b:
  source_cb_totality_graph M q a ->source_cb_totality_graph M q b ->a=b.
Proof.
  intros(ba&ea&ga&pa&HBA&HEA&HGA&HPA&HAA)(bb&eb&gb&pb&HBB&HEB&HGB&HPB&HAB).
  pose proof(sf_relation_functional M SFAnd(source_ordinal_predicate_code M)q ba bb HBA HBB) as E. subst bb.
  pose proof(sf_relation_functional M SFEx ba(zeroM M)ea eb HEA HEB) as E. subst eb.
  pose proof(sf_relation_functional M SFMember(zeroM M)(code_numeral M 1)ga gb HGA HGB) as E. subst gb.
  pose proof(sf_relation_functional M SFImpl ga ea pa pb HPA HPB) as E. subst pb.
  exact(sf_relation_functional M SFAll pa(zeroM M)a b HAA HAB).
Qed.

Theorem source_cb_monotonicity_functional M q a b:
  source_cb_monotonicity_graph M q a ->source_cb_monotonicity_graph M q b ->a=b.
Proof.
  intros(la&ra&oa&sa&pa&ia&ma&HLA&HRA&HOA&HSA&HPA&HIA&HMA&HAA)
    (lb&rb&ob&sb&pb&ib&mb&HLB&HRB&HOB&HSB&HPB&HIB&HMB&HAB).
  pose proof(numerical_renaming_functional M q _ _ _ _ la lb HLA HLB) as E. subst lb.
  pose proof(numerical_renaming_functional M q _ _ _ _ ra rb HRA HRB) as E. subst rb.
  pose proof(numerical_instantiation_functional M(source_ordinal_predicate_code M)(code_numeral M 1)
    oa ob HOA HOB) as E. subst ob.
  pose proof(source_cb_subset_functional M(code_numeral M 1)(zeroM M)sa sb HSA HSB) as E. subst sb.
  pose proof(code_relation_functional M(source_prop_expression source_oc_mono_template)
    (source_oc_mono_environment oa(source_ordinal_predicate_code M)sa la ra)pa pb HPA HPB) as E. subst pb.
  pose proof(sf_relation_functional M SFAll pa(zeroM M)ia ib HIA HIB) as E. subst ib.
  pose proof(sf_relation_functional M SFAll ia(zeroM M)ma mb HMA HMB) as E. subst mb.
  exact(sf_relation_functional M SFAll ma(zeroM M)a b HAA HAB).
Qed.

Theorem source_cb_monotonicity_total M q k:
  source_bounded M q k ->exists out,source_cb_monotonicity_graph M q out.
Proof.
  intro HB. destruct(source_oc_initial_monotonicity_total M q) as(old&HO).
  destruct(numerical_instantiation_total M old(zeroM M)) as(out&HOut).
  exists out. exact(source_cb_initial_monotonicity_instance M q old out k HB HO HOut).
Qed.

Print Assumptions source_cb_totality_functional.
Print Assumptions source_cb_monotonicity_functional.
Print Assumptions source_cb_monotonicity_total.
