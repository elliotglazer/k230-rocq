(** Replacement under ordinary finite hypotheses. Functionality may depend
    on the recursion assumptions; they are retained by the output telescope. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes
  SourceBounded SourceFiniteCutoffShift SchemaRenamingDescriptors SourceFunctionalityShells
  SetSchemaConstructors SourceZFRReplacementUse SourceReplacementContainerSpecialization
  SourceFiniteTelescope SourceZFRFiniteRule SourceZFRProvability SourceDerivedRules
  NumericalSourceFull SourceInstantiationConstructors SourcePropositionalRebase.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.

Theorem source_zfr_replacement_conditional_container M phi count a b c functionality p2 container
    assumptions conditional_f specialized out k:
  source_bounded M phi(succM M(succM M count)) ->
  schema_renaming M RepA phi a ->schema_renaming M RepB phi b ->schema_renaming M RepC phi c ->
  source_functionality_graph M a b functionality ->source_cutoff_shift M 2 phi p2 ->
  code_relation M(source_replacement_container_environment M container p2)
    (E_replacement_container(CEvar 0)(CEvar 1))specialized ->
  (forall f,In f assumptions ->source_bounded M f k) ->source_bounded M specialized k ->
  source_finite_telescope M assumptions functionality conditional_f ->
  source_finite_telescope M assumptions specialized out ->
  source_zfr_provable M conditional_f ->source_zfr_provable M out.
Proof.
  intros HB HA HBB HC HF HP HSpecialized BA BT HCF HO PCF.
  destruct(sf_replacement_constructor_total M a b c)as(raw&HRaw).
  pose proof(source_zfr_replacement_open M phi count a b c raw HB HA HBB HC HRaw)as PRaw.
  destruct(source_replacement_open_split M a b c raw HRaw)as(f&range&HFunctionality&HRange&HImp).
  pose proof(code_relation_functional M _ _ f functionality HFunctionality HF)as E. subst f.
  destruct(source_replacement_container_specialization M phi c range p2(succM M(succM M count))container
    HB HC HRange HP)as(rawbody&actual&HAll&HInst&HActual).
  pose proof(code_relation_functional M(E_replacement_container(CEvar 0)(CEvar 1))
    (source_replacement_container_environment M container p2)actual specialized HActual HSpecialized)as E. subst actual.
  apply(source_zfr_finite_rule M[raw;conditional_f]assumptions specialized out k BA BT HO).
  - intros law[<-|[<-|[]]];assumption.
  - intros cb cc cn BC Laws Premises.
    assert(PF:source_full_prv M cb cc cn functionality).
    { apply(source_full_finite_telescope_apply M assumptions functionality conditional_f HCF cb cc cn);
        [apply Laws;right;now left|exact Premises]. }
    assert(PR:source_full_prv M cb cc cn range).
    { exact(source_full_modus_ponens M cb cc cn functionality range raw HImp(Laws raw(or_introl eq_refl))PF). }
    apply(full_source_AllE M cb cc cn rawbody range container specialized).
    + exact(source_wf_quantifier_instance M cb cc cn SFAll rawbody range container specialized(or_introl eq_refl)
        HAll(source_full_prv_wellformed M cb cc cn range PR)HInst).
    + exact PR.
    + exact HAll.
    + exact HInst.
Qed.
Print Assumptions source_zfr_replacement_conditional_container.
