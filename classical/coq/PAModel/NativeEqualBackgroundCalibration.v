(** Literal calibration of named Empty and one-object Hosting to their
    fixed standard source formulas. Names range over the arbitrary model. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions SetFormulaCodes
  SetCodeDescent SetSchemaConstructors SchemaConstructorBounds ZFCFiniteAxiomTemplates
  SourceBounded SourceNumeralLift SourceFiniteParameters SourceFiniteParameterProofs
  SourceUnaryParameters NumericalRenamingMaps NumericalRenaming NumericalInstantiation
  NumericalContexts NumericalSourceFull SourceInstantiationConstructors RawBinderRenaming
  SourceNamedQuantifierRules NativeEmptyClosure.
From Undecidability.FOL Require Import Syntax.Facts Syntax.Bounded Sets.minZF.
Open Scope minZFsyn.
Unset Implicit Arguments.

Definition source_equal_empty :sf_form :=∃∀($0 ∈' $1 → ⊥).
Definition source_equal_host_body :sf_form :=∃($1 ∈' $0).
Definition source_equal_hosting :sf_form :=∀source_equal_host_body.

Theorem source_named_host_parameter_graph M a private member host :private<>a ->
  sf_relation M SFMember a private member ->source_named_quantifier M false private member host ->
  code_relation M (fun _=>a)
    (source_parameter_expression source_three_parameter_names source_equal_host_body) host.
Proof.
  intros HNe HM (rb&rc&body&HMap&HR&HEx).
  destruct(proj1(numerical_renaming_member M a private member rb rc
    (succM M private)(succM M(zeroM M)) body HM) HR) as(u&v&HU&HV&HBody).
  apply(proj1(HMap a u)) in HU. apply(proj1(HMap private v)) in HV.
  destruct HU as[[E _]|[_ EU]];[congruence|].
  destruct HV as[[_ EV]|[NE _]];[|contradiction]. subst u v.
  unfold source_equal_host_body. cbn[source_parameter_expression source_parameter_up source_three_parameter_names].
  assert (HName:code_relation M (fun _=>a)(CEadd(CEvar 0)(CEconst 1))(succM M a)).
  { exists a,(code_numeral M 1). split;[reflexivity|]. split;[reflexivity|].
    apply Arithmetic.succ_as_add. }
  assert(HBodyGraph:code_relation M (fun _=>a)
    (E_sf SFMember (CEadd(CEvar 0)(CEconst 1))(CEconst 0)) body).
  { exact(proj2(schema_expression_graph M (fun _=>a) SFMember _ (CEconst 0)
      (succM M a)(zeroM M) body HName eq_refl) HBody). }
  exact(proj2(schema_expression_graph M (fun _=>a) SFEx _ (CEconst 0) body (zeroM M) host HBodyGraph eq_refl) HEx).
Qed.

Theorem source_full_hosting_named_instance M b c n a private member host :private<>a ->
  sf_relation M SFMember a private member ->source_named_quantifier M false private member host ->
  source_full_prv M b c n (code_numeral M(sf_encode source_equal_hosting)) ->source_full_prv M b c n host.
Proof.
  intros HNe HM HQ HP.
  pose proof(source_named_host_parameter_graph M a private member host HNe HM HQ) as HGraph.
  assert (HB:bounded 1 source_equal_host_body).
  { apply set_formula_boundb_sound. vm_compute. reflexivity. }
  pose proof(source_unary_parameter_instantiation M source_equal_host_body source_three_parameter_names
    (fun _=>a) a host HB eq_refl HGraph) as HI.
  pose proof(sf_make_numeral M SFAll (sf_encode source_equal_host_body) 0) as HAll.
  apply(full_source_AllE M b c n (code_numeral M(sf_encode source_equal_host_body))
    (code_numeral M(sf_encode source_equal_hosting)) a host);[|exact HP|exact HAll|exact HI].
  exact(source_wf_quantifier_instance M b c n SFAll _ _ a host (or_introl eq_refl)
    HAll (source_full_prv_wellformed M b c n _ HP) HI).
Qed.

Theorem source_named_empty_exists_code M a private empty emptyExists :private<>a ->
  source_named_empty M a private empty ->source_named_quantifier M false private empty emptyExists ->
  emptyExists=code_numeral M(sf_encode source_equal_empty).
Proof.
  intros HNe(member&negative&HM&HN&(rb&rc&negbody&HMap&HR&HAll))
    (sb&sc&allbody&SMap&SBody&HEx).
  destruct(proj1(numerical_renaming_binary M SFImpl member (zeroM M) negative rb rc
    (succM M a)(succM M(zeroM M)) negbody (or_intror(or_intror eq_refl)) HN) HR)
    as(rmember&bad&HRM&HRBad&HNegBody).
  apply(proj1(numerical_renaming_invalid M (zeroM M) rb rc (succM M a)
    (succM M(zeroM M)) bad (or_introl eq_refl))) in HRBad. subst bad.
  destruct(proj1(numerical_renaming_member M a private member rb rc
    (succM M a)(succM M(zeroM M)) rmember HM) HRM) as(u&v&HU&HV&HRMember).
  apply(proj1(HMap a u)) in HU. apply(proj1(HMap private v)) in HV.
  destruct HU as[[_ EU]|[NE _]];[|contradiction].
  destruct HV as[[E _]|[_ EV]];[congruence|]. subst u v.
  destruct(proj1(numerical_renaming_quantifier M true negbody empty sb sc
    (succM M private)(succM M(zeroM M)) allbody HAll) SBody)
    as(lb&lc&ln&newneg&HL&HNewNeg&HNewAll).
  destruct(proj1(numerical_renaming_binary M SFImpl rmember (zeroM M) negbody lb lc ln
    (succM M(zeroM M)) newneg (or_intror(or_intror eq_refl)) HNegBody) HNewNeg)
    as(newmem&newbad&HNewMem&HNewBad&HNewImpl).
  apply(proj1(numerical_renaming_invalid M (zeroM M) lb lc ln
    (succM M(zeroM M)) newbad (or_introl eq_refl))) in HNewBad. subst newbad.
  destruct(proj1(numerical_renaming_member M (zeroM M)(succM M private) rmember lb lc ln
    (succM M(zeroM M)) newmem HRMember) HNewMem) as(z&w&HZ&HW&HMember01).
  apply(proj1(renaming_lift_head M sb sc _ _ lb lc ln z HL)) in HZ. subst z.
  destruct(renaming_lift_tail_inv M sb sc _ _ lb lc ln private w HL HW) as(v&HV&EW).
  apply(proj1(SMap private v)) in HV. destruct HV as[[_ EV]|[NE _]];[|contradiction].
  subst v w.
  rewrite(sf_relation_functional M SFMember (zeroM M)(code_numeral M 1) newmem
    (code_numeral M(sf_make SFMember 0 1)) HMember01 (sf_make_numeral M SFMember 0 1)) in HNewImpl.
  rewrite(sf_relation_functional M SFImpl (code_numeral M(sf_make SFMember 0 1))(zeroM M)
    newneg (code_numeral M(sf_make SFImpl (sf_make SFMember 0 1) 0)) HNewImpl
    (sf_make_numeral M SFImpl (sf_make SFMember 0 1) 0)) in HNewAll.
  rewrite(sf_relation_functional M SFAll (code_numeral M(sf_make SFImpl (sf_make SFMember 0 1) 0))
    (zeroM M) allbody (code_numeral M(sf_make SFAll (sf_make SFImpl (sf_make SFMember 0 1) 0) 0))
    HNewAll (sf_make_numeral M SFAll (sf_make SFImpl (sf_make SFMember 0 1) 0) 0)) in HEx.
  exact(sf_relation_functional M SFEx _ _ emptyExists (code_numeral M(sf_encode source_equal_empty))
    HEx (sf_make_numeral M SFEx (sf_make SFAll (sf_make SFImpl (sf_make SFMember 0 1) 0) 0) 0)).
Qed.

Print Assumptions source_full_hosting_named_instance.
Print Assumptions source_named_empty_exists_code.
