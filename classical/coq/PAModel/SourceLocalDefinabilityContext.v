(** One genuine closed ZFR context supports all fixed local-definability
    laws at every model-valued role assignment. It is constructed once,
    before choosing any eigenvariables or matrix-specific witnesses. *)
From PAModel Require Import Model CodeExpressions SetFormulaCodes SourceBounded NumericalSourceFull
 SourceLocalDefinabilityFixed SourceClosureTernaryFixed SourceClosureCarrierFixed SourceProjectionOperationFixed
 SourceFiniteParameterClosedContext SourceParameterIdentityCalibration SourceFiniteNameParameters SourceFiniteParameters
 SourceFiniteProofContexts SourceDescriptorProvability SourceSetTheoryDescriptors SourceZFRProvability.
From Stdlib Require Import Lists.List Lia.
Import ListNotations.
Unset Implicit Arguments.
Definition source_local_fixed_formula tag:sf_form:=match tag with
 |0=>source_local_def_exists_law|1=>source_local_def_unpack_law|2=>source_local_L_def_member_law
 |3=>source_local_selection_operation_law|4=>source_projection_extension_exists
 |5=>source_closure_ternary_law 5|_=>source_closure_carrier_law end.
Definition source_local_fixed_arity tag:=match tag with 0=>1|1=>2|2=>4|3=>5|4=>2|5=>6|_=>3 end.
Definition source_local_fixed_expression tag:=source_parameter_expression
 (source_finite_parameter_names(source_local_fixed_arity tag))(source_local_fixed_formula tag).
Lemma source_local_fixed_numeral_proof M tag:(tag<7)%nat ->
 source_descriptor_provable M ZFRSourceDescriptor(code_numeral M(sf_encode(source_local_fixed_formula tag))).
Proof.
 intro HT. apply(proj2(source_zfr_descriptor_provable M _)).
 destruct tag as[|[|[|[|[|[|[|tag]]]]]]];try lia;cbn[source_local_fixed_formula].
 - apply(source_zfr_local_def_exists M(fun i=>code_numeral M i)).
   exact(source_parameter_identity_calibration M source_local_def_exists_law(source_finite_parameter_names 1)
    (fun i=>code_numeral M i)ltac:(intro i;unfold source_finite_parameter_names;destruct(Nat.ltb i 1);reflexivity)).
 - apply(source_zfr_local_def_unpack M(fun i=>code_numeral M i)).
   exact(source_parameter_identity_calibration M source_local_def_unpack_law(source_finite_parameter_names 2)
    (fun i=>code_numeral M i)ltac:(intro i;unfold source_finite_parameter_names;destruct(Nat.ltb i 2);reflexivity)).
 - apply(source_zfr_local_L_def_member M(fun i=>code_numeral M i)).
   exact(source_parameter_identity_calibration M source_local_L_def_member_law(source_finite_parameter_names 4)
    (fun i=>code_numeral M i)ltac:(intro i;unfold source_finite_parameter_names;destruct(Nat.ltb i 4);reflexivity)).
 - apply(source_zfr_local_selection_operation M(fun i=>code_numeral M i)).
   exact(source_parameter_identity_calibration M source_local_selection_operation_law(source_finite_parameter_names 5)
    (fun i=>code_numeral M i)ltac:(intro i;unfold source_finite_parameter_names;destruct(Nat.ltb i 5);reflexivity)).
 - apply(source_zfr_projection_extension M(fun i=>code_numeral M i)).
   exact(source_parameter_identity_calibration M source_projection_extension_exists(source_finite_parameter_names 2)
    (fun i=>code_numeral M i)ltac:(intro i;unfold source_finite_parameter_names;destruct(Nat.ltb i 2);reflexivity)).
 - apply(source_zfr_closure_ternary M 5(fun i=>code_numeral M i));[lia|].
   exact(source_parameter_identity_calibration M(source_closure_ternary_law 5)(source_finite_parameter_names 6)
    (fun i=>code_numeral M i)ltac:(intro i;unfold source_finite_parameter_names;destruct(Nat.ltb i 6);reflexivity)).
 - apply(source_zfr_closure_carrier M(fun i=>code_numeral M i)).
   exact(source_parameter_identity_calibration M source_closure_carrier_law(source_finite_parameter_names 3)
    (fun i=>code_numeral M i)ltac:(intro i;unfold source_finite_parameter_names;destruct(Nat.ltb i 3);reflexivity)).
Qed.
Definition source_local_fixed_context M b c n:=source_zfr_context M b c n /\
 forall tag,(tag<7)%nat ->source_full_prv M b c n(code_numeral M(sf_encode(source_local_fixed_formula tag))).
Theorem source_local_fixed_context_total M:exists b c n,source_local_fixed_context M b c n.
Proof.
 set(forms:=List.map(fun tag=>code_numeral M(sf_encode(source_local_fixed_formula tag)))(List.seq 0 7)).
 assert(HP:forall f,In f forms ->source_descriptor_provable M ZFRSourceDescriptor f).
 { intros f HF. apply List.in_map_iff in HF. destruct HF as(tag&<-&HT).
   apply source_local_fixed_numeral_proof. apply List.in_seq in HT. lia. }
 destruct(source_descriptor_finite_common_context M ZFRSourceDescriptor forms HP)as(b&c&n&HC&P).
 exists b,c,n. split;[exact(proj1(source_zfr_descriptor_context M b c n)HC)|].
 intros tag HT. apply P. unfold forms. apply List.in_map_iff. exists tag. split;[reflexivity|]. apply List.in_seq. lia.
Qed.
Theorem source_full_local_fixed_instance M b c n tag rho out:
 source_local_fixed_context M b c n ->(tag<7)%nat ->
 code_relation M rho(source_local_fixed_expression tag)out ->source_full_prv M b c n out.
Proof.
 intros(HC&HP)HT HO.
 exact(source_full_finite_parameter_closed_context M(source_local_fixed_formula tag)(source_local_fixed_arity tag)rho out b c n
  (source_zfr_context_closed M b c n HC)(HP tag HT)HO).
Qed.
Print Assumptions source_local_fixed_numeral_proof.
Print Assumptions source_local_fixed_context_total.
Print Assumptions source_full_local_fixed_instance.
