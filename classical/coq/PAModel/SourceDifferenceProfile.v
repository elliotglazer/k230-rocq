(** Axiom-free logical conversion of the literal Op2/SepOf definition to
    its membership biconditional, at arbitrary internal parameter names. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceFiniteParameters
 SourceFiniteParameterProofs SourceSubsetClosedPoint SourceDescriptorProvability SourceDescriptorClosure
 SchemaConstructorBounds NumericalContexts NumericalSourceFull SourceProofWeakening SourceDerivedRules
 OldNamedSyntaxBridge.
From OldZFC Require Z_cl.
From Undecidability.FOL Require Import Syntax.Facts Deduction.FullNDFacts Sets.minZF.
From Stdlib Require Import Lists.List.
Import ListNotations.
Open Scope minZFsyn.
Set Implicit Arguments.
#[local] Instance difference_point_pc :peirce:=class.
Definition source_difference_operation (x y r:sf_term):sf_form :=
 (∀($0 ∈' r`[↑] →($0 ∈' x`[↑] ∧($0 ∈' y`[↑] →⊥)))) ∧
 (∀($0 ∈' x`[↑] →($0 ∈' y`[↑] →⊥) →$0 ∈' r`[↑])).
Definition source_difference_profile (x y r:sf_term):sf_form :=
 ∀($0 ∈' r`[↑] ↔($0 ∈' x`[↑] ∧($0 ∈' y`[↑] →⊥))).
Definition source_difference_profile_law:sf_form :=
 source_difference_operation $0 $1 $2 →source_difference_profile $0 $1 $2.
Lemma source_difference_profile_finite :(@nil sf_form) ⊢source_difference_profile_law.
Proof.
 unfold source_difference_profile_law,source_difference_profile. apply II,AllI.
 change([source_difference_operation $1 $2 $3] ⊢
   ($0 ∈' $3 ↔($0 ∈' $1 ∧($0 ∈' $2 →⊥)))).
 assert(POp:[source_difference_operation $1 $2 $3] ⊢source_difference_operation $1 $2 $3).
 { apply Ctx. now left. }
 pose proof(CE1 POp)as PF. pose proof(CE2 POp)as PR.
 unfold source_difference_operation in PF,PR.
 apply(AllE $0)in PF,PR. cbn in PF,PR.
 apply CI;[exact PF|]. apply II.
 eapply IE.
 - eapply IE.
   + eapply Weak;[exact PR|]. intros f HF. now right.
   + eapply CE1. apply Ctx. now left.
 - eapply CE2. apply Ctx. now left.
Qed.
Unset Implicit Arguments.
Definition source_difference_operation_expression :=source_parameter_expression source_three_parameter_names
 (source_difference_operation $0 $1 $2).
Definition source_difference_profile_expression :=source_parameter_expression source_three_parameter_names
 (source_difference_profile $0 $1 $2).
Theorem source_descriptor_difference_profile M T rho out :
 code_relation M rho(source_parameter_expression source_three_parameter_names source_difference_profile_law)out ->
 source_descriptor_provable M T out.
Proof.
 intro HO. apply source_descriptor_provable_from_empty.
 exact(source_empty_three_parameter_proof M source_difference_profile_law rho out source_difference_profile_finite HO).
Qed.
Print Assumptions source_difference_profile_finite.
Print Assumptions source_descriptor_difference_profile.


Lemma source_difference_operation_literal :source_difference_operation $0 $1 $2=
 isolated_formula(OldZFC.Z_cl.Op 2(@OC.var OB.sig_empty 0)(@OC.var OB.sig_empty 1)
  (@OC.var OB.sig_empty 1)(@OC.var OB.sig_empty 2)).
Proof. reflexivity. Qed.
Theorem source_full_difference_profile M b c n rho operation profile :
 code_relation M rho source_difference_operation_expression operation ->
 code_relation M rho source_difference_profile_expression profile ->
 source_full_prv M b c n operation ->source_full_prv M b c n profile.
Proof.
 intros HO HP PO. destruct(sf_relation_total M SFImpl operation profile)as(law&HL).
 assert(HLaw:code_relation M rho
  (source_parameter_expression source_three_parameter_names source_difference_profile_law)law).
 { exact(proj2(schema_expression_graph M rho SFImpl _ _ operation profile law HO HP) HL). }
 pose proof(source_empty_three_parameter_proof M source_difference_profile_law rho law source_difference_profile_finite HLaw)as PLaw.
 destruct(source_full_prv_wellformed M b c n operation PO)as(k&_&HC).
 assert(P:source_full_prv M b c n law).
 { apply(source_full_prv_weaken_bounded M(zeroM M)(zeroM M)(zeroM M)b c n law k PLaw);[|exact HC].
   intros f HF. exfalso. exact(context_empty M(zeroM M)(zeroM M)f HF). }
 exact(source_full_modus_ponens M b c n operation profile law HL P PO).
Qed.
Print Assumptions source_difference_operation_literal.
Print Assumptions source_full_difference_profile.
