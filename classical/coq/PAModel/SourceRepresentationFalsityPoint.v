(** The finite logical base of the falsity representation. It uses only
    the definition of an empty set, with no set-theory axiom. *)
From PAModel Require Import Model CodeExpressions SetFormulaCodes SourceNumeralLift SourceQuantifierRules SetSchemaConstructors
 SourceDefinabilityPrimitives SourceDescriptorProvability SourceDescriptorClosure.
From Undecidability.FOL Require Import Syntax.Facts Deduction.FullNDFacts Sets.minZF.
From Stdlib Require Import Lists.List.
Import ListNotations.
Open Scope minZFsyn.
Set Implicit Arguments.
#[local] Instance representation_point_pc : peirce := class.

Definition representation_empty_shift :sf_form :=subst_form ↑ source_def_empty.
Definition representation_falsity_iff :sf_form :=($0 ∈' $1 → ⊥) ∧(⊥ →$0 ∈' $1).
Definition representation_falsity_point :sf_form :=representation_empty_shift →representation_falsity_iff.
Lemma representation_falsity_point_finite :(@nil sf_form) ⊢representation_falsity_point.
Proof.
 unfold representation_falsity_point,representation_falsity_iff. apply II,CI.
 - assert(HE:List.cons representation_empty_shift List.nil ⊢representation_empty_shift)
    by(apply Ctx;cbn;auto).
   change(List.cons representation_empty_shift List.nil ⊢∀($0 ∈' $2 →⊥))in HE.
   apply(AllE $0)in HE. cbn in HE. exact HE.
 - apply II,Exp,Ctx. cbn. auto.
Qed.
Unset Implicit Arguments.
Lemma representation_empty_shift_graph M :source_formula_shift M
 (code_numeral M(sf_encode source_def_empty))(code_numeral M(sf_encode representation_empty_shift)).
Proof. apply source_formula_numeral_shift. Qed.
Lemma representation_falsity_iff_graph M :code_relation M(fun _=>zeroM M)
 (E_sf_iff(E_sf SFMember(CEconst 0)(CEconst 1))(CEconst 0))
 (code_numeral M(sf_encode representation_falsity_iff)).
Proof. exact(code_relation_numeral M(fun _=>0)%nat
 (E_sf_iff(E_sf SFMember(CEconst 0)(CEconst 1))(CEconst 0))). Qed.
Theorem source_descriptor_representation_falsity_point M T point :
 sf_relation M SFImpl(code_numeral M(sf_encode representation_empty_shift))
  (code_numeral M(sf_encode representation_falsity_iff)) point ->source_descriptor_provable M T point.
Proof.
 intro HP. rewrite(sf_relation_functional M SFImpl _ _ point
  (code_numeral M(sf_encode representation_falsity_point)) HP
  (sf_make_numeral M SFImpl(sf_encode representation_empty_shift)(sf_encode representation_falsity_iff))).
 exact(source_descriptor_provable_from_empty M T _
   (source_full_forward_model_empty M representation_falsity_point representation_falsity_point_finite)).
Qed.
Print Assumptions representation_falsity_point_finite.
Print Assumptions representation_empty_shift_graph.
Print Assumptions representation_falsity_iff_graph.
Print Assumptions source_descriptor_representation_falsity_point.
