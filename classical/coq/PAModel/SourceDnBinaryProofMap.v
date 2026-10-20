(** Internally many Dn steps preserve actual two-premise source proofs.
    The induction property is itself expressed by a PA formula. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions NumericalProofs SetFormulaCodes
 SourceBounded SourceDn SourceDnBounds SourceDnBinaryProofStep SourceDescriptorProvability.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.

Definition source_dn_binary_proof_at M T count :=forall a b c outA outB outC k bc point targetbc result,
 source_bounded M a(addM M count(succM M(succM M k))) ->
 source_bounded M b(addM M count(succM M(succM M k))) ->
 source_bounded M c(addM M count(succM M(succM M k))) ->
 source_dn M count a outA ->source_dn M count b outB ->source_dn M count c outC ->
 sf_relation M SFImpl b c bc ->sf_relation M SFImpl a bc point ->
 sf_relation M SFImpl outB outC targetbc ->sf_relation M SFImpl outA targetbc result ->
 source_descriptor_provable M T point ->source_descriptor_provable M T result.
Definition source_dn_binary_proof_formula T :form :=∀∀∀∀∀∀∀∀∀∀∀(
 source_bounded_accept_formula $10($11 ⊕ σ(σ $4)) →
 source_bounded_accept_formula $9($11 ⊕ σ(σ $4)) →
 source_bounded_accept_formula $8($11 ⊕ σ(σ $4)) →
 source_dn_formula $11 $10 $7 →source_dn_formula $11 $9 $6 →source_dn_formula $11 $8 $5 →
 sf_formula SFImpl $9 $8 $3 →sf_formula SFImpl $10 $3 $2 →
 sf_formula SFImpl $6 $5 $1 →sf_formula SFImpl $7 $1 $0 →
 source_descriptor_provable_formula T $2 →source_descriptor_provable_formula T $0).
Local Opaque holds source_bounded_accept_formula source_dn_formula sf_formula source_descriptor_provable_formula.
Lemma source_dn_binary_proof_definable M T :Definable1 M(source_dn_binary_proof_at M T).
Proof.
 exists(source_dn_binary_proof_formula T),(fun _=>zeroM M). intro count.
 unfold source_dn_binary_proof_formula,source_dn_binary_proof_at.
 repeat setoid_rewrite holds_all. repeat setoid_rewrite holds_imp.
 setoid_rewrite source_bounded_accept_formula_correct. setoid_rewrite source_dn_formula_correct.
 setoid_rewrite sf_formula_correct. setoid_rewrite source_descriptor_provable_formula_correct. reflexivity.
Qed.
Theorem source_descriptor_dn_binary_map M T count :source_dn_binary_proof_at M T count.
Proof.
 revert count. apply(definable_induction M(source_dn_binary_proof_at M T)(source_dn_binary_proof_definable M T)).
 - intros a b c outA outB outC k bc point targetbc result BA BB BC HDA HDB HDC HBC HP HTBC HResult PP.
   apply source_dn_zero in HDA. apply source_dn_zero in HDB. apply source_dn_zero in HDC.
   subst outA outB outC.
   assert(targetbc=bc)by(eapply sf_relation_functional;eassumption). subst targetbc.
   now rewrite(sf_relation_functional M SFImpl a bc result point HResult HP).
 - intros count IH a b c outA outB outC k bc point targetbc result BA BB BC HDA HDB HDC HBC HP HTBC HResult PP.
   apply source_dn_succ in HDA. apply source_dn_succ in HDB. apply source_dn_succ in HDC.
   destruct HDA as(prevA&HDA&HSA),HDB as(prevB&HDB&HSB),HDC as(prevC&HDC&HSC).
   assert(E:addM M(succM M count)(succM M(succM M k))=
     addM M count(succM M(succM M(succM M k)))).
   { rewrite Arithmetic.add_succ,(Arithmetic.add_comm M count(succM M(succM M(succM M k)))),
      Arithmetic.add_succ,(Arithmetic.add_comm M(succM M(succM M k)) count). reflexivity. }
   rewrite E in BA,BB,BC.
   destruct(sf_relation_total M SFImpl prevB prevC)as(previousBC&HPreviousBC).
   destruct(sf_relation_total M SFImpl prevA previousBC)as(previousPoint&HPreviousPoint).
   pose proof(IH a b c prevA prevB prevC(succM M k) bc point previousBC previousPoint BA BB BC
     HDA HDB HDC HBC HP HPreviousBC HPreviousPoint PP)as PPrevious.
   exact(source_descriptor_dn_successor_binary_map M T prevA prevB prevC outA outB outC
     previousBC previousPoint targetbc result k
     (source_dn_bounded M count a prevA(succM M k) HDA BA)
     (source_dn_bounded M count b prevB(succM M k) HDB BB)
     (source_dn_bounded M count c prevC(succM M k) HDC BC)
     HSA HSB HSC HPreviousBC HPreviousPoint HTBC HResult PPrevious).
Qed.
Print Assumptions source_dn_binary_proof_definable.
Print Assumptions source_descriptor_dn_binary_map.
