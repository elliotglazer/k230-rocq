(** Uniform actual proof production for NumF at every internal index.
    Only the two displayed finite set-existence certificates are inputs. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions NumericalProofs
 SetFormulaCodes NumericalRenamingMaps NumericalRenaming NumericalInstantiation
 SourceQuantifierRules SourceBounded SourceDefinabilityPrimitives SourceDefinabilityStep
 SourceDefinabilityIteration SourceDefinabilityBounds SourceDefinabilitySuccessor
 SourceDefinabilityLogicalStep SourceDescriptorProvability SourceDescriptorClosure
 SourceFiniteProofContexts SourceAxiomContexts NumericalContexts NumericalSourceFull.
From FOL Require Import FullSyntax Arithmetics.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.
Definition source_numf_proof_at M T n :=forall matrix ex,
 source_numf M n matrix ->sf_relation M SFEx matrix(zeroM M) ex ->
 source_descriptor_provable M T ex.
Definition source_numf_proof_formula T :form :=∀∀(
 source_numf_formula $2 $1 →sf_formula SFEx $1 zero $0 →source_descriptor_provable_formula T $0).
Local Opaque holds source_numf_formula sf_formula source_descriptor_provable_formula.
Lemma source_numf_proof_definable M T :Definable1 M(source_numf_proof_at M T).
Proof.
 exists(source_numf_proof_formula T),(fun _=>zeroM M). intro n.
 unfold source_numf_proof_formula,source_numf_proof_at.
 repeat setoid_rewrite holds_all. repeat setoid_rewrite holds_imp.
 setoid_rewrite source_numf_formula_correct. setoid_rewrite sf_formula_correct.
 setoid_rewrite source_descriptor_provable_formula_correct. reflexivity.
Qed.
Theorem source_descriptor_numf_induction M T :
 source_descriptor_provable M T(code_numeral M(sf_encode source_def_empty_exists)) ->
 source_descriptor_provable M T(code_numeral M(sf_encode source_def_succ_exists)) ->
 forall n,source_numf_proof_at M T n.
Proof.
 intros PZero PSucc. apply(definable_induction M(source_numf_proof_at M T)(source_numf_proof_definable M T)).
 - intros matrix ex HM HE. apply source_def_iteration_zero in HM. subst matrix.
   rewrite(sf_relation_functional M SFEx(code_numeral M(sf_encode source_def_empty))(zeroM M)
     ex(code_numeral M(sf_encode source_def_empty_exists)) HE(source_def_empty_exists_graph M)). exact PZero.
 - intros n IH matrix ex HM HE. apply source_def_iteration_succ in HM. destruct HM as(previous&HP&HS).
   destruct(source_def_step_graph M false previous matrix HS)as(s&pair&ES&HPair&HMatrix). subst s.
   destruct(sf_relation_total M SFEx previous(zeroM M))as(exprev&HExPrev).
   pose proof(IH previous exprev HP HExPrev)as PPrev.
   assert(Premises:forall f,In f (List.cons exprev(List.cons(code_numeral M(sf_encode source_def_succ_exists)) List.nil)) ->
      source_descriptor_provable M T f).
   { intros f[<-|[<-|[]]];assumption. }
   destruct(source_descriptor_finite_common_context M T _ Premises)as(b&c&l&HC&P).
   destruct(numerical_renaming_total M previous(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1))as(shifted&HShift).
   destruct(sf_relation_total M SFAnd shifted(code_numeral M(sf_encode source_def_succ10)))as(pairinst&HInstPair).
   exists b,c,l. split;[exact HC|].
   exact(source_full_unit_exists_successor M b c l previous shifted exprev
    (code_numeral M(sf_encode source_def_successor01))(code_numeral M(sf_encode source_def_succ10))
    (code_numeral M(sf_encode source_def_succ_exists)) pair matrix ex pairinst
    (proj1 HC)(source_numf_bound M n previous HP) HShift
    (numerical_def_successor_bound M)(source_def_succ10_bound M) HExPrev
    (source_def_succ_exists_graph M) HPair HMatrix HE(source_def_successor_swap M) HInstPair
    (P exprev(or_introl eq_refl))(P _(or_intror(or_introl eq_refl)))).
Qed.
Print Assumptions source_numf_proof_definable.
Print Assumptions source_descriptor_numf_induction.
