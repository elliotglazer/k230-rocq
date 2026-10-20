(** Actual double-negation elimination from the source calculus's Peirce
    rule, uniformly for arbitrary internally coded matrices. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded
  NumericalContexts NumericalSourceFull SourcePropositionalTemplates SourceFunctionalityShells.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Definition source_double_negation_template:=SPTImpl(SPTImpl(SPTSlot 0)SPTFalse)SPTFalse.
Lemma source_double_negation_program:source_prop_program[source_double_negation_template](SPTSlot 0).
Proof.
  eapply SPTIE;[exact(SPTPc _(SPTSlot 0)SPTFalse)|].
  apply SPTII,SPTExp. eapply(SPTIE _(SPTImpl(SPTSlot 0)SPTFalse)SPTFalse);
    apply SPTCtx;cbn;auto.
Qed.
Theorem source_full_double_negation_elimination M b c n a neg double:
  sf_relation M SFImpl a(zeroM M)neg ->sf_relation M SFImpl neg(zeroM M)double ->
  source_full_prv M b c n double ->source_full_prv M b c n a.
Proof.
  intros HN HD PD.
  destruct(source_full_prv_wellformed M b c n double PD)as(k&BDouble&BC).
  pose proof(proj1(proj1(source_bounded_accept_binary M SFImpl neg(zeroM M)double k
    (or_intror(or_intror eq_refl))HD)BDouble))as BNeg.
  pose proof(proj1(proj1(source_bounded_accept_binary M SFImpl a(zeroM M)neg k
    (or_intror(or_intror eq_refl))HN)BNeg))as BA.
  assert(HGraph:code_relation M(fun _=>a)(source_prop_expression source_double_negation_template)double).
  { unfold source_double_negation_template,source_prop_expression. functionality_graph. }
  apply(source_prop_program_sound M _ _ source_double_negation_program(fun _=>a)k b c n a
    ltac:(intro i;exact BA)BC);[|reflexivity].
  intros p[<-|[]]out HO. rewrite(code_relation_functional M _ _ out double HO HGraph). exact PD.
Qed.
Print Assumptions source_double_negation_program.
Print Assumptions source_full_double_negation_elimination.
