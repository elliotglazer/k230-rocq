(** Map an internally finite formula table to a fixed proof macro's
    implication telescope. Only the macro's list of ordinary premises is external. *)
From PAModel Require Import Model FiniteCoding FiniteCRT FiniteCRTFormula CodeExpressions NumericalProofs
  SetFormulaCodes BoundedCollection SourceFiniteTelescope.
From FOL Require Import FullSyntax Arithmetics.
From Stdlib Require Import Lists.List.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature|0.
#[local] Existing Instance PA_preds_signature|0.

Definition source_implication_output_table M a ib ic count ob oc:=
  forall i inner out,coding_lt M i count ->beta M ib ic i inner ->beta M ob oc i out ->
    sf_relation M SFImpl a inner out.
Definition source_implication_table_step_formula:form:=∃(
  beta_formula $3 $4 $2 $0 ∧sf_formula SFImpl $5 $0 $1).
Local Opaque holds beta_formula sf_formula.

Theorem source_implication_table_step_correct M a ib ic i out:
  holds M(out .: i .: ib .: ic .: a .: fun _=>zeroM M)source_implication_table_step_formula <->
  exists inner,beta M ib ic i inner /\sf_relation M SFImpl a inner out.
Proof.
  unfold source_implication_table_step_formula.
  setoid_rewrite holds_ex. setoid_rewrite holds_and.
  setoid_rewrite beta_formula_correct. setoid_rewrite sf_formula_correct. reflexivity.
Qed.

Theorem source_implication_output_table_total M a ib ic count:
  exists ob oc,source_implication_output_table M a ib ic count ob oc.
Proof.
  assert(HTotal:collection_total M source_implication_table_step_formula
    (ib .: ic .: a .: fun _=>zeroM M)count).
  { intros i _. destruct(beta_total M ib ic i)as(inner&HI).
    destruct(sf_relation_total M SFImpl a inner)as(out&HO). exists out.
    apply(proj2(source_implication_table_step_correct M a ib ic i out)). exists inner. auto. }
  destruct(bounded_collection_table M source_implication_table_step_formula
    (ib .: ic .: a .: fun _=>zeroM M)count HTotal)as(ob&oc&HT).
  exists ob,oc. intros i inner out HI HInner HOut.
  destruct(proj1(source_implication_table_step_correct M a ib ic i out)(HT i out HI HOut))as(inner'&HInner'&HO).
  pose proof(beta_unique M ib ic i inner inner' HInner HInner')as E. now subst inner'.
Qed.

Definition source_telescope_output_table M A ib ic count ob oc:=
  forall i inner out,coding_lt M i count ->beta M ib ic i inner ->beta M ob oc i out ->
    source_finite_telescope M A inner out.

Theorem source_telescope_output_table_total M A ib ic count:
  exists ob oc,source_telescope_output_table M A ib ic count ob oc.
Proof.
  induction A as[|a A IH].
  - exists ib,ic. intros i inner out HI HInner HOut.
    change(out=inner). exact(beta_unique M ib ic i out inner HOut HInner).
  - destruct IH as(tb&tc&HT).
    destruct(source_implication_output_table_total M a tb tc count)as(ob&oc&HO).
    exists ob,oc. intros i inner out HI HInner HOut.
    destruct(beta_total M tb tc i)as(middle&HM).
    exists middle. split;[exact(HT i inner middle HI HInner HM)|].
    exact(HO i middle out HI HM HOut).
Qed.

Print Assumptions source_implication_table_step_correct.
Print Assumptions source_implication_output_table_total.
Print Assumptions source_telescope_output_table_total.
