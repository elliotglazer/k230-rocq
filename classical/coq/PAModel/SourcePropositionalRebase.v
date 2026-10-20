(** Substitute fixed arithmetic code expressions for a finite propositional
    program's holes. This changes only its evaluation environment. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes
  SchemaConstructorBounds SourcePropositionalTemplates.
Unset Implicit Arguments.

Fixpoint source_prop_expression_with (holes:nat->code_expr) (a:source_prop_template) :=
  match a with
  | SPTSlot i=>holes i | SPTFalse=>CEconst 0
  | SPTImpl a b=>E_sf SFImpl (source_prop_expression_with holes a) (source_prop_expression_with holes b)
  | SPTAnd a b=>E_sf SFAnd (source_prop_expression_with holes a) (source_prop_expression_with holes b)
  | SPTOr a b=>E_sf SFOr (source_prop_expression_with holes a) (source_prop_expression_with holes b)
  end.

Lemma schema_expression_split M env h A B f :
  code_relation M env (E_sf h A B) f ->
  exists a b,code_relation M env A a /\code_relation M env B b /\sf_relation M h a b f.
Proof.
  intro HF. destruct (code_relation_total M A env) as [a HA].
  destruct (code_relation_total M B env) as [b HB].
  exists a,b. split;[exact HA|]. split;[exact HB|].
  exact (proj1 (schema_expression_graph M env h A B a b f HA HB) HF).
Qed.

Theorem source_prop_expression_with_graph M env holes rho a :
  (forall i,code_relation M env (holes i) (rho i)) ->
  forall f,code_relation M env (source_prop_expression_with holes a) f <->
    code_relation M rho (source_prop_expression a) f.
Proof.
  intro HH. induction a;intro f;cbn [source_prop_expression_with source_prop_expression].
  - split.
    + intro H. exact (code_relation_functional M (holes n) env f (rho n) H (HH n)).
    + intro E. change (f=rho n) in E. now subst f.
  - reflexivity.
  - destruct (code_relation_total M (source_prop_expression_with holes a1) env) as [u HU].
    destruct (code_relation_total M (source_prop_expression_with holes a2) env) as [v HV].
    rewrite (schema_expression_graph M env SFImpl _ _ u v f HU HV).
    rewrite (schema_expression_graph M rho SFImpl _ _ u v f (proj1 (IHa1 u) HU) (proj1 (IHa2 v) HV)). reflexivity.
  - destruct (code_relation_total M (source_prop_expression_with holes a1) env) as [u HU].
    destruct (code_relation_total M (source_prop_expression_with holes a2) env) as [v HV].
    rewrite (schema_expression_graph M env SFAnd _ _ u v f HU HV).
    rewrite (schema_expression_graph M rho SFAnd _ _ u v f (proj1 (IHa1 u) HU) (proj1 (IHa2 v) HV)). reflexivity.
  - destruct (code_relation_total M (source_prop_expression_with holes a1) env) as [u HU].
    destruct (code_relation_total M (source_prop_expression_with holes a2) env) as [v HV].
    rewrite (schema_expression_graph M env SFOr _ _ u v f HU HV).
    rewrite (schema_expression_graph M rho SFOr _ _ u v f (proj1 (IHa1 u) HU) (proj1 (IHa2 v) HV)). reflexivity.
Qed.

Print Assumptions schema_expression_split.
Print Assumptions source_prop_expression_with_graph.
