(** Bound propagation for the exact finite source schema constructors.
    The body codes and variable bounds are arbitrary PA-model elements. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT
  CodeExpressions SetFormulaCodes SetCodeDescent SourceBounded
  SetSchemaConstructors.
From Stdlib Require Import Lia.
Unset Implicit Arguments.

Lemma schema_expression_graph M env h A B a b f :
  code_relation M env A a -> code_relation M env B b ->
  (code_relation M env (E_sf h A B) f <-> sf_relation M h a b f).
Proof.
  intros HA HB. rewrite sf_relation_graph.
  destruct h; cbn [E_sf sf_payload_second sf_tag];
    apply sf_expression_pair_graph; try assumption;reflexivity.
Qed.

Definition schema_expression_bound M env E k :=
  forall f, code_relation M env E f -> source_bounded M f k.

Lemma schema_expression_binary M env h A B k : sf_binary h ->
  schema_expression_bound M env A k -> schema_expression_bound M env B k ->
  schema_expression_bound M env (E_sf h A B) k.
Proof.
  intros Hh HA HB f Hf.
  destruct (code_relation_total M A env) as [a Ha].
  destruct (code_relation_total M B env) as [b Hb].
  apply (schema_expression_graph M env h A B a b f Ha Hb) in Hf.
  apply (proj2 (source_bounded_accept_binary M h a b f k Hh Hf)).
  split; [apply HA|apply HB];assumption.
Qed.

Lemma schema_expression_unary M env h A k : sf_unary h ->
  schema_expression_bound M env A (succM M k) ->
  schema_expression_bound M env (E_sf h A (CEconst 0)) k.
Proof.
  intros Hh HA f Hf.
  destruct (code_relation_total M A env) as [a Ha].
  apply (schema_expression_graph M env h A (CEconst 0) a (zeroM M) f Ha eq_refl) in Hf.
  apply (proj2 (source_bounded_accept_unary M h a f k Hh Hf)).
  now apply HA.
Qed.

Lemma schema_expression_atom M env h i j k : sb_atomic h ->
  coding_lt M (code_numeral M i) k -> coding_lt M (code_numeral M j) k ->
  schema_expression_bound M env (E_sf h (CEconst i) (CEconst j)) k.
Proof.
  intros Hh Hi Hj f Hf.
  apply (schema_expression_graph M env h (CEconst i) (CEconst j)
    (code_numeral M i) (code_numeral M j) f eq_refl eq_refl) in Hf.
  apply (proj2 (source_bounded_accept_atom M h _ _ f k Hh Hf)). auto.
Qed.

Lemma schema_expression_variable M env i k : source_bounded M (env i) k ->
  schema_expression_bound M env (CEvar i) k.
Proof. intros H f E. cbn [code_relation] in E. now subst f. Qed.

Lemma schema_expression_iff M env A B k :
  schema_expression_bound M env A k -> schema_expression_bound M env B k ->
  schema_expression_bound M env (E_sf_iff A B) k.
Proof.
  intros HA HB. unfold E_sf_iff.
  apply schema_expression_binary; [now left| |];
    apply schema_expression_binary; unfold sf_binary;auto.
Qed.

Ltac schema_constructor_bound :=
  first [apply schema_expression_iff
  | apply schema_expression_binary; [solve [unfold sf_binary;auto]| |]
  | apply schema_expression_unary; [solve [unfold sf_unary;auto]|]
  | apply schema_expression_atom; [solve [unfold sb_atomic;auto]| |]
  | apply schema_expression_variable].

Ltac schema_small_index :=
  cbn [code_numeral];
  repeat apply (proj2 (coding_lt_succ_cancel _ _ _));
  apply coding_zero_lt_succ.

Theorem schema_separation_constructor_bound M body f n :
  source_bounded M body (succM M (succM M (succM M n))) ->
  sf_separation_constructor M body f -> source_bounded M f n.
Proof.
  intros Hb Hf.
  assert (Hbound : schema_expression_bound M (fun _ => body)
    (E_sf_separation (CEvar 0)) n).
  { unfold E_sf_separation,E_sf_all,E_sf_ex,E_sf_mem.
    repeat schema_constructor_bound; try schema_small_index;exact Hb. }
  exact (Hbound f Hf).
Qed.

Theorem schema_replacement_constructor_bound M a b c f n :
  source_bounded M a (succM M (succM M (succM M n))) ->
  source_bounded M b (succM M (succM M (succM M n))) ->
  source_bounded M c (succM M (succM M (succM M (succM M n)))) ->
  sf_replacement_constructor M a b c f -> source_bounded M f n.
Proof.
  intros HA HB HC Hf.
  assert (Hbound : schema_expression_bound M (schema_env3 a b c)
    (E_sf_replacement (CEvar 0) (CEvar 1) (CEvar 2)) n).
  { unfold E_sf_replacement,E_sf_functionality,E_sf_all,E_sf_ex,E_sf_mem,E_sf_eq.
    repeat schema_constructor_bound; try schema_small_index;assumption. }
  exact (Hbound f Hf).
Qed.

