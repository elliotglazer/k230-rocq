(** Literal constructor graphs for ordinary and relativized functionality.
    These lemmas only unpack arithmetic syntax; they assume no proofs. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes
  SchemaConstructorBounds SetSchemaConstructors SourceRelativeSchemaConstructors.
Unset Implicit Arguments.

Definition source_functionality_graph M a b f :=
  code_relation M (schema_env3 a b (zeroM M)) (E_sf_functionality (CEvar 0) (CEvar 1)) f.
Definition source_relative_functionality_graph M d a b f :=
  code_relation M (schema_env3 d a b)
    (E_sf_relative_functionality (CEvar 0) (CEvar 1) (CEvar 2)) f.

Lemma source_sf_expression_join M rho h A B a b f :
  code_relation M rho A a -> code_relation M rho B b -> sf_relation M h a b f ->
  code_relation M rho (E_sf h A B) f.
Proof. intros HA HB HF. exact (proj2 (schema_expression_graph M rho h A B a b f HA HB) HF). Qed.

Ltac functionality_graph :=
  match goal with
  | |- code_relation ?M ?rho (E_sf ?h ?A ?B) ?f =>
      eapply (source_sf_expression_join M rho h A B);
        [functionality_graph|functionality_graph|eassumption]
  | |- code_relation _ _ (CEvar _) _ => reflexivity
  | |- code_relation _ _ (CEconst _) _ => reflexivity
  end.

Theorem source_relative_functionality_shell M domain a b eq f :
  sf_relation M SFEqual (code_numeral M 1) (zeroM M) eq ->
  source_relative_functionality_graph M domain a b f ->
  exists rhs point g2 p1 g1 p0 g0,
    sf_relation M SFImpl b eq rhs /\ sf_relation M SFImpl a rhs point /\
    sf_relation M SFImpl domain point g2 /\ sf_relation M SFAll g2 (zeroM M) p1 /\
    sf_relation M SFImpl domain p1 g1 /\ sf_relation M SFAll g1 (zeroM M) p0 /\
    sf_relation M SFImpl domain p0 g0 /\ sf_relation M SFAll g0 (zeroM M) f.
Proof.
  intros HE HF.
  destruct (sf_relation_total M SFImpl b eq) as [rhs HR].
  destruct (sf_relation_total M SFImpl a rhs) as [point HP].
  destruct (sf_relation_total M SFImpl domain point) as [g2 HG2].
  destruct (sf_relation_total M SFAll g2 (zeroM M)) as [p1 HQ2].
  destruct (sf_relation_total M SFImpl domain p1) as [g1 HG1].
  destruct (sf_relation_total M SFAll g1 (zeroM M)) as [p0 HQ1].
  destruct (sf_relation_total M SFImpl domain p0) as [g0 HG0].
  destruct (sf_relation_total M SFAll g0 (zeroM M)) as [f0 HQ0].
  assert (HF0:source_relative_functionality_graph M domain a b f0).
  { unfold source_relative_functionality_graph,E_sf_relative_functionality,
      E_sf_relative_all,E_sf_all,E_sf_eq. functionality_graph. }
  pose proof (code_relation_functional M _ _ f f0 HF HF0) as E. subst f0.
  exists rhs,point,g2,p1,g1,p0,g0. repeat split;assumption.
Qed.

Theorem source_functionality_shell M a b eq f :
  sf_relation M SFEqual (code_numeral M 1) (zeroM M) eq ->
  source_functionality_graph M a b f ->
  exists rhs point p1 p2,
    sf_relation M SFImpl b eq rhs /\ sf_relation M SFImpl a rhs point /\
    sf_relation M SFAll point (zeroM M) p1 /\ sf_relation M SFAll p1 (zeroM M) p2 /\
    sf_relation M SFAll p2 (zeroM M) f.
Proof.
  intros HE HF.
  destruct (sf_relation_total M SFImpl b eq) as [rhs HR].
  destruct (sf_relation_total M SFImpl a rhs) as [point HP].
  destruct (sf_relation_total M SFAll point (zeroM M)) as [p1 HQ1].
  destruct (sf_relation_total M SFAll p1 (zeroM M)) as [p2 HQ2].
  destruct (sf_relation_total M SFAll p2 (zeroM M)) as [f0 HQ0].
  assert (HF0:source_functionality_graph M a b f0).
  { unfold source_functionality_graph,E_sf_functionality,E_sf_all,E_sf_eq. functionality_graph. }
  pose proof (code_relation_functional M _ _ f f0 HF HF0) as E. subst f0.
  exists rhs,point,p1,p2. repeat split;assumption.
Qed.

Print Assumptions source_relative_functionality_shell.
Print Assumptions source_functionality_shell.
