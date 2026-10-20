(** Exact constructor graph and substitution laws for source iff. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SetSchemaConstructors SourceBounded NumericalProofs
  NumericalSubstitutionMaps NumericalSubstitution SourcePropositionalRebase SourceFunctionalityShells.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.
Definition source_iff_graph M a b out:=code_relation M(sf_env a b)(E_sf_iff(CEvar 0)(CEvar 1))out.
Definition source_iff_formula(a b out:term):form:=code_formula(E_sf_iff(CEvar 0)(CEvar 1))(sf_env a b)out.
Theorem source_iff_formula_correct M rho a b out:
  holds M rho(source_iff_formula a b out)<->source_iff_graph M(evalM M rho a)(evalM M rho b)(evalM M rho out).
Proof.
  unfold source_iff_formula,source_iff_graph. rewrite code_formula_correct.
  apply code_relation_ext. intros[|i];reflexivity.
Qed.
Theorem source_iff_total M a b:exists out,source_iff_graph M a b out.
Proof. apply code_relation_total. Qed.
Theorem source_iff_functional M a b f g:source_iff_graph M a b f->source_iff_graph M a b g->f=g.
Proof. apply code_relation_functional. Qed.
Theorem source_iff_parts M a b out:source_iff_graph M a b out->exists lr rl,
  sf_relation M SFImpl a b lr /\sf_relation M SFImpl b a rl /\sf_relation M SFAnd lr rl out.
Proof.
  intro H. unfold source_iff_graph,E_sf_iff in H.
  destruct(schema_expression_split M _ _ _ _ out H)as(lr&rl&HL&HR&HO).
  exists lr,rl. split;[exact HL|]. split;[exact HR|exact HO].
Qed.
Theorem source_iff_build M a b lr rl out:
  sf_relation M SFImpl a b lr->sf_relation M SFImpl b a rl->sf_relation M SFAnd lr rl out->source_iff_graph M a b out.
Proof.
  intros HL HR HO. unfold source_iff_graph,E_sf_iff. functionality_graph.
Qed.
Theorem source_iff_substitution M a b out a' b' out' sb sc sn base:
  source_iff_graph M a b out->source_iff_graph M a' b' out'->
  numerical_substitution M a sb sc sn base a'->numerical_substitution M b sb sc sn base b'->
  numerical_substitution M out sb sc sn base out'.
Proof.
  intros H H' HA HB. destruct(source_iff_parts M a b out H)as(lr&rl&HL&HR&HO).
  destruct(source_iff_parts M a' b' out' H')as(lr'&rl'&HL'&HR'&HO').
  apply(proj2(numerical_substitution_binary M SFAnd lr rl out sb sc sn base out'(or_introl eq_refl)HO)).
  exists lr',rl'. split.
  - apply(proj2(numerical_substitution_binary M SFImpl a b lr sb sc sn base lr'(or_intror(or_intror eq_refl))HL)).
    exists a',b'. auto.
  - split;[|exact HO']. apply(proj2(numerical_substitution_binary M SFImpl b a rl sb sc sn base rl'
      (or_intror(or_intror eq_refl))HR)). exists b',a'. auto.
Qed.
Theorem source_iff_bounded M a b out k:
  source_bounded M a k->source_bounded M b k->source_iff_graph M a b out->source_bounded M out k.
Proof.
  intros HA HB H. destruct(source_iff_parts M a b out H)as(lr&rl&HL&HR&HO).
  apply(proj2(source_bounded_accept_binary M SFAnd lr rl out k(or_introl eq_refl)HO)). split.
  - apply(proj2(source_bounded_accept_binary M SFImpl a b lr k(or_intror(or_intror eq_refl))HL)). auto.
  - apply(proj2(source_bounded_accept_binary M SFImpl b a rl k(or_intror(or_intror eq_refl))HR)). auto.
Qed.
Print Assumptions source_iff_formula_correct.
Print Assumptions source_iff_substitution.
Print Assumptions source_iff_bounded.



