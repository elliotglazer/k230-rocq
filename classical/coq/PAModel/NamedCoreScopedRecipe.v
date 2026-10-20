(** Literal reduction of the native named K core to its four opaque matrix
    occurrences. Each occurrence retains its precise stack of repeated names. *)
From Stdlib Require Import List.
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions NumericalProofs
  SetFormulaCodes SetSchemaConstructors SchemaConstructorBounds RawSourceImage NativeKBundle
  SourceNamedScopes SourceNamedScopeBinding NativeNamedScopeEvaluation.
Import ListNotations.
Unset Implicit Arguments.

Definition scoped_expression_matches M env names t codeenv E :=
  forall f,code_relation M codeenv E f ->scoped_native_evaluation M env names t f.

Lemma scoped_expression_matches_binary M env names ta tb codeenv A B h :
  scoped_expression_matches M env names ta codeenv A ->
  scoped_expression_matches M env names tb codeenv B ->
  forall t,(h=SFImpl /\t=NNTImpl ta tb) \/(h=SFAnd /\t=NNTAnd ta tb) ->
  scoped_expression_matches M env names t codeenv (E_sf h A B).
Proof.
  intros HA HB t [[-> ->]|[-> ->]] f HF;
    destruct (code_relation_total M A codeenv) as (a&HEA),
      (code_relation_total M B codeenv) as (b&HEB);
    apply (schema_expression_graph M codeenv _ A B a b f HEA HEB) in HF;
    exists a,b.
  all: split;[exact (HA a HEA)|].
  all: split;[exact (HB b HEB)|exact HF].
Qed.

Lemma scoped_expression_matches_quantifier M env names nameExpr name t codeenv E h :
  code_relation M env nameExpr name ->
  scoped_expression_matches M env (name::names) t codeenv E ->
  forall resultTemplate,(h=SFAll /\resultTemplate=NNTAll nameExpr t) \/
    (h=SFEx /\resultTemplate=NNTEx nameExpr t) ->
  scoped_expression_matches M env names resultTemplate codeenv (E_sf h E (CEconst 0)).
Proof.
  intros HN HT resultTemplate [[-> ->]|[-> ->]] f HF;
    destruct (code_relation_total M E codeenv) as (body&HE);
    apply (schema_expression_graph M codeenv _ E (CEconst 0) body (zeroM M) f HE eq_refl) in HF;
    exists name,body.
  all: split;[exact HN|].
  all: split;[exact (HT body HE)|exact HF].
Qed.

Lemma scoped_expression_matches_atom M env names eq x y a b u v codeenv U V :
  code_relation M env x a ->code_relation M env y b ->
  named_scope_index M names a u ->named_scope_index M names b v ->
  code_relation M codeenv U u ->code_relation M codeenv V v ->
  scoped_expression_matches M env names (NNTAtom eq x y) codeenv
    (E_sf (if eq then SFEqual else SFMember) U V).
Proof.
  intros HX HY HU HV HEU HEV f HF.
  apply (schema_expression_graph M codeenv _ U V u v f HEU HEV) in HF.
  exists a,b,u,v. repeat first [assumption|split].
Qed.

Lemma scoped_expression_matches_hole M env names hole phi out codeenv E :
  raw_source_image M (env hole) phi ->named_scope_renaming M names phi out ->
  code_relation M codeenv E out ->
  scoped_expression_matches M env names (NNTHole hole) codeenv E.
Proof.
  intros HP HR HE f HF.
  rewrite (code_relation_functional M E codeenv f out HF HE).
  exists phi. auto.
Qed.

Definition E_named_core_scoped (b q0 q1 q2 q3:code_expr) :=
  E_sf_ex (E_sf SFAnd (E_sf SFImpl q0 (E_sf SFMember (CEadd b (CEconst 1)) (CEconst 0)))
    (E_sf_all (E_sf SFImpl (E_sf_mem 0 1)
      (E_sf_ex (E_sf SFAnd q1
        (E_sf_all (E_sf SFImpl
          (E_sf_all (E_sf SFImpl (E_sf_mem 0 1) (E_sf_mem 0 3)))
          (E_sf_all (E_sf SFImpl q2 (E_sf_ex (E_sf SFAnd q3 (E_sf_mem 0 5)))))))))))).

Definition named_core_scoped_env {A} (b q0 q1 q2 q3:A) i :=match i with
  |0=>b|1=>q0|2=>q1|3=>q2|_=>q3 end.

Ltac named_scoped_constructor :=
  match goal with
  | |-scoped_expression_matches _ _ _ (NNTImpl _ _) _ _=>
    eapply (scoped_expression_matches_binary _ _ _ _ _ _ _ _ SFImpl);[| |left;split;reflexivity]
  | |-scoped_expression_matches _ _ _ (NNTAnd _ _) _ _=>
    eapply (scoped_expression_matches_binary _ _ _ _ _ _ _ _ SFAnd);[| |right;split;reflexivity]
  | |-scoped_expression_matches _ _ _ (NNTAll _ _) _ _=>
    eapply (scoped_expression_matches_quantifier _ _ _ _ _ _ _ _ SFAll);[| |left;split;reflexivity];[reflexivity|]
  | |-scoped_expression_matches _ _ _ (NNTEx _ _) _ _=>
    eapply (scoped_expression_matches_quantifier _ _ _ _ _ _ _ _ SFEx);[| |right;split;reflexivity];[reflexivity|]
  end.

Lemma named_core_add_one M i :addM M i (code_numeral M 1)=succM M i.
Proof.
  change (addM M i (succM M (zeroM M))=succM M i).
  now rewrite Arithmetic.add_comm,Arithmetic.add_succ,Arithmetic.add_zero.
Qed.
Ltac named_scope_atom_index :=
  first [reflexivity|left;split;reflexivity|
    right;split;[congruence|];eexists;split;[named_scope_atom_index|reflexivity]].

Theorem named_core_scoped_recipe M a b c u phi q0 q1 q2 q3 :
  a<>b ->c<>a ->c<>b ->raw_source_image M c phi ->
  named_scope_renaming M [c] phi q0 ->named_scope_renaming M [a;b;c] phi q1 ->
  named_scope_renaming M [b;a;a;b;c] phi q2 ->named_scope_renaming M [b;b;a;a;b;c] phi q3 ->
  scoped_expression_matches M (code_parameters a b c u) []
    (NNT_core (CEvar 0) (CEvar 1) (CEvar 2) (NNTHole 2))
    (named_core_scoped_env b q0 q1 q2 q3)
    (E_named_core_scoped (CEvar 0) (CEvar 1) (CEvar 2) (CEvar 3) (CEvar 4)).
Proof.
  intros Hab Hca Hcb HP H0 H1 H2 H3.
  unfold E_named_core_scoped,E_sf_all,E_sf_ex,E_sf_mem,NNT_core,NNT_subset,NNT_request.
  repeat named_scoped_constructor.



  all: try solve [eapply scoped_expression_matches_hole;[exact HP|eassumption|reflexivity]].
  all: eapply scoped_expression_matches_atom;[reflexivity|reflexivity| | | |reflexivity].
  all: try solve [first [reflexivity|exists b,(code_numeral M 1);repeat first [reflexivity|split]]].
  all: cbn [code_parameters named_core_scoped_env named_scope_index].
  all: rewrite ?named_core_add_one.
  all: named_scope_atom_index.
Qed.

Theorem native_named_core_scoped_exact M a b c u phi q0 q1 q2 q3 original result :
  a<>b ->c<>a ->c<>b ->raw_source_image M c phi ->
  named_scope_renaming M [c] phi q0 ->named_scope_renaming M [a;b;c] phi q1 ->
  named_scope_renaming M [b;a;a;b;c] phi q2 ->named_scope_renaming M [b;b;a;a;b;c] phi q3 ->
  native_named_evaluation M (code_parameters a b c u)
    (NNT_core (CEvar 0) (CEvar 1) (CEvar 2) (NNTHole 2)) original ->
  code_relation M (named_core_scoped_env b q0 q1 q2 q3)
    (E_named_core_scoped (CEvar 0) (CEvar 1) (CEvar 2) (CEvar 3) (CEvar 4)) result ->original=result.
Proof.
  intros Hab Hca Hcb HP H0 H1 H2 H3 HO HR.
  apply (scoped_native_evaluation_functional M (code_parameters a b c u)
    (NNT_core (CEvar 0) (CEvar 1) (CEvar 2) (NNTHole 2)) [] original result).
  - exact (native_named_scope_empty_exact M _ _ original HO).
  - exact (named_core_scoped_recipe M a b c u phi q0 q1 q2 q3 Hab Hca Hcb HP H0 H1 H2 H3 result HR).
Qed.

Print Assumptions native_named_core_scoped_exact.
