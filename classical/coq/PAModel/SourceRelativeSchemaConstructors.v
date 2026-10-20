(** The exact open target matrices for the WF schema proofs. The inserted
    domain graph is a formula code, not an assumed true class predicate. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes
  SetSchemaConstructors QuotationSchemaSkeleton SourceRelativization
  SourceRelativizationFunctionality SourceSchemaRelativization.
Unset Implicit Arguments.

Definition E_sf_relative_all d a := E_sf_all (E_sf SFImpl d a).
Definition E_sf_relative_ex d a := E_sf_ex (E_sf SFAnd d a).
Definition E_sf_relative_separation d body :=
  E_sf_relative_all d (E_sf_relative_ex d (E_sf_relative_all d
    (E_sf_iff (E_sf_mem 0 1) (E_sf SFAnd (E_sf_mem 0 2) body)))).
Definition E_sf_relative_functionality d a b :=
  E_sf_relative_all d (E_sf_relative_all d (E_sf_relative_all d
    (E_sf SFImpl a (E_sf SFImpl b (E_sf_eq 1 0))))).
Definition E_sf_relative_replacement d a b c :=
  E_sf SFImpl (E_sf_relative_functionality d a b)
    (E_sf_relative_all d (E_sf_relative_ex d (E_sf_relative_all d
      (E_sf_iff (E_sf_mem 0 1)
        (E_sf_relative_ex d (E_sf SFAnd (E_sf_mem 0 3) c)))))).

Lemma relative_separation_skeleton_exact :
  skeleton_relative_code separation_skeleton=
    E_sf_relative_separation (CEvar 0) (CEvar 1).
Proof. reflexivity. Qed.
Lemma relative_replacement_skeleton_exact :
  skeleton_relative_code replacement_skeleton=
    E_sf_relative_replacement (CEvar 0) (CEvar 1) (CEvar 2) (CEvar 3).
Proof. reflexivity. Qed.

Theorem source_separation_constructor_relativization_exact M d body rbody f rf :
  source_relativization M d body rbody -> sf_separation_constructor M body f ->
  (source_relativization M d f rf <-> sf_relative_separation_constructor M d rbody rf).
Proof.
  intros HB HF. split.
  - intro HR. destruct (code_relation_total M (skeleton_relative_code separation_skeleton)
      (skeleton_relative_environment d (fun _=>rbody))) as [v HV].
    pose proof (source_separation_constructor_relativization M d body rbody f v HB HF HV) as HS.
    pose proof (source_relativization_functional M f d rf v HR HS) as E. now subst rf.
  - exact (source_separation_constructor_relativization M d body rbody f rf HB HF).
Qed.

Theorem source_replacement_constructor_relativization_exact M d a b c ra rb rc f rf :
  source_relativization M d a ra -> source_relativization M d b rb ->
  source_relativization M d c rc -> sf_replacement_constructor M a b c f ->
  (source_relativization M d f rf <-> sf_relative_replacement_constructor M d ra rb rc rf).
Proof.
  intros HA HB HC HF. split.
  - intro HR. destruct (code_relation_total M (skeleton_relative_code replacement_skeleton)
      (skeleton_relative_environment d (schema_env3 ra rb rc))) as [v HV].
    pose proof (source_replacement_constructor_relativization M d a b c ra rb rc f v
      HA HB HC HF HV) as HS.
    pose proof (source_relativization_functional M f d rf v HR HS) as E. now subst rf.
  - exact (source_replacement_constructor_relativization M d a b c ra rb rc f rf HA HB HC HF).
Qed.

Print Assumptions relative_separation_skeleton_exact.
Print Assumptions relative_replacement_skeleton_exact.
Print Assumptions source_separation_constructor_relativization_exact.
Print Assumptions source_replacement_constructor_relativization_exact.
