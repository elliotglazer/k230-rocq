(** Public six-argument relation for internally finite-prefix de Bruijn
    renaming.  The trace's unused padding coordinate is fixed to zero. *)
From PAModel Require Import Model FiniteCoding NumericalProofs SentenceBounds
  SetFormulaCodes SetCodeDescent NumericalRenamingMaps RenamingPayloads
  RenamingRules RenamingComputation RenamingFunctionality.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.

Definition numerical_renaming M f b c n delta v :=
  renaming_computation M f b c n delta (zeroM M) v.
Definition numerical_renaming_formula (f b c n delta v : term) : form :=
  renaming_computation_formula f b c n delta zero v.
Lemma numerical_renaming_formula_correct M rho f b c n delta v :
  holds M rho (numerical_renaming_formula f b c n delta v) <->
  numerical_renaming M (evalM M rho f) (evalM M rho b) (evalM M rho c)
    (evalM M rho n) (evalM M rho delta) (evalM M rho v).
Proof. apply renaming_computation_formula_correct. Qed.
Lemma numerical_renaming_formula_bound :
  bounded 6 (numerical_renaming_formula $0 $1 $2 $3 $4 $5).
Proof. apply formula_boundb_sound. vm_compute. reflexivity. Qed.
Theorem numerical_renaming_total M f b c n delta :
  exists v, numerical_renaming M f b c n delta v.
Proof. apply renaming_computation_total. Qed.
Theorem numerical_renaming_functional_equivalent M f b c n d e m delta v w :
  renaming_equivalent M b c n d e m delta ->
  numerical_renaming M f b c n delta v -> numerical_renaming M f d e m delta w -> v=w.
Proof. apply renaming_computation_functional_equivalent. Qed.
Theorem numerical_renaming_functional M f b c n delta v w :
  numerical_renaming M f b c n delta v -> numerical_renaming M f b c n delta w -> v=w.
Proof. apply renaming_computation_functional. Qed.
Theorem numerical_renaming_extensional M f b c n d e m delta v :
  renaming_equivalent M b c n d e m delta ->
  (numerical_renaming M f b c n delta v <-> numerical_renaming M f d e m delta v).
Proof. apply renaming_computation_environment_extensional. Qed.

Theorem numerical_renaming_invalid M f b c n delta v :
  (f=zeroM M \/ sf_invalid M f) ->
  (numerical_renaming M f b c n delta v <-> v=zeroM M).
Proof.
  intro Hbad. split.
  - apply renaming_computation_invalid. exact Hbad.
  - intro E. subst v. apply renaming_computation_leaf. left. auto.
Qed.
Theorem numerical_renaming_atom M equality a d f b c n delta v :
  sf_relation M (renaming_source_atom equality) a d f ->
  (numerical_renaming M f b c n delta v <->
   exists x y, renaming_lookup M b c n delta a x /\
     renaming_lookup M b c n delta d y /\
     sf_relation M (renaming_source_atom equality) x y v).
Proof.
  intro Hf. split.
  - apply renaming_computation_atom_inv. exact Hf.
  - intros [x [y [Hx [Hy Hv]]]]. apply renaming_computation_leaf. right.
    destruct equality; [right|left]; exists a,d,x,y; auto.
Qed.
Theorem numerical_renaming_member M a d f b c n delta v :
  sf_relation M SFMember a d f ->
  (numerical_renaming M f b c n delta v <->
   exists x y, renaming_lookup M b c n delta a x /\
     renaming_lookup M b c n delta d y /\ sf_relation M SFMember x y v).
Proof. apply (numerical_renaming_atom M false). Qed.
Theorem numerical_renaming_equal M a d f b c n delta v :
  sf_relation M SFEqual a d f ->
  (numerical_renaming M f b c n delta v <->
   exists x y, renaming_lookup M b c n delta a x /\
     renaming_lookup M b c n delta d y /\ sf_relation M SFEqual x y v).
Proof. apply (numerical_renaming_atom M true). Qed.
Theorem numerical_renaming_binary M h a d f b c n delta v :
  sf_binary h -> sf_relation M h a d f ->
  (numerical_renaming M f b c n delta v <->
   exists x y, numerical_renaming M a b c n delta x /\
     numerical_renaming M d b c n delta y /\ sf_relation M h x y v).
Proof.
  intros Hh Hf. split.
  - apply renaming_computation_binary_inv; assumption.
  - intros [x [y [Hx [Hy Hv]]]].
    exact (renaming_computation_binary M h a d f b c n delta (zeroM M) x y v Hh Hf Hx Hy Hv).
Qed.
Theorem numerical_renaming_quantifier M universal a f b c n delta v :
  sf_relation M (renaming_source_quantifier universal) a (zeroM M) f ->
  (numerical_renaming M f b c n delta v <->
   exists d e m w, renaming_lift M b c n delta d e m /\
     numerical_renaming M a d e m delta w /\
     sf_relation M (renaming_source_quantifier universal) w (zeroM M) v).
Proof.
  intro Hf. split.
  - apply renaming_computation_unary_inv. exact Hf.
  - intros [d [e [m [w [He [Hw Hv]]]]]].
    exact (renaming_computation_unary M universal a f b c n delta (zeroM M) d e m w v Hf He Hw Hv).
Qed.
