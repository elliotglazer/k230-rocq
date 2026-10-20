(** Public six-argument relation for internally finite-prefix de Bruijn
    substitution.  The trace's unused padding coordinate is fixed to zero. *)
From PAModel Require Import Model FiniteCoding NumericalProofs SentenceBounds
  SetFormulaCodes SetCodeDescent NumericalSubstitutionMaps SubstitutionPayloads
  SubstitutionRules SubstitutionComputation SubstitutionFunctionality.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.

Definition numerical_substitution M f b c n base v :=
  substitution_computation M f b c n base (zeroM M) v.
Definition numerical_substitution_formula (f b c n base v : term) : form :=
  substitution_computation_formula f b c n base zero v.
Lemma numerical_substitution_formula_correct M rho f b c n base v :
  holds M rho (numerical_substitution_formula f b c n base v) <->
  numerical_substitution M (evalM M rho f) (evalM M rho b) (evalM M rho c)
    (evalM M rho n) (evalM M rho base) (evalM M rho v).
Proof. apply substitution_computation_formula_correct. Qed.
Lemma numerical_substitution_formula_bound :
  bounded 6 (numerical_substitution_formula $0 $1 $2 $3 $4 $5).
Proof. apply formula_boundb_sound. vm_compute. reflexivity. Qed.
Theorem numerical_substitution_total M f b c n base :
  exists v, numerical_substitution M f b c n base v.
Proof. apply substitution_computation_total. Qed.
Theorem numerical_substitution_functional_equivalent M f b c n d e m base v w :
  substitution_equivalent M b c n d e m base ->
  numerical_substitution M f b c n base v -> numerical_substitution M f d e m base w -> v=w.
Proof. apply substitution_computation_functional_equivalent. Qed.
Theorem numerical_substitution_functional M f b c n base v w :
  numerical_substitution M f b c n base v -> numerical_substitution M f b c n base w -> v=w.
Proof. apply substitution_computation_functional. Qed.
Theorem numerical_substitution_extensional M f b c n d e m base v :
  substitution_equivalent M b c n d e m base ->
  (numerical_substitution M f b c n base v <-> numerical_substitution M f d e m base v).
Proof. apply substitution_computation_environment_extensional. Qed.

Theorem numerical_substitution_invalid M f b c n base v :
  (f=zeroM M \/ sf_invalid M f) ->
  (numerical_substitution M f b c n base v <-> v=zeroM M).
Proof.
  intro Hbad. split.
  - apply substitution_computation_invalid. exact Hbad.
  - intro E. subst v. apply substitution_computation_leaf. left. auto.
Qed.
Theorem numerical_substitution_atom M equality a d f b c n base v :
  sf_relation M (substitution_source_atom equality) a d f ->
  (numerical_substitution M f b c n base v <->
   exists x y, substitution_lookup M b c n base a x /\
     substitution_lookup M b c n base d y /\
     sf_relation M (substitution_source_atom equality) x y v).
Proof.
  intro Hf. split.
  - apply substitution_computation_atom_inv. exact Hf.
  - intros [x [y [Hx [Hy Hv]]]]. apply substitution_computation_leaf. right.
    destruct equality; [right|left]; exists a,d,x,y; auto.
Qed.
Theorem numerical_substitution_member M a d f b c n base v :
  sf_relation M SFMember a d f ->
  (numerical_substitution M f b c n base v <->
   exists x y, substitution_lookup M b c n base a x /\
     substitution_lookup M b c n base d y /\ sf_relation M SFMember x y v).
Proof. apply (numerical_substitution_atom M false). Qed.
Theorem numerical_substitution_equal M a d f b c n base v :
  sf_relation M SFEqual a d f ->
  (numerical_substitution M f b c n base v <->
   exists x y, substitution_lookup M b c n base a x /\
     substitution_lookup M b c n base d y /\ sf_relation M SFEqual x y v).
Proof. apply (numerical_substitution_atom M true). Qed.
Theorem numerical_substitution_binary M h a d f b c n base v :
  sf_binary h -> sf_relation M h a d f ->
  (numerical_substitution M f b c n base v <->
   exists x y, numerical_substitution M a b c n base x /\
     numerical_substitution M d b c n base y /\ sf_relation M h x y v).
Proof.
  intros Hh Hf. split.
  - apply substitution_computation_binary_inv; assumption.
  - intros [x [y [Hx [Hy Hv]]]].
    exact (substitution_computation_binary M h a d f b c n base (zeroM M) x y v Hh Hf Hx Hy Hv).
Qed.
Theorem numerical_substitution_quantifier M universal a f b c n base v :
  sf_relation M (substitution_source_quantifier universal) a (zeroM M) f ->
  (numerical_substitution M f b c n base v <->
   exists d e m w, substitution_lift M b c n base d e m /\
     numerical_substitution M a d e m (succM M base) w /\
     sf_relation M (substitution_source_quantifier universal) w (zeroM M) v).
Proof.
  intro Hf. split.
  - apply substitution_computation_unary_inv. exact Hf.
  - intros [d [e [m [w [He [Hw Hv]]]]]].
    exact (substitution_computation_unary M universal a f b c n base (zeroM M) d e m w v Hf He Hw Hv).
Qed.
