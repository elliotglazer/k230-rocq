(** The equality predicate of an arbitrary PAeq interpretation is an
    equivalence relation and respects every arithmetic function symbol.
    This uses the literal equality axioms, before any native-equality quotient. *)
From Stdlib Require Import List Vectors.Vector.
From FOL Require Import FullSyntax Arithmetics.
Import Vector.VectorNotations.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.

Definition pa_equality_relation D (I : interp D) (x y : D) :=
 @i_atom PA_funcs_signature PA_preds_signature D I Eq ([x;y]).

Lemma paeq_equality_axiom phi : List.In phi EQ -> PAeq phi.
Proof.
 intro H. apply PAeq_FA. unfold FAeq. apply in_or_app. now left.
Qed.

Theorem paeq_relation_laws D (I : interp D) :
 (forall phi rho, PAeq phi -> @sat _ _ D I falsity_on rho phi) ->
 (forall x, pa_equality_relation D I x x) /\
 (forall x y, pa_equality_relation D I x y -> pa_equality_relation D I y x) /\
 (forall x y z, pa_equality_relation D I x y -> pa_equality_relation D I y z -> pa_equality_relation D I x z).
Proof.
 intro HA. set (rho := fun _ : nat => @i_func _ _ D I Zero ([])).
 pose proof (HA ax_refl rho (paeq_equality_axiom ax_refl (or_introl eq_refl))) as HRefl.
 pose proof (HA ax_sym rho (paeq_equality_axiom ax_sym (or_intror (or_introl eq_refl)))) as HSym.
 pose proof (HA ax_trans rho (paeq_equality_axiom ax_trans (or_intror (or_intror (or_introl eq_refl))))) as HTrans.
 split; [exact HRefl|]. split; [exact HSym|exact HTrans].
Qed.

Theorem paeq_relation_function_laws D (I : interp D) :
 (forall phi rho, PAeq phi -> @sat _ _ D I falsity_on rho phi) ->
 (forall x y, pa_equality_relation D I x y ->
   pa_equality_relation D I (@i_func _ _ D I Succ ([x])) (@i_func _ _ D I Succ ([y]))) /\
 (forall x x' y y', pa_equality_relation D I x x' -> pa_equality_relation D I y y' ->
   pa_equality_relation D I (@i_func _ _ D I Plus ([x;y])) (@i_func _ _ D I Plus ([x';y']))) /\
 (forall x x' y y', pa_equality_relation D I x x' -> pa_equality_relation D I y y' ->
   pa_equality_relation D I (@i_func _ _ D I Mult ([x;y])) (@i_func _ _ D I Mult ([x';y']))).
Proof.
 intro HA. set (rho := fun _ : nat => @i_func _ _ D I Zero ([])).
 pose proof (HA ax_succ_congr rho (paeq_equality_axiom ax_succ_congr
   (or_intror (or_intror (or_intror (or_introl eq_refl)))))) as HS.
 pose proof (HA ax_add_congr rho (paeq_equality_axiom ax_add_congr
   (or_intror (or_intror (or_intror (or_intror (or_introl eq_refl))))))) as HA'.
 pose proof (HA ax_mult_congr rho (paeq_equality_axiom ax_mult_congr
   (or_intror (or_intror (or_intror (or_intror (or_intror (or_introl eq_refl)))))))) as HM.
 split.
 - intros x y H. exact (HS y x H).
 - split.
   + intros x x' y y' Hx Hy. exact (HA' y' y x' x Hx Hy).
   + intros x x' y y' Hx Hy. exact (HM y' y x' x Hx Hy).
Qed.

Print Assumptions paeq_relation_laws.
Print Assumptions paeq_relation_function_laws.
