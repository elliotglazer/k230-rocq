(** Checked closedness of the literal finite PA axioms and their genuine
    one-universal FullND generalization. *)
From FOL Require Import FullSyntax Arithmetics.
From Stdlib Require Import Lists.List Lia.
Import ListNotations FullSyntax.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.
#[local] Existing Instance falsity_on | 0.
#[local] Existing Instance class | 0.
Ltac full_PA_literal_bound :=
 lazymatch goal with
 | |- bounded _ falsity => constructor
 | |- bounded _ (quant _ _) => constructor;full_PA_literal_bound
 | |- bounded _ (bin _ _ _) => constructor;full_PA_literal_bound
 | |- bounded _ (atom _ _) => constructor;intros t H;full_PA_literal_vector
 | |- bounded_t _ (var _) => constructor;lia
 | |- bounded_t _ (func _ _) => constructor;intros t H;full_PA_literal_vector
 | |- ?G =>idtac "unmatched bound" G;fail 1
 end
with full_PA_literal_vector :=
 lazymatch goal with
 | H:Vector.In ?t (Vector.cons _ _ _ _) |- _ =>
   apply Vector.In_cons_iff in H;destruct H as[H|H];[subst t;full_PA_literal_bound|full_PA_literal_vector]
 | H:Vector.In _ (Vector.nil _) |- _ =>inversion H
 | |- ?G =>idtac "unmatched vector bound" G;fail 1
 end.
Ltac full_PA_closed_decision :=
 unfold closed;cbv[ax_refl ax_sym ax_trans ax_succ_congr ax_add_congr ax_mult_congr
  ax_add_zero ax_add_rec ax_mult_zero ax_mult_rec ax_zero_succ ax_succ_inj];full_PA_literal_bound.
Lemma full_PA_FAeq_closed ax:In ax FAeq ->closed ax.
Proof.
 intro H. cbn[FAeq EQ FA]in H.
 do 10(destruct H as[H|H];[subst ax;full_PA_closed_decision|]). contradiction.
Qed.
Lemma full_PA_zero_succ_closed:closed ax_zero_succ.
Proof. full_PA_closed_decision. Qed.
Lemma full_PA_succ_inj_closed:closed ax_succ_inj.
Proof. full_PA_closed_decision. Qed.
Lemma full_closed_formula_generalize(phi:form):closed phi ->
 @FullND.prv PA_funcs_signature PA_preds_signature falsity_on class (phi::nil)(∀phi).
Proof.
 intro HB. apply AllI. cbn.
 assert(E:phi[↑]=phi).
 { change(phi[iter up 0 ↑]=phi). now apply subst_bounded. }
 rewrite E. apply Ctx. now left.
Qed.
Print Assumptions full_PA_FAeq_closed.
Print Assumptions full_PA_zero_succ_closed.
Print Assumptions full_PA_succ_inj_closed.
Print Assumptions full_closed_formula_generalize.
