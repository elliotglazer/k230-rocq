(** Literal fixed set-operation facts needed by the varying-matrix recursion. *)
From OldUndecidability.FOL Require Import Syntax.Facts Sets.minZF Deduction.FullNDFacts.
From OldZF Require Import Std_iface Std_setnd Std_setbase Std_setrec.
From OldZFC Require Import Z_base.
From PAModel Require Import SourceLFixed SourceHierarchyOld.
From Stdlib Require Import Lists.List.
Import ListNotations.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.
Inductive source_recursion_fixed_fact :=
| RecOpExists | RecSingExists | RecAdjExists | RecOpInjective | RecAgreeUse
| RecAppSing | RecAppSingIntro | RecAppAdjEl | RecAppAdjLeft | RecAppAdjRight
| RecEqReflexive | RecEqSymmetric | RecEqTransitive
| RecMemberLeft | RecMemberRight | RecEqualLeft | RecEqualRight.
Definition old_recursion_fact (tag:source_recursion_fixed_fact) :form :=
 match tag with
 | RecOpExists => ∃ OP $1 $2 $0
 | RecSingExists => ∃ Sing $1 $0
 | RecAdjExists => ∃ Adj $1 $2 $0
 | RecOpInjective => OP $0 $1 $4 →OP $2 $3 $5 →$4 ≡' $5 →($0 ≡' $2 ∧ $1 ≡' $3)
 | RecAgreeUse => Agr $0 $1 $2 →App $0 $2 $3 →App $1 $2 $4 →$3 ≡' $4
 | RecAppSing => Sing $0 $1 →App $1 $2 $3 →OP $2 $3 $0
 | RecAppSingIntro => Sing $0 $1 →OP $2 $3 $0 →App $1 $2 $3
 | RecAppAdjEl => Adj $0 $1 $2 →App $2 $3 $4 →(App $0 $3 $4 ∨ OP $3 $4 $1)
 | RecAppAdjLeft => Adj $0 $1 $2 →App $0 $3 $4 →App $2 $3 $4
 | RecAppAdjRight => Adj $0 $1 $2 →OP $3 $4 $1 →App $2 $3 $4
 | RecEqReflexive => $0 ≡' $0
 | RecEqSymmetric => $0 ≡' $1 →$1 ≡' $0
 | RecEqTransitive => $0 ≡' $1 →$1 ≡' $2 →$0 ≡' $2
 | RecMemberLeft => $0 ≡' $1 →$0 ∈' $2 →$1 ∈' $2
 | RecMemberRight => $0 ≡' $1 →$2 ∈' $0 →$2 ∈' $1
 | RecEqualLeft => $0 ≡' $1 →$0 ≡' $2 →$1 ≡' $2
 | RecEqualRight => $0 ≡' $1 →$2 ≡' $0 →$2 ≡' $1
 end.
Ltac recursion_fixed_background :=
 intros z Hz;repeat first[solve[exact(old_hierarchy_base z Hz)]|right].
Ltac recursion_fixed_context :=apply Ctx;cbn;tauto.
Theorem old_recursion_fact_proof tag :old_L_background ⊢C old_recursion_fact tag.
Proof.
 destruct tag;cbn[old_recursion_fact].
 - exact(op_ex old_hierarchy_base $0 $1).
 - exact(sing_ex old_hierarchy_base $0).
 - exact(adj_ex old_hierarchy_base $0 $1).
 - apply II,II,II. eapply op_inj;[recursion_fixed_background|recursion_fixed_context|recursion_fixed_context|recursion_fixed_context].
 - apply II,II,II. eapply agree_use;[recursion_fixed_background|recursion_fixed_context|recursion_fixed_context|recursion_fixed_context].
 - apply II,II. eapply app_sing;[recursion_fixed_background|recursion_fixed_context|recursion_fixed_context].
 - apply II,II. eapply app_sing_intro;[recursion_fixed_background|recursion_fixed_context|recursion_fixed_context].
 - apply II,II. eapply app_adj_el;[recursion_fixed_background|recursion_fixed_context|recursion_fixed_context].
 - apply II,II. eapply app_adj_l;[recursion_fixed_background|recursion_fixed_context|recursion_fixed_context].
 - apply II,II. eapply app_adj_r;[recursion_fixed_background|recursion_fixed_context|recursion_fixed_context].
 - exact(eq_refl' old_hierarchy_base $0).
 - apply II. eapply eq_sym';[recursion_fixed_background|recursion_fixed_context].
 - apply II,II. eapply eq_trans';[recursion_fixed_background|recursion_fixed_context|recursion_fixed_context].
 - apply II,II.
   assert(E:($0 ∈' $2::$0 ≡' $1::old_L_background) ⊢C $0 ≡' $1)by recursion_fixed_context.
   assert(H:($0 ∈' $2::$0 ≡' $1::old_L_background) ⊢C $0 ∈' $2)by recursion_fixed_context.
   assert(HG:incl ZF0base($0 ∈' $2::$0 ≡' $1::old_L_background))by recursion_fixed_background.
   frew_in E ($0 ∈' $2`[↑]) H. exact H.
 - apply II,II.
   assert(E:($2 ∈' $0::$0 ≡' $1::old_L_background) ⊢C $0 ≡' $1)by recursion_fixed_context.
   assert(H:($2 ∈' $0::$0 ≡' $1::old_L_background) ⊢C $2 ∈' $0)by recursion_fixed_context.
   assert(HG:incl ZF0base($2 ∈' $0::$0 ≡' $1::old_L_background))by recursion_fixed_background.
   frew_in E ($2`[↑] ∈' $0) H. exact H.
 - apply II,II.
   assert(E:($0 ≡' $2::$0 ≡' $1::old_L_background) ⊢C $0 ≡' $1)by recursion_fixed_context.
   assert(H:($0 ≡' $2::$0 ≡' $1::old_L_background) ⊢C $0 ≡' $2)by recursion_fixed_context.
   assert(HG:incl ZF0base($0 ≡' $2::$0 ≡' $1::old_L_background))by recursion_fixed_background.
   frew_in E ($0 ≡' $2`[↑]) H. exact H.
 - apply II,II.
   assert(E:($2 ≡' $0::$0 ≡' $1::old_L_background) ⊢C $0 ≡' $1)by recursion_fixed_context.
   assert(H:($2 ≡' $0::$0 ≡' $1::old_L_background) ⊢C $2 ≡' $0)by recursion_fixed_context.
   assert(HG:incl ZF0base($2 ≡' $0::$0 ≡' $1::old_L_background))by recursion_fixed_background.
   frew_in E ($2`[↑] ≡' $0) H. exact H.
Qed.
Print Assumptions old_recursion_fact_proof.
