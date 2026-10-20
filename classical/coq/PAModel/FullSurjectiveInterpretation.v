(** Full first-order satisfaction is preserved by a surjective interpretation
    map that commutes with functions and reflects every atomic predicate.
    Valuations are compared pointwise; no function extensionality is used. *)
From Stdlib Require Import Vectors.Vector.
From FOL Require Import FullSyntax.
Unset Implicit Arguments.

Section Transfer.
 Context {SigmaF : funcs_signature} {SigmaP : preds_signature}.
 Variables (D Q : Type) (I : @interp SigmaF SigmaP D) (J : @interp SigmaF SigmaP Q).
 Variable project : D -> Q.
 Hypothesis function_map : forall f (v : Vector.t D (ar_syms f)),
   project (@i_func _ _ D I f v) = @i_func _ _ Q J f (Vector.map project v).
 Hypothesis atom_map : forall p (v : Vector.t D (ar_preds p)),
   @i_atom _ _ D I p v <-> @i_atom _ _ Q J p (Vector.map project v).
 Hypothesis project_surjective : forall q, exists d, project d = q.

 Theorem full_surjective_eval rho xi t :
   (forall n, project (rho n) = xi n) ->
   project (@eval _ _ D I rho t) = @eval _ _ Q J xi t.
 Proof.
   induction t as [n|f v IH] in rho, xi |- *; intro HEnv.
   - exact (HEnv n).
   - cbn. rewrite function_map. f_equal. rewrite Vector.map_map.
     apply Vector.map_ext_in. intros a HA. exact (IH a HA rho xi HEnv).
 Qed.

 Theorem full_surjective_satisfaction {ff : falsity_flag} (phi : form) rho xi :
   (forall n, project (rho n) = xi n) ->
   (@sat _ _ D I ff rho phi <-> @sat _ _ Q J ff xi phi).
 Proof.
   induction phi in rho, xi |- *; intro HEnv; cbn.
   - reflexivity.
   - rewrite atom_map.
     match goal with
     | |- @i_atom _ _ _ _ _ ?left <-> @i_atom _ _ _ _ _ ?right =>
       assert (E : left = right)
     end.
     { rewrite Vector.map_map. apply Vector.map_ext_in.
       intros a HA. exact (full_surjective_eval rho xi a HEnv). }
     rewrite E. reflexivity.
   - destruct b0; rewrite (IHphi1 rho xi HEnv), (IHphi2 rho xi HEnv); reflexivity.
   - destruct q.
     + split.
       * intros H q. destruct (project_surjective q) as (d&Hd).
         apply (proj1 (IHphi (d .: rho) (q .: xi) ltac:(intros [|n]; [exact Hd|exact (HEnv n)]))).
         exact (H d).
       * intros H d.
         apply (proj2 (IHphi (d .: rho) (project d .: xi) ltac:(intros [|n]; [reflexivity|exact (HEnv n)]))).
         exact (H (project d)).
     + split.
       * intros (d&H). exists (project d).
         apply (proj1 (IHphi (d .: rho) (project d .: xi) ltac:(intros [|n]; [reflexivity|exact (HEnv n)]))).
         exact H.
       * intros (q&H). destruct (project_surjective q) as (d&Hd). exists d.
         apply (proj2 (IHphi (d .: rho) (q .: xi) ltac:(intros [|n]; [exact Hd|exact (HEnv n)]))).
         exact H.
 Qed.
End Transfer.

Print Assumptions full_surjective_eval.
Print Assumptions full_surjective_satisfaction.
