(* Copyright 2021 Pierre Courtieu
  This file is part of LibHyps. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it. *)

(** ** A specific variant of decompose. Which decomposes all logical connectives. *)

Ltac decomp_logicals h :=
  idtac;match type of h with
  | @ex _ (fun x => _) => let x' := fresh x in let h1 := fresh in destruct h as [x' h1]; decomp_logicals h1
  | @sig _ (fun x => _) => let x' := fresh x in let h1 := fresh in destruct h as [x' h1]; decomp_logicals h1
  | @sig2 _ (fun x => _) (fun _ => _) => let x' := fresh x in
                                         let h1 := fresh in
                                         let h2 := fresh in
                                         destruct h as [x' h1 h2];
                                         decomp_logicals h1;
                                         decomp_logicals h2
  | @sigT _ (fun x => _) => let x' := fresh x in let h1 := fresh in destruct h as [x' h1]; decomp_logicals h1
  | @sigT2 _ (fun x => _) (fun _ => _) => let x' := fresh x in
                                          let h1 := fresh in
                                          let h2 := fresh in
                                          destruct h as [x' h1 h2]; decomp_logicals h1; decomp_logicals h2
  | and _ _ => let h1 := fresh in let h2 := fresh in destruct h as [h1 h2]; decomp_logicals h1; decomp_logicals h2
  | iff _ _ => let h1 := fresh in let h2 := fresh in destruct h as [h1 h2]; decomp_logicals h1; decomp_logicals h2
  | or _ _ => let h' := fresh in destruct h as [h' | h']; [decomp_logicals h' | decomp_logicals h' ]
  | IF_then_else _ _ _ => let h' := fresh in destruct h as [h' | h']; [decomp_logicals h' | decomp_logicals h']
  | _ => idtac
  end.

(*
Lemma foo: (IF_then_else False True False) -> False.
Proof.
  intros H.
  decomp_logicals H.
Admitted.

Lemma foo2 : { aa:False & True  } -> False.
Proof.
  intros H.
  decomp_logicals H.
Admitted.


Lemma foo3 : { aa:False & True & False  } -> False.
Proof.
  intros H.
  decomp_logicals H.
Abort.
*)
