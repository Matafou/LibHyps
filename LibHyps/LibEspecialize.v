
Require Import LibHyps.LibHypsTactics.

(* debug *)
Module Prgoal_Notation.
  Ltac pr_goal :=
    match goal with
      |- ?g =>
        let allh := harvest_hyps revert_clearbody_all in
        (* let allh := all_hyps in *)
        idtac allh " ⊢ " g
    end.
End Prgoal_Notation.

Require Import Arith.
(* The tactics in this file use the folowing pattern, that consists in
   refining a new evar goal until being in the right scope to prove
   the premise. *)
(*
Lemma foo: forall x y : nat, (forall n m p :nat, n < m -> n <= m -> p > 0 -> False) -> False.
Proof.
  intros x y H. 
  (* On veut prouver le n <= m comme conséquence du n < m dans H. *)
  (* On crée un but dont le type n'est pas connu, et on raffine pour
     être dans le bon environnement. *)

  assert (forall n m p : nat, n < m -> n <= m).
  { admit. }
  pose proof (fun (n m p : nat) (h:n < m) => (H n m p h (H0 n m p h))).

  let ev := open_constr:(_) in
  assert (ev) as h.
  { refine (fun (n m p:nat) (h:n < m) => _).
    assert(n <= m) as hhyp.
    { now apply Nat.lt_le_incl. }
    exact(H n m p h hhyp). }
  (* Voilà! *)
Admitted.
*)  

(* Describing how each arg of a hypothesis must be treated: either
   requantify it, or evarize it, or requantify but don't use it in
   premise proofs (not sure this is needed) finally make it a subgoal.
   We don't use list for cosmetic reasons: no need for nil (since the
   list is non empty). *)
Inductive spec_args : Type :=
  ConsQuantif: spec_args -> spec_args (* re-quantify *)
| ConsEvar: spec_args -> spec_args    (* make it an evar *)
| ConsIgnore: spec_args -> spec_args  (* gnore it (useless?) *)
| ConsSubGoal: spec_args -> spec_args (* make it a subgoal *)
| SubGoalEnd: spec_args.              (* make it a subgoal, end of list. *)


Inductive int_spec_args: Type :=
| ConsEVAR: nat -> int_spec_args -> int_spec_args
| ConsGOAL: nat -> int_spec_args -> int_spec_args
| FinalGOAL: nat -> int_spec_args.


Declare Scope especialize_scope.
Delimit Scope especialize_scope with espec.
(* Local Open Scope especialize_scope. *)

Declare Scope especialize_using_scope.
Delimit Scope especialize_using_scope with euspec.
(* Local Open Scope especialize_using_scope. *)

Module SpecNotation.

  Infix "?::" := ConsEVAR (at level 60, right associativity) : especialize_scope.
  Infix "#::" := ConsGOAL (at level 60, right associativity) : especialize_scope.
  Notation "## X" := (FinalGOAL X) (at level 60) : especialize_scope.

  Notation "! X" := (ConsQuantif X) (at level 100) : especialize_using_scope.
  Notation "? X" := (ConsEvar X) (at level 100) : especialize_using_scope.
  Notation "# X" := (ConsSubGoal X) (at level 100) : especialize_using_scope.
  Notation "##" := (SubGoalEnd) (at level 100) : especialize_using_scope.

  Ltac interp_num min l :=
    lazymatch l with
      nil => fail
    | FinalGOAL ?min' =>
        match min with
          min' => constr:(SubGoalEnd)
        | _ => 
            let lres := interp_num (S min) l in
            constr:(ConsQuantif lres)
        end
    | ConsGOAL ?min' ?l' =>
        match min with
          min' =>
            let lres := interp_num (S min) l' in
            constr:(ConsSubGoal lres)
        | _ => 
            let lres := interp_num (S min) l in
            constr:(ConsQuantif lres)
        end
    | ConsEVAR ?min' ?l' =>
        match min with
          min' =>
            let lres := interp_num (S min) l' in
            constr:(ConsEvar lres)
        | _ => 
            let lres := interp_num (S min) l in
            constr:(ConsQuantif lres)
        end
    end.

End SpecNotation.
Import SpecNotation.

  (* builds the application of c to each element of l (in reversed
   order). apply t [t1;t2;t3] => (t t3 t2 t1) *)
  Ltac list_apply c l :=
    match l with
      DNil => c
    | DCons _ ?x ?l' =>
        let inside := list_apply c l' in
        let res := constr:(ltac:(exact (inside x))) in
        res
    end.

  Ltac refine_hd h largs :=
    match largs with
    | SubGoalEnd =>
        match type of h with
        | (forall x:?t, _) =>
            (* create the user subgoal *)
            let x' := fresh x in
            unshelve (evar(x':t); exact (h x'))
        end
    | ConsQuantif ?largs' => 
        match type of h with
        | (forall x:?t, _) =>
            let x':= fresh x in
            refine (fun x': t => _);
            specialize (h x');
            refine_hd h largs'
        end
    (* Fallback to evar creation *)
    (* | ConsQuantif ?largs' => refine_hd h (ConsEvar largs') *)
    | ConsEvar ?largs' => 
        match type of h with
        | (forall x:?t, _) =>
            let x' := fresh x in
            evar(x':t);
            specialize (h x');
            subst x';
            refine_hd h largs'
        end
    | ConsSubGoal ?largs' =>
        match type of h with
        | (forall x:?t, _) =>
            let x' := fresh x in
            unshelve (evar(x':t));[
                clear h 
              | specialize (h x');
                refine_hd h largs']
        end
    end.


  Ltac refine_premise_hd h largs :=
    match largs with
    | SubGoalEnd =>
        match type of h with
        | (forall x:?t, _) =>
            (* create the user subgoal *)
            let x' := fresh x in
            unshelve (evar(x':t); exact x')
        end
    | ConsQuantif ?largs' => 
        match type of h with
        | (forall x:?t, _) =>
            let x':= fresh x in
            refine (fun x': t => _);
            specialize (h x');
            refine_premise_hd h largs'
        end
    (* Fallback to evar creation *)
    (* | ConsQuantif ?largs' => refine_premise_hd h (ConsEvar largs') *)
    | ConsEvar ?largs' => 
        match type of h with
        | (forall x:?t, _) =>
            let x' := fresh x in
            evar(x':t);
            specialize (h x');
            subst x';
            refine_premise_hd h largs'
        end
    | ConsSubGoal ?largs' =>
        match type of h with
        | (forall x:?t, _) =>
            let x' := fresh x in
            unshelve (evar(x':t));[
                clear h 
              | specialize (h x');
                refine_premise_hd h largs']
        end
    end.


  (* Precondition: name is already fresh *)
  Global Ltac espec_gen H l name :=
    (* morally this evar is of type Type, don't know how to enforce this
     without having an ugly cast in goals *)
    let ev1 := open_constr:(_) in
    assert ev1 as name
    ; [
        (refine_hd H l)
      | ].

  Global Ltac eprem_gen H l name :=
    (* morally this evar is of type Type, don't know how to enforce this
     without having an ugly cast in goals *)
    let ev1 := open_constr:(_) in
    assert ev1 as name
    ; [
        (refine_premise_hd H l)
      | ].


  Ltac fresh_unfail H :=
    match constr:(True) with
    | _ => fresh H
    | _ => fresh "H_"
    end.
  Global Ltac especialize_clear H args :=
    (is_var H ; 
     let temp := fresh_unfail H in
     espec_gen H args temp; [ .. | clear H; rename temp into H ])
    + ((assert_fails (is_var(H))) ; 
       let tempH := fresh_unfail H in
       specialize H as tempH;
       let temp := fresh_unfail H in
       espec_gen tempH args temp).


  Global Ltac especialize_named H args name :=
    (is_var H ; espec_gen H args name)
    + ((assert_fails (is_var(H))) ; 
       let tempH := fresh_unfail H in
       specialize H as tempH;
       espec_gen tempH args name;
       [ .. | clear tempH ]).

  Global Ltac epremise_named H args name :=
    (is_var H ; eprem_gen H args name)
    + ((assert_fails (is_var(H))) ; 
       let tempH := fresh_unfail H in
       specialize H as tempH;
       eprem_gen tempH args name;
       [ .. | clear tempH ]).


  Global Ltac especialize_autoname H args :=
    let name := fresh_unfail H in
    espec_gen H args name.

  Global Ltac especialize_clear_autoname H args :=
    let name := fresh_unfail H in
    (* let name := fresh name "_inst" in *)
    especialize_autoname H args name.


  Tactic Notation "especialize" constr(H) "using" constr(specarg) "as" ident(idH) :=
    especialize_named H specarg idH.

  Tactic Notation "especialize" constr(H) "using" constr(specarg) :=
    especialize_clear H specarg.

  (* TODO *)
  Tactic Notation "especialize" constr(H) "using" constr(specarg) ":" ident(hprem) :=
    especialize_clear H specarg.

  Tactic Notation "assert" "premises" constr(H) "at" constr(specarg) "as" ident(idH) :=
    let specarg' := SpecNotation.interp_num 1%nat specarg in
    epremise_named H specarg' idH.


  Tactic Notation "especialize" constr(H) "at" constr(specarg) "as" ident(idH) :=
    let specarg' := SpecNotation.interp_num 1%nat specarg in
    especialize_named H specarg' idH.

  Tactic Notation "assert" "premises" constr(H) "at" constr(specarg) :=
    let specarg' := SpecNotation.interp_num 1%nat specarg in
    let idH := fresh "Hprem" in
    epremise_named H specarg' idH.

  Tactic Notation "especialize" constr(H) "at" constr(specarg) :=
    let specarg' := SpecNotation.interp_num 1%nat specarg in
    especialize_clear H specarg'.

  (* TODO *)
  Tactic Notation "especialize" constr(H) "at" constr(specarg) ":" ident(hprem) :=
    let specarg' := SpecNotation.interp_num 1%nat specarg in
    especialize_clear H specarg'.


  (* Tactic Notation "exploit" constr(H) "using" constr(specarg) "as" ident(idH) := *)
  (* prove_premises H specarg idH. *)




  Ltac check_var H :=
    (is_var(H))
    + (assert_fails(is_var(H))
       ; fail "the term " H "is not a hypothesis. To create a new hypothesis from it, please us 'as <name>'. ").



  (* SPECIALIZE WITH EVAR(S) *)
  (* Precondiion: H must already be a hyp at this point. *)
  Ltac spec_evar H var_name :=
    check_var(H);
    let idt := fresh var_name "T" in
    let id := fresh var_name in
    evar (idt : Type);
    evar (id : idt);
    specialize H with (var_name := id); subst id; subst idt.

  Tactic Notation "specevar" constr(H) "at" ident(i) "as" ident(newH) :=
    specialize H as newH;
    spec_evar newH i.

  Tactic Notation "specevar" constr(H) "at" ident(i) "as" "?" :=
    let newH := fresh "H" in
    specevar newH at i as newH.

  Ltac create_hyp_if_necessary H :=
    (assert_fails(is_var(H)); let newH := fresh_unfail H in specialize H as newH)
    + idtac.


  (* Without a name: duplicate only if c is not a hypothesis, otherwise
   specialize directly on H *)
  Tactic Notation "specevar" constr(c) "at" ident(i) :=
    create_hyp_if_necessary c;
    spec_evar c i.


  Definition eq_one (i:nat) := i = 1.
(*
Module Using.

Local Open Scope especialize_using_scope.

Lemma test_espec: forall x:nat, x = 1 -> (forall a y z:nat, a = 1 -> y = 1 -> z+y+a = 2 -> z+1 = x -> False) -> x > 1.
Proof.
  intros x hx h_eqone.
  (* specevar h_eqone at y. *)
  especialize h_eqone using (? ? ! # ##).
  + reflexivity.
  + reflexivity.
  + exfalso.
    apply h_eqone with 0.
    * reflexivity.
    * symmetry.
      assumption.
Qed.
  
Lemma test_espec': forall x:nat, x = 1 -> (forall a y z:nat, a = 1 -> y = 1 -> z+y+a = 2 -> z+1 = x -> False) -> x > 1.
Proof.
  intros x hx h_eqone.
  (* specevar h_eqone at y. *)
  especialize h_eqone using (? ? ! # ##) as h_eqonetemp.
  + reflexivity.
  + reflexivity.
  + exfalso.
    apply h_eqonetemp with 0.
    * reflexivity.
    * symmetry.
      assumption.
Qed.
  

Lemma test_espec2: forall x:nat, x = 1 -> (forall a y z:nat, a = 1 -> y = 1 -> z+y+a = 2 -> z+1 = x -> False) -> x > 1.
Proof.
  intros x hx h_eqone.
  (* specevar h_eqone at y. *)
  especialize h_eqone using (! ? ! ! ##).
  + reflexivity.
  + exfalso.
    apply h_eqone with 1 0.
    * reflexivity.
    * reflexivity.
    * symmetry.
      assumption.
Qed.
  

Lemma test_espec3: forall x:nat, x = 1 -> (forall a y z:nat, a = 1 -> y = 1 -> z+y+a = 2 -> z+1 = x -> False) -> x > 1.
Proof.
  intros x hx h_eqone.
  (* specevar h_eqone at y. *)
  especialize h_eqone using (! ? ? ! ##).
  + reflexivity.
  + exfalso.
    apply h_eqone with 1.
    * reflexivity.
    * instantiate (z:=0). reflexivity.
    * symmetry.
      assumption.
Qed.
  

Lemma test_espec4: forall x:nat, x = 1 -> (forall a y z:nat, a = 1 -> y = 1 -> z+y+a = 2 -> z+1 = x -> False) -> x > 1.
Proof.
  intros x hx h_eqone.
  (* specevar h_eqone at y. *)
  especialize h_eqone using (? ? ? ! ##).
  + reflexivity.
  + exfalso.
    apply h_eqone.
    * reflexivity.
    * instantiate (z:=0). reflexivity.
    * symmetry.
      assumption.
Qed.
  
Lemma test_espec5: forall x:nat, x = 1 -> (forall a y z:nat, a = 1 -> y = 1 -> z+y+a = 2 -> z+1 = x -> False) -> x > 1.
Proof.
  intros x hx h_eqone.
  (* specevar h_eqone at y. *)
  especialize h_eqone using (? ? ? ##).
  + reflexivity.
  + exfalso.
    apply h_eqone.
    * reflexivity.
    * instantiate (z:=0). reflexivity.
    * symmetry.
      assumption.
Qed.
  
Lemma test_espec6: forall x:nat, x = 1 -> (forall a y z:nat, a = 1 -> y = 1 -> z+y+a = 2 -> z+1 = x -> False) -> x > 1.
Proof.
  intros x hx h_eqone.
  (* specevar h_eqone at y. *)
  especialize h_eqone using (? ! ! ##).
  + reflexivity.
  + exfalso.
    apply h_eqone with 1 0.
    * reflexivity.
    * reflexivity.
    * symmetry.
      assumption.
Qed.

Lemma test_espec7: forall x:nat, x = 1 -> (forall a y z:nat, a = 1 -> y = 1 -> z+y+a = 2 -> z+1 = x -> False) -> x > 1.
Proof.
  intros x hx h_eqone.
  (* specevar h_eqone at y. *)
  especialize h_eqone using (? ! ? # ! ! ##).
  + reflexivity.
  + rewrite hx.
    instantiate (z:=0).
    reflexivity.
  + exfalso.
    apply h_eqone with 1.
    * reflexivity.
    * reflexivity.
Qed.

Lemma test_espec8: forall x:nat, x = 1 -> (forall a y z:nat, a = 1 -> y = 1 -> z+y+a = 2 -> z+1 = x -> False) -> x > 1.
Proof.
  intros x hx h_eqone.
  (* specevar h_eqone at y. *)
  especialize h_eqone using (? ! ! # ! ! ##).
  + reflexivity.
  + subst.
    rewrite Nat.add_comm in x2.
    cbn in x2.
    injection x2;intro ;assumption.
  + exfalso.
    apply h_eqone with 1 0.
    * reflexivity.
    * reflexivity.
Qed.

Lemma test_espec9: forall x:nat, x = 1 -> (forall a y z:nat, a = 1 -> y = 1 -> z+y+a = 2 -> z+1 = x -> False) -> x > 1.
Proof.
  intros x hx h_eqone.
  (* specevar h_eqone at y. *)
  especialize h_eqone using (! ! ! # ! ! ##).
  + subst.
    Fail
      (* this should fail if there are only nat hyps: *)
      ltac:(match goal with
            | H: ?t |- a = 1 =>
                match t with
                  nat => fail 1
                | _ => idtac "remaining hyp: " H ":" t 
                end
            end).
Abort.

End Using. *)


Import SpecNotation.
  Module At.
    Module Using.
      Import List.ListNotations.
      Open Scope list_scope.

      Close Scope autonaming_scope.
      Open Scope especialize_scope.
      Lemma test_espec: forall x:nat, x = 1 -> (forall a y z:nat, a = 1 -> y = 1 -> z+y+a = 2 -> z+1 = x -> False) -> x > 1.
      Proof.
        intros x hx h_eqone.
        (* specevar h_eqone at y. *)
        (* especialize h_eqone at (ConsEVAR 1 (ConsEVAR 2 (ConsGOAL 4 (FinalGOAL 5)))). *)
        assert premises h_eqone at (2?::##5) as h.
        + reflexivity.
        + exfalso.
          eapply h_eqone with (z:=0);eauto.
          subst.
          reflexivity.
Qed.



Lemma foo: False.
Proof.
  (* specialize (le_sind 0) as h. *)
  (* Set Ltac Debug. *)
  especialize (le_sind 0)  at (1?:: ##2) as h'.
  (* Set Ltac Debug. *)
  especialize (le_sind 0) at (1?:: ##2) as h.  ? P.  as hh : h.
  { admit. }
  especialize min_l at 1 as ? : ?.
  { apply (le_n O). }
  
  especialize H at 1 as hh : h.
  { reflexivity. }
  match type of h with False => idtac "OK" | _ => fail end.
  assumption.
Qed.
*)


Lemma test_espec2: forall x:nat, x = 1 -> (forall a y z:nat, a = 1 -> y = 1 -> z+y+a = 2 -> z+1 = x -> False) -> x > 1.
Proof.
  intros x hx h_eqone.
  (* specevar h_eqone at y. *)
  especialize h_eqone using (! ? ! ! ##).
  + reflexivity.
  + exfalso.
    apply h_eqonetemp with 1 0.
    * reflexivity.
    * reflexivity.
    * symmetry.
      assumption.
Qed.
  

Lemma test_espec3: forall x:nat, x = 1 -> (forall a y z:nat, a = 1 -> y = 1 -> z+y+a = 2 -> z+1 = x -> False) -> x > 1.
Proof.
  intros x hx h_eqone.
  (* specevar h_eqone at y. *)
  especialize h_eqone using (! ? ? ! ##).
  + reflexivity.
  + exfalso.
    apply h_eqonetemp with 1.
    * reflexivity.
    * instantiate (z:=0). reflexivity.
    * symmetry.
      assumption.
Qed.
  

Lemma test_espec4: forall x:nat, x = 1 -> (forall a y z:nat, a = 1 -> y = 1 -> z+y+a = 2 -> z+1 = x -> False) -> x > 1.
Proof.
  intros x hx h_eqone.
  (* specevar h_eqone at y. *)
  especialize h_eqone using (? ? ? ! ##).
  + reflexivity.
  + exfalso.
    apply h_eqonetemp.
    * reflexivity.
    * instantiate (z:=0). reflexivity.
    * symmetry.
      assumption.
Qed.
  
Lemma test_espec5: forall x:nat, x = 1 -> (forall a y z:nat, a = 1 -> y = 1 -> z+y+a = 2 -> z+1 = x -> False) -> x > 1.
Proof.
  intros x hx h_eqone.
  (* specevar h_eqone at y. *)
  especialize h_eqone using (? ? ? ##).
  + reflexivity.
  + exfalso.
    apply h_eqonetemp.
    * reflexivity.
    * instantiate (z:=0). reflexivity.
    * symmetry.
      assumption.
Qed.
  
Lemma test_espec6: forall x:nat, x = 1 -> (forall a y z:nat, a = 1 -> y = 1 -> z+y+a = 2 -> z+1 = x -> False) -> x > 1.
Proof.
  intros x hx h_eqone.
  (* specevar h_eqone at y. *)
  especialize h_eqone using (? ! ! ##).
  + reflexivity.
  + exfalso.
    apply h_eqonetemp with 1 0.
    * reflexivity.
    * reflexivity.
    * symmetry.
      assumption.
Qed.

Lemma test_espec7: forall x:nat, x = 1 -> (forall a y z:nat, a = 1 -> y = 1 -> z+y+a = 2 -> z+1 = x -> False) -> x > 1.
Proof.
  intros x hx h_eqone.
  (* specevar h_eqone at y. *)
  especialize h_eqone using (? ! ? # ! ! ##).
  + reflexivity.
  + rewrite hx.
    instantiate (z:=0).
    reflexivity.
  + exfalso.
    apply h_eqonetemp with 1.
    * reflexivity.
    * reflexivity.
Qed.

Lemma test_espec8: forall x:nat, x = 1 -> (forall a y z:nat, a = 1 -> y = 1 -> z+y+a = 2 -> z+1 = x -> False) -> x > 1.
Proof.
  intros x hx h_eqone.
  (* specevar h_eqone at y. *)
  especialize h_eqone using (? ! ! # ! ! ##).
  + reflexivity.
  + subst.
    rewrite Nat.add_comm in x2.
    cbn in x2.
    injection x2;intro ;assumption.
  + exfalso.
    apply h_eqonetemp with 1 0.
    * reflexivity.
    * reflexivity.
Qed.

Lemma test_espec9: forall x:nat, x = 1 -> (forall a y z:nat, a = 1 -> y = 1 -> z+y+a = 2 -> z+1 = x -> False) -> x > 1.
Proof.
  intros x hx h_eqone.
  (* specevar h_eqone at y. *)
  especialize h_eqone using (! ! ! # ! ! ##).
  + subst.
    Fail
      (* this should fail if there are only nat hyps: *)
      ltac:(match goal with
            | H: ?t |- a = 1 =>
                match t with
                  nat => fail 1
                | _ => idtac "remaining hyp: " H ":" t 
                end
            end).
Abort.


End At.
