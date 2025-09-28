From Stdlib Require Import String.
(* Require ident_of_string. *)
Require Import Ltac2.Ltac2.
From Ltac2 Require Import Option Constr Printf.
Import Constr.Unsafe.
Declare Scope specialize_scope.
Delimit Scope specialize_scope with spec.
Local Open Scope specialize_scope.
Require IdentParsing.

From Stdlib Require Import String Ascii.
Open Scope string_scope.
Local Set Default Proof Mode "Classic".

(* the type describing how to specialize the arguments of a hyp *)
Inductive spec_arg : Type :=
  (* This 4 are meant to be put in a exhaustive list of what to do
     with arg in order. *)
  Quantif | QuantifIgnore | SubGoal | Evar: string -> spec_arg
| QuantifAtName: string -> spec_arg (* quantify all until the hyp
                                       named (1st string), which is
                                       made a subgoal *)                   

| QuantifAtNum: nat -> spec_arg (* quantify all until the non dep
                                   natth is reached, which is made a
                                   subgoal *)
| EvarAtName: string -> string -> spec_arg (* quantify all until hyp
                                              named (1st string),
                                              which is made an evar
                                              named after the snd
                                              string. *)
| SubGoalUntilNum: nat -> spec_arg. (* make subgoals with all non dep hyp. *)

Definition spec_args := list spec_arg .

(* List storing heterogenous terms, for storing telescopes. A simple
   product could also be used. *)
(*
Inductive Depl :=
| DNil: Depl
| DCons: forall (A:Type) (x:A), Depl -> Depl.
*)

(* if H head product is dependent, call tac1, else call tac2 *)
Ltac if_is_dep_prod H tac1 tac2 :=
  (* tryif is_dep_prod H then ltac:(tac1) else ltac:(tac2). *)
  let t := type of H in
  match goal with
  | |- _ => match goal with
            | |- _ => assert t;
                      let h := fresh "__h__" in
                      intro h;
                      (tryif clear h then fail else fail 1) (* we fail in both cases to backtrack the assert*)
            | |- _ => tac2
            | |- _ => fail 2 (* don't fall back to tac1 *)
            end
  | |- _ => tac1
  end.

Ltac2 rec length_constr_string (xs : constr) : int :=
  match kind xs with
  | App _ args =>
    match Int.equal (Array.length args) 2 with
    | true => Int.add 1 (length_constr_string (Array.get args 1))
    | _ => if equal xs 'String.EmptyString then 0 else Control.throw No_value
    end
  | Constr.Unsafe.Constructor _ _ => 0
  | _ => Control.throw No_value
  end.

Ltac2 string_of_constr_string (s : constr) : string :=
  let s := eval vm_compute in ($s : String.string) in
  let ret := String.make (length_constr_string s) (Char.of_int 0) in
  let t := constr:(true) in
  let rec fill i s :=
    (match kind s with
    | App _ args =>
      (if Int.equal (Array.length args) 2 then
         (String.set ret i (match kind (Array.get args 0) with App _ b => Char.of_int (
            Int.add (if equal (Array.get b 0) t then 1 else 0) (
            Int.add (if equal (Array.get b 1) t then 2 else 0) (
            Int.add (if equal (Array.get b 2) t then 4 else 0) (
            Int.add (if equal (Array.get b 3) t then 8 else 0) (
            Int.add (if equal (Array.get b 4) t then 16 else 0) (
            Int.add (if equal (Array.get b 5) t then 32 else 0) (
            Int.add (if equal (Array.get b 6) t then 64 else 0) (
                    (if equal (Array.get b 7) t then 128 else 0)))))))))
          | _ => Control.throw No_value end);
        fill (Int.add i 1) (Array.get args 1))
      else ())
    | _ => ()
    end) in
  fill 0 s;
  ret.

Ltac if_eqstr :=
  ltac2:(ident s tac1 tac2 |-
           (if String.equal
                 (Ident.to_string (Option.get (Ltac1.to_ident ident)))
                 (string_of_constr_string (Option.get (Ltac1.to_constr s)))
            then Ltac1.apply tac1 [] 
            else Ltac1.apply tac2 []) Ltac1.run).

Ltac2 ident_of_constr_string (s : constr) := Option.get (Ident.of_string (string_of_constr_string s)).

Ltac ident_of_constr_string_cps := ltac2:(s tac |-
  Ltac1.apply tac [Ltac1.of_ident (ident_of_constr_string (Option.get (Ltac1.to_constr s)))] Ltac1.run).

Ltac evar_as_string s t := ident_of_constr_string_cps s ltac:(fun s => let s' := fresh s in evar(s':t)).


(* ESPECIALIZE INTERNAL DOC *)
(* We show here by hand what the especialize tactic does. We start
with a hypothesis H of type

H: (forall n m:nat, n<m -> n<=m -> forall p:nat, p>0 -> p+1 = m+n)

Suppose we want:

1. let the user prove that the premise (n <= m) can be proved from the
   other premise (n < m) and can thus be removed from H

2. let the user prove the premise (p > 0) for a p yet to be determined
   (evar) and remove both p and (p>0) from H.
*)
Lemma foo: forall x y : nat, (forall n m:nat, n < m -> n <= m -> forall p:nat, p > 0 -> p+1 = m+n) -> False.
Proof.

  intros x y H. 
  (* - We start from a goal evarEV with no typing constraint. *)
  let ev1 := open_constr:(_) in
  assert ev1 as newH.
  (* then we refine this unknown goal by mimick H until we reach the
  premise we want to remove: *)
  intro n. (*or refine (fun (n:nat) => _) *)
  specialize (H n).
  intro m. 
  specialize (H m).

  (* 1 more times, but more automatic *)
  match type of H with
    (forall nme:?t, _) => (intro nme) (*refine (fun nme:t => _)*); specialize (H nme)
  end.
  
  (* We want to prove (n<=m) as a consequence of (n<m) in H. So here
  instead of mimickig H we assert the premise as a new goal. *)
  assert (n<=m) as h.
  all:swap 1 2.
  (* we go on by specializing H with this new goal *)
  specialize (H h).

  (* let us make the premise p an evar and specialize H with it. *)
  evar (p:nat).
  specialize (H p);subst p.
  (* Let us make another goal for (?p > 0) *)
  assert (?p>0) as h'.
  all:swap 1 2.
  (* we go on by specializing H with this new goal *)
  specialize (H h').
  (* Now we have finished, we finish refining the unknown goal with H itself. *)
  exact H.
  (* Now we are left with 2 subgoals and the initial goal where H has
     been specialized. *)
Abort.


(* This performs the refinement of the current goal by mimicking h and
   making evars and subgoals according to args. n is the number of
   dependent product we have already met. *)
Ltac refine_hd h largs n :=
  let newn := if_is_dep_prod h ltac:(constr:(n)) ltac:(constr:(S n)) in
  (* let newn := tryif is_dep_prod h then constr:(n) else constr:(S n) in *)
  lazymatch largs with
  | nil =>  exact h
  | _ => 
      lazymatch type of h with
      | (forall (h_premis:?t) , _) =>
          let id := ident:(h_premis) in (* ltac hack, if the product was not named,
                                           then "h_premis" is taken "as is" by fresh *)
          let intronme := (*fresh*) id in
          lazymatch largs with
          | nil =>  exact h
          | cons Quantif ?largs' =>
              refine (fun intronme: t => _);
              specialize (h intronme);
              refine_hd h largs' newn
          | cons QuantifIgnore ?largs' => 
              (* let intronme := fresh x in *)
              refine (fun intronme: t => _);
              specialize (h intronme);
              clear h_premis;
              refine_hd h largs' newn
          | cons (QuantifAtName ?nme) ?largs' => 
              if_eqstr ident:(h_premis) nme
              ltac:(idtac;refine_hd h (cons SubGoal largs') n)
              ltac:(idtac;refine_hd h (cons Quantif largs) n)
          | cons (EvarAtName ?nmearg ?nameevar) ?largs' => 
              if_eqstr ident:(h_premis) nmearg
              ltac:(idtac;refine_hd h (cons (Evar nameevar) largs') n)
              ltac:(idtac;refine_hd h (cons Quantif largs) n)
          | cons (QuantifAtNum ?num) ?largs' => 
              if_is_dep_prod h
                ltac:((idtac;refine_hd h (cons Quantif largs) n))
                ltac:(idtac;tryif convert num newn
                             then refine_hd h (cons SubGoal largs') n
                             else refine_hd h (cons Quantif largs) n)
          | cons (SubGoalUntilNum ?num) ?largs' => 
              if_is_dep_prod h
                ltac:((idtac;refine_hd h (cons Quantif largs) n))
                ltac:(idtac;tryif convert num newn
                             then refine_hd h (cons SubGoal largs') n
                             else refine_hd h (cons SubGoal largs) n)
          | cons (Evar ?ename) ?largs' => 
              evar_as_string ename t;
              (* hackish: this should get the evar just created *)
              let hename := match goal with H:t|-_ => H end in
              specialize (h hename);
              subst hename;
              (* idtac "subst"; *)
              refine_hd h largs' newn
          | cons SubGoal ?largs' =>
              (unshelve evar_as_string "SubGoal" t);
              (* hackish: this should get the evar just created *)
              [ | let hename := match goal with
                                  H:t|-_ => H
                                end in
                  specialize (h hename);
                  clearbody hename;
                  (* idtac "subst"; *)
                  refine_hd h largs' newn]
          end
      | _ => idtac "Not enough products." ; fail
      end
  end.

(* initialize n to zero. *)
Ltac refine_spec h larg := refine_hd h larg 0.

(* builds the inital unknown goal, call the refining tactic, end up by
   replacing h or naming the new hyp. *)
(* Precondition: name is already fresh *)
Local Ltac espec_gen H l name clearb :=
  (* morally this evar is of type Type, don't know how to enforce this
     without having an ugly cast in goals *)
  (* idtac "espec_gen " H " " l " " name " " clearb;  *)
  let ev1 := open_constr:(_) in
  match clearb with
    true =>  
      assert ev1 as name ; [ (refine_spec H l) | clear H;try rename name into H ]
  | false =>
      assert ev1 as name; [ (refine_spec H l) | ]
  end.
  
(* ltac2 int -> constr nat *)
Ltac2 rec int_to_coq_nat n :=
  match Int.equal n 0 with
  | true => constr:(O)
  | false => let n := int_to_coq_nat (Int.sub n 1) in
             constr:(S $n)
  end.

Ltac2 int_to_constr_nat n :=
  let val := int_to_coq_nat n in
  Std.eval_vm None val.

Ltac2 rec li_to_speclist_QAU (li: int list): constr :=
  match li with
    [] => constr:(@nil spec_arg)
  | i :: l' => 
      let cl := li_to_speclist_QAU l' in
      let ci := int_to_constr_nat i in
      constr:(cons (QuantifAtNum $ci) $cl)
  end.

Ltac2 rec li_to_speclist_SAU (li: int list): constr :=
  match li with
    [] => constr:(@nil spec_arg)
  | i :: l' => 
      let cl := li_to_speclist_SAU l' in
      let ci := int_to_constr_nat i in
      constr:(cons (SubGoalUntilNum $ci) $cl)
  end.

Ltac2 rec li_to_speclist_EAU (li: ident list): constr :=
  match li with
    [] => constr:(@nil spec_arg)
  | i :: l' => 
      let cl := li_to_speclist_EAU l' in
      let istr := Ident.to_string i in
      let icstr := IdentParsing.coq_string_of_string istr in
      constr:(cons (EvarAtName $icstr $icstr) $cl)
  end.

Ltac2 occurrences_to_quantifatnum (occs:Std.occurrences): constr :=
  match occs with
  | Std.AllOccurrences => Control.zero (Tactic_failure (Some (fprintf "Not implemented yet 1")))
  | Std.AllOccurrencesBut (_) => Control.zero (Tactic_failure (Some (fprintf "Not implemented yet 2")))
  | Std.NoOccurrences => Control.zero (Tactic_failure (Some (fprintf "Not implemented yet 3")))
  | Std.OnlyOccurrences (li) => li_to_speclist_QAU li
  end.

Ltac2 occurrences_to_evaratname (li:ident list): constr := li_to_speclist_EAU li.

Ltac2 espec_at_using_ltac1_gen (h:constr) (li:int list) (occsevar:ident list) (newH: ident) (clearb:bool):unit :=
  let c1 := li_to_speclist_QAU li in
  let c2 := occurrences_to_evaratname occsevar in
  let c := Std.eval_red constr:(List.app $c2 $c1) in  
  let clearb := if clearb then constr:(true) else constr:(false) in
  ltac1:(h c newH clearb |- espec_gen h c newH clearb)
          (Ltac1.of_constr h)
          (Ltac1.of_constr c)
          (Ltac1.of_ident newH)
          (Ltac1.of_constr clearb)
.

Ltac2 espec_until_using_ltac1_gen (h:constr) (li:int list) (occsevar:ident list) (newH: ident) (clearb:bool):unit :=
  let c1 := li_to_speclist_SAU li in
  let c2 := occurrences_to_evaratname occsevar in
  let c := Std.eval_red constr:(List.app $c2 $c1) in  
  let clearb := if clearb then constr:(true) else constr:(false) in
  ltac1:(h c newH clearb |- espec_gen h c newH clearb)
          (Ltac1.of_constr h)
          (Ltac1.of_constr c)
          (Ltac1.of_ident newH)
          (Ltac1.of_constr clearb)
.

Ltac2 interp_ltac1_id_list (lid:Ltac1.t) : ident list :=
  List.map (fun x => Option.get (Ltac1.to_ident x)) (Option.get (Ltac1.to_list lid)).

Ltac2 interp_ltac1_int_list (li:Ltac1.t) : int list :=
  List.map (fun x => Option.get (Ltac1.to_int x)) (Option.get (Ltac1.to_list li)).

Ltac2 interp_ltac1_hyp (h:Ltac1.t) : constr := Option.get (Ltac1.to_constr h).

(* call Ltac2'especialize on argscoming from Ltac1 notation *)
Ltac2 call_specialize_ltac2_gen h (li:Ltac1.t) levars newh (clearb:bool) :=
  let li2 := match Ltac1.to_list li with
              None => []
            | Some _ => interp_ltac1_int_list li
            end in
  let levar2 := match Ltac1.to_list levars with
               None => []
             | Some _ => interp_ltac1_id_list levars
             end in
  espec_at_using_ltac1_gen
    (interp_ltac1_hyp h)
    li2
    levar2
    (Option.get (Ltac1.to_ident newh))
    clearb .

(* call Ltac2'especialize on argscoming from Ltac1 notation *)

Ltac2 call_specialize_until_ltac2_gen h li levars newh clearb :=
  let li2 := match Ltac1.to_list li with
               None => []
             | Some _ => interp_ltac1_int_list li
             end in
  let levar2 := match Ltac1.to_list levars with
                  None => []
                | Some _ => interp_ltac1_id_list levars
                end in
  if Int.gt (List.length li2) 1
  then
    (* msgi (List.length li'); *)
    Control.zero (Tactic_failure (Some (fprintf "In 'specialize X until I', I must be a singleton.")))
  else 
    espec_until_using_ltac1_gen (interp_ltac1_hyp h) li2 levar2
         (Option.get (Ltac1.to_ident newh)) clearb.

Ltac2 call_specialize_until_ltac2_no_evar_gen h li newh clearb :=
  let li' := interp_ltac1_int_list li in
  if Int.gt (List.length li') 1
  then
    (* msgi (List.length li'); *)
    Control.zero (Tactic_failure (Some (fprintf "In 'specialize X until I', I must be a singleton.")))
  else 
    espec_until_using_ltac1_gen (interp_ltac1_hyp h) li' []
         (Option.get (Ltac1.to_ident newh)) clearb.

Ltac gen_hyp_name h := lazymatch goal with
                       | |- _ => let _ := is_var h in fresh h "_spec_"
                       | |- _ => fresh "H_spec_"
                       end.
Ltac dummy_term := constr:(Prop).


(* ESPECIALIZE AT *)
(* ********************* *)
Tactic Notation "especialize" constr(h) "with" ne_ident_list(levars) "at" ne_integer_list(li) "as" ident(newH) :=
  let tac := ltac2:(h li levars newH |- call_specialize_ltac2_gen h li levars newH false) in
  tac h li levars newH.

Tactic Notation "especialize" constr(h) "at" ne_integer_list(li) "with" ne_ident_list(levars) "as" ident(newH) :=
  let tac := ltac2:(h li levars newH |- call_specialize_ltac2_gen h li levars newH false) in
  tac h li levars newH.

(* ********************* *)
Tactic Notation "especialize" constr(h) "at" ne_integer_list(li) "with" ne_ident_list(levars) :=
  let tac := ltac2:(h li levars newH |- call_specialize_ltac2_gen h li levars newH true) in
  let dummy_id := gen_hyp_name h in
  tac h li levars ident:(dummy_id).

Tactic Notation "especialize" constr(h) "with" ne_ident_list(levars) "at" ne_integer_list(li) :=
  let tac := ltac2:(h li levars newH |- call_specialize_ltac2_gen h li levars newH true) in
  let dummy_id := gen_hyp_name h in
  tac h li levars ident:(dummy_id).

(* ********************* *)

Tactic Notation "especialize" constr(h) "with" ne_ident_list(levars) "as" ident(newH) :=
  let tac := ltac2:(h li levars newH |- call_specialize_ltac2_gen h li levars newH false) in
  let li := dummy_term in       (* something that is not a list. *)
  tac h li levars newH.

(* ********************* *)
Tactic Notation "especialize" constr(h) "at" ne_integer_list(li) "as" ident(newH) :=
    let tac := ltac2:(h li levars newH |- call_specialize_ltac2_gen h li levars newH false) in
    let levars := dummy_term in       (* something that is not a list. *)
    tac h li levars newH.

(* ********************* *)
Tactic Notation "especialize" constr(h) "with" ne_ident_list(levars) :=
  let tac := ltac2:(h li levars newH |- call_specialize_ltac2_gen h li levars newH true) in
  let li := dummy_term  in       (* something that is not a list. *)
  let dummy_id := gen_hyp_name h in
  tac h li levars ident:(dummy_id).

(* ********************* *)
Tactic Notation "especialize" constr(h) "at" ne_integer_list(li) :=
    let tac := ltac2:(h li levars newH |- call_specialize_ltac2_gen h li levars newH true) in
    let levars := dummy_term in       (* something that is not a list. *)
    let dummy_id := gen_hyp_name h in
    tac h li levars ident:(dummy_id).



(* ESPECIALIZE UNTIL *)
(* ********************* *)
Tactic Notation "especialize" constr(h) "until" ne_integer_list(li) "with" ne_ident_list(levars)  "as" ident(newH) :=
  let tac := ltac2:(h li levars newH |- call_specialize_until_ltac2_gen h li levars newH false) in
  tac h li levars newH.

(* Strangely putting "with" before "until" is not recognized at
   parsing. Probably because "until" is not a keyword.
   Error: Syntax error: [ltac_use_default] expected after [tactic] (in
   [tactic_command]). *)
 Tactic Notation "especialize" constr(h) "with" ne_ident_list(levars) "until" ne_integer_list(li) "as" ident(newH) :=
  let tac := ltac2:(h li levars newH |- call_specialize_until_ltac2_gen h li levars newH false) in
  tac h li levars newH.

Tactic Notation "especialize" constr(h) "until" ne_integer_list(li) "with" ne_ident_list(levars) "as" "?" :=
  let tac := ltac2:(h li levars newH |- call_specialize_until_ltac2_gen h li levars newH false) in
  let nme := gen_hyp_name h in
  tac h li levars ident:(nme).


(* "with" must be first, probably because it is not a keyword: *)
Tactic Notation "especialize" constr(h) "until" ne_integer_list(li) "with" ne_ident_list(levars) :=
  let tac := ltac2:(h li levars newH |- call_specialize_until_ltac2_gen h li levars newH true) in
  let nme := gen_hyp_name h in
  tac h li levars ident:(nme).

(* "with" must be first, probably because it is not a keyword: *)
Tactic Notation "especialize" constr(h) "until" ne_integer_list(li) "as"  ident(newH) :=
  let tac := ltac2:(h li levars newH |- call_specialize_until_ltac2_gen h li levars newH false) in
  let levars := dummy_term in
  tac h li levars ident:(newH).

(* "with" must be first, probably because it is not a keyword: *)
Tactic Notation "especialize" constr(h) "until" ne_integer_list(li) "as"  "?" :=
  let tac := ltac2:(h li levars newH |- call_specialize_until_ltac2_gen h li levars newH false) in
  let nme := gen_hyp_name h in
  let levars := dummy_term in
  tac h li levars ident:(nme).

(* "with" must be first, probably because it is not a keyword: *)
Tactic Notation "especialize" constr(h) "until" ne_integer_list(li) :=
  let tac := ltac2:(h li levars newH |- call_specialize_until_ltac2_gen h li levars newH true) in
  let nme := gen_hyp_name h in
  let levars := dummy_term in
  tac h li levars ident:(nme).


(* tests *)
Definition hidden_product := forall i j :nat, i+1=j -> i+1=j -> i+1=j.

Lemma foo: forall x y : nat,
    (forall (n m p :nat) (hhh:n < m) (iii:n <= m),
        p > 0
        -> p > 2
        -> p > 1
        -> hidden_product) -> False.
Proof.
  intros x y H. 

  especialize H at 2;
    [ now apply PeanoNat.Nat.lt_le_incl | match goal with | |- False => idtac end;
                                          match type of H with forall (n:_) (m:_) (p:_), n < m -> _ => idtac end ].
  Undo 1.
  especialize H at 2 as h;
    [ now apply PeanoNat.Nat.lt_le_incl | match goal with | |- False => idtac end;
                                          match type of h with forall (n:_) (m:_) (p:_), n < m -> _ => idtac end ].
  Undo 1.
  especialize H with p;
    [ match goal with | |- False => idtac end; match type of H with forall (n:_) (m:_), n < m -> _ => idtac end ].
  Undo 1.
  especialize H with n p;
    [ match goal with | |- False => idtac end; match type of H with forall (m:_), _ < m -> _ => idtac end ].
  Undo 1.
  especialize H with p as h;
    [ match goal with | |- False => idtac end; match type of h with forall (n:_) (m:_), n < m -> _ => idtac end ].
  Undo 1.
  especialize H with n p as h;
    [ match goal with | |- False => idtac end; match type of h with forall (m:_), _ < m -> _ => idtac end ].
  Undo 1.

  especialize H at 4 with p;[
      match goal with h: ?n < ?m , h':?n <= ?m, H'':?p > 0 |- ?p > 2 => idtac end
    | match goal with |- False => idtac end; match type of H with forall n m, (n < m) -> _ => idtac end ].
  Undo 1.
  especialize H at 3 with n p;
    [ match goal with | h: ?n < ?m , h':?n <= ?m |- ?p > 0 => is_evar p end
    | match goal with | |- False => idtac end; match type of H with forall (m:_), _ < m -> _ => idtac end ].
  Undo 1.
  especialize H  with p at 3;
    [ match goal with | h: ?n < ?m , h':?n <= ?m |- ?p > 0 => is_evar p end
    | match goal with | |- False => idtac end; match type of H with forall (n:_) (m:_), n < m-> _ => idtac end ].
  Undo 1.
  especialize H with n p at 3;
    [ match goal with | h: ?n < ?m , h':?n <= ?m |- ?p > 0 => is_evar p end
    | match goal with | |- False => idtac end; match type of H with forall (m:_), _ < m -> _ => idtac end ].
  Undo 1.

  especialize H at 2 with p as h2;
    [ match goal with H:?n < ?m |- ?n <= ?m => idtac end
    | match goal with |- False => idtac end;
      match type of h2 with forall n m, (n < m) -> _ => idtac end ].
  Undo 1.
  especialize H with p at 2 as h2;
    [ match goal with H:?n < ?m |- ?n <= ?m => idtac end
    | match goal with |- False => idtac end;
      match type of h2 with forall n m, (n < m) -> _ => idtac end ].
  Undo 1.


  especialize H until 2 with p as h ;
    [ match goal with |- ?n < ?m => idtac end
    | match goal with H:?n < ?m  |- ?n <= ?m => idtac end
    | match goal with |- False => idtac end;
      match type of h with forall n m, (?q > _) -> _ => idtac end
    ].
  Undo 1.
(* This syntax ("with" before "until") does not work due to "until" not being a keyword. *)
(*  especialize H with p until 2 as h ;
    [ match goal with |- ?n < ?m => idtac end
    | match goal with H:?n < ?m  |- ?n <= ?m => idtac end
    | match goal with |- False => idtac end;
      match type of h with forall n m, (?q > _) -> _ => idtac end
    ].
  Undo 1. *)
  rename H into Hyp;
  especialize Hyp until 2 with p as ?;
    [ match goal with |- ?n < ?m => idtac end
    | match goal with H:?n < ?m  |- ?n <= ?m => idtac end
    | match goal with |- False => idtac end;
      match type of Hyp_spec_ with forall n m, (?q > _) -> _ => idtac end
    ].
  Undo 1.
  especialize H until 2 as h;
    [ match goal with |- ?n < ?m => idtac end
    | match goal with H:?n < ?m  |- ?n <= ?m => idtac end
    | match goal with |- False => idtac end;
      match type of h with forall n m p, (?q > _) -> _ => idtac end ].
  Undo 1.
  rename H into hyp;
  especialize hyp until 2 as ?;
    [ match goal with |- ?n < ?m => idtac end
    | match goal with H:?n < ?m  |- ?n <= ?m => idtac end
    | match goal with |- False => idtac end;
      match type of hyp_spec_ with forall n m p, (?q > _) -> _ => idtac end ].
  Undo 1.
  especialize H until 2;[
      match goal with |- ?n < ?m => idtac end
    | match goal with H:?n < ?m  |- ?n <= ?m => idtac end
    | match goal with |- False => idtac end;
      match type of H with forall n m p, (?q > _) -> _ => idtac end ].
  Fail Check h.
  Undo 1.
  especialize H until 3 with n p;
    [ match goal with | |- ?n < ?m => idtac end
    | match goal with | h: ?n < ?m  |- ?n <= ?m => idtac end
    | match goal with | h: ?n < ?m , h':?n <= ?m |- ?p > 0 => idtac end
    | match goal with | |- False => idtac end].
  Undo 1.


  especialize H at 2 4 with n m.
  1: match goal with
       |- ?lft <= ?rght => is_evar lft; is_evar rght
     end.
  2: match goal with
       H: p > 0 , H':?lft <= ?rght |- p > 2 => is_evar lft; is_evar rght
     end.
  3: match goal with
       H: forall p:nat, ?lft < ?rght -> p > 0 -> p > 1 -> _ |- False => is_evar lft; is_evar rght
     end.
  Undo 4.

Abort.




Lemma foo': forall x y : nat,
    (forall (n m p :nat) (hhh:n < m) (iii:n <= m),
        p > 0
        -> p > 0
        -> p > 0
        -> p > 0
        -> p > 0
        -> p > 0
        -> p > 0
        -> p > 0
        -> p > 0
        -> p > 0
        -> p > 0
        -> p > 0
        -> p > 0
        -> p > 0
        -> p > 0
        -> p > 0
        -> p > 2
        -> p > 1
        -> hidden_product) -> False.
Proof.
  intros x y H. 
  especialize H at 19 20 with p;[ | | ]; [ 
      (* test generated names *)
      match type of h_premis with
        _> _ => idtac
      end;
      match goal with
        hhh : ?n < ?m, iii : ?n <= ?m |- _ > 2 => idtac
      end
    |  match goal with
         hhh : ?n < ?m, iii : ?n <= ?m |- _ > 1 => idtac
       end
    |  match goal with
       | |- False => idtac
       end ].
  Undo 1.
Abort.



(* Experimenting a small set of tactic to manipulate a hyp: *)
(*
Ltac quantify H :=
  match type of H with
    (forall x:?t, _) => refine (fun (x:t) => _); specialize (H x)
  end.

Ltac evary H :=
  match type of H with
    (forall x:?t, _) => evar (x:t); specialize (H x);subst x
  end.

Ltac goaly H :=
  match type of H with
    (forall x:?t, _) => [> assert (x:t); [ | specialize (H x)]]
  end.
  
Ltac stopy H := exact H.
Ltac start name :=
  let ev1 := open_constr:(_) in
  assert ev1 as name.

Lemma foo: forall x y : nat,
    (forall (n m p :nat) (hhh:n < m) (iii:n <= m), p > 0 -> p+m=n) -> False.
Proof.
  intros x y H. 
  start newH.
  quantify H.
  quantify H.
  quantify H.
  quantify H.
  goaly H.
  { now apply PeanoNat.Nat.lt_le_incl. }
  stopy H.
Abort.
*)  
  
