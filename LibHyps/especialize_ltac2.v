From Stdlib Require Import String.
Require ident_of_string.
Require Import Ltac2.Ltac2.
From Ltac2 Require Import Option Constr Printf.
Import Constr.Unsafe.
Declare Scope specialize_scope.
Delimit Scope specialize_scope with spec.
Local Open Scope specialize_scope.

From Stdlib Require Import String Ascii.
Open Scope string_scope.
Local Set Default Proof Mode "Classic".

(*
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


Local Ltac2 tag_info s := (String.concat "" [ "<infomsg>"; s; "</infomsg>" ]).
Local Ltac2 tag_msg m := Message.concat
                     (Message.concat (Message.of_string "<infomsg>") m)
                     (Message.of_string "</infomsg>").
Local Ltac2 str_to_msg s := tag_msg (Message.of_string s).
Local Ltac2 int_to_msg i := tag_msg (Message.of_int i).
Local Ltac2 id_to_msg id := tag_msg (Message.of_ident id).
Local Ltac2 constr_to_msg c := tag_msg (Message.of_constr c).

Local Ltac2 msgs s := Message.print (str_to_msg s).
Local Ltac2 msgi i := Message.print (int_to_msg i).
Local Ltac2 msgc c := Message.print (constr_to_msg c).
Local Ltac2 msgid id := Message.print (id_to_msg id).


Ltac2 pr_binder () (b:binder) :=
  let nme:ident option := Binder.name b in
  let typ:constr := Binder.type b in
  fprintf "(%I:%t)" (Option.get nme) typ.
*)

(* the type describing how to specialize the arguments of a hyp *)
Inductive spec_arg : Type :=
  (* This 4 are meant to be put in a exhaustive list of what to do
  with arg in order. *)
  Quantif | QuantifIgnore | SubGoal | Evar: string -> spec_arg

(* quantify everything until the hyp named after the string, which is
   made a subgoal *)
| QuantifAtName: string -> spec_arg

(* thisquantify everything until the non dep num is reached, which is
made a subgoal *)
| QuantifAtNum: nat -> spec_arg

(* (* quantify everything until the hyp named after the string, which is
   made an evar *) *)
| EvarAtName: string -> string -> spec_arg

(* make subgoals with all non dep hyp. *)
| SubGoalUntilNum: nat -> spec_arg
.

Definition spec_args := list spec_arg .

(* List storing heterogenous terms, for storing (tele(scopes). A
   simple product could also be used. *)
Inductive Depl :=
| DNil: Depl
| DCons: forall (A:Type) (x:A), Depl -> Depl.


(* - We start from a goal evarEV with no typing constraint.

    h: forall x y z, P x -> ...
    ========================
    ?EV

    subgoal 2
    h: forall x y z, P x -> ...
    ========================
    old goal
    

  - We refine it to have the same products at head than h, until we
    reach the aimed hypothesis

    h: P x -> ...
    x: ...   y: ...   z: ...
    ========================
    ?EV

  - then we do 2 things
    - create a goal USERGOAL for this hyp
    - conclude EV (and fix its type) by applying h to USERGOAL

    subgoal 1
    x: ...   y: ...   z: ...
    ==========================
    P x

    subgoal 2:
    h: forall x y z, P x -> ...
    hEV: forall x y z, ...
    ==========================
    old goal

   Refines a non specified goal (an evar) to prove the specialized
   version of h. The idea is to use (fun x y z => (?ev x y z)) as the
   argument being instnaciated, where ?ev will be the new goal

 larg is the specidication of what to do with each arg, larg2 is the
   accumulator *)


(* Illustrating the idea on an example: *)
(*
Ltac2 create_evar_goal (nme:ident) :=
  let ev:ident := Fresh.in_goal @__h__ in (* this uses base name "h" *)
  (* Std.pose (Some(@h)) constr:(Type). *)
  epose _ as $ev;
  let cev := Control.hyp ev in
  let h' := Fresh.in_goal nme in
  assert($h': $cev);subst $ev.

(* in ltac1 this amounts to refine (fun (id:typ), _ ) where (id:typ)
   is the head produt's bider of h. FIXME: simplifiy this code? *)
Ltac2 quantify h :=
  let hcstr := Control.hyp h in
  let th := Constr.type hcstr in
  printf "<infomsg>inter hyp: %I (%t) : %t</infomsg>" h hcstr th ;
  let bnder := match kind th with
               | Prod bnder _ => bnder
               | _ => Control.zero (Tactic_failure (Some (fprintf "goal is not a product.")))
               end in
  msgs "post bnder" ;
  printf "<infomsg>binder = %a</infomsg>" pr_binder bnder;
  let nme:ident := Option.get (Binder.name bnder) in
  printf "<infomsg>name = %I</infomsg>" nme;
  let typ:constr := Binder.type bnder in
  printf "<infomsg>type = %t</infomsg>" typ;
  (unshelve (
       msgs "in unshelve" ;  
       let t:constr := Constr.in_context nme typ (fun () => ()) in
       let tt := (Constr.type t) in
       (printf "<infomsg>t := = %t : %t</infomsg>" t tt);
       msgs "post in_context" ;  
       (* let t:constr := open_constr:(_) in *)
       (Control.refine (fun () => t));
       (Control.enter (fun () => msgs "post refine")))
   (* > [  Control.shelve()| ] *)
  )
  (* let cnme := Control.hyp nme in *)
  (* specialize ($hcstr $cnme) *)
.
*)
(*
Lemma foo: forall x y : nat, (forall n m p :nat, n < m -> n <= m -> p > 0 -> p+1 = m+n) -> False.
Proof.

  intros x y H. 


  (* On veut prouver le n <= m comme conséquence du n < m dans H. *)
  (* On crée un but dont le typ#e n'est pas connu, et on raffine pour
     être dans le bon environnement. *)

  (* assert (forall n m p : nat, n < m -> n <= m). *)
  (* { admit. } *)
  (* pose proof (fun (n m p : nat) (h:n < m) => (H n m p h (H0 n m p h))). *)

  (* let arg_i := Fresh.in_goal @h in (* this uses base name "h" *) *)
  (create_evar_goal @h).
  quantify @H.
  2:specialize (H n).
  2:specialize (H n).
  2:quantify @H.
  
  specialize (H m).  
  quantify @H.
  specialize (H p).
  
  assert (n<m) as ccl > [ | exact (H ccl) ].
  { admit. }
  exact (H ccl).

  
  Control.shelve().
  Unshelve.
shelve_unifiable.
  
  2:{
    specialize (H n).
    quantify @H.
  
  quantify ident:(H).
  quantify @H.

  let t:constr := Constr.in_context ident:(foo) typ (fun () => ()) in
  ().



 > [ () | specialize (H n) | ].


  epose _ as hole_name;
  let hcstr := Control.hyp @H in
  let th := Constr.type hcstr in
  (* let cev := Control.hyp @hole_name in *)
  let bnder := 
    match Unsafe.kind th with
    | Unsafe.Prod bnder _ => bnder
    | _ => Control.zero (Tactic_failure (Some (fprintf "hypothesis is not a product.")))
    end in
  printf "bnder = %a" pr_binder bnder;
  let thole := Option.get (Control.hyp_value @hole_name) in
  match kind thole with
  | Unsafe.Evar evar _ =>
      let open_cstr:constr := make (Unsafe.Lambda bnder thole) in
      printf "open_cstr = %t" open_cstr;
      printf "thole = %t" thole;
      (* unfold @hole_name; *)
      ltac1:(refine $open_cstr)
      (* Ltac1.apply (tac ()) [open_cstr] Ltac1.run *)
      (* Control.new_goal evar *)
  | _ => Control.zero (Tactic_failure (Some (fprintf "???")))
  end.

(*
;
  Control.enter (fun () => 
                   (* Control.new_goal thole; *)
                   printf "%t" thole)*)
    
    (* Control.refine (fun () => constr:(fun (n:nat) =>_)). *)
  (* quantify ident:(H). *)
  
  


  (* ltac1:(refine (fun (n m p:nat) => _)). *)
  Control.refine (fun _ => open_constr:(fun (n m p:nat) => _));Control.shelve_unifiable().
  specialize (H n m p).
  

  let h' := Fresh.in_goal @hh in
  assert($h':__h__);subst __h__.
 

  let ev:ident := Fresh.in_goal @h in (* this uses base name "h" *)
  (* Std.pose (Some(@h)) constr:(Type). *)
  epose _ as $ev; (* _ gives a new evar, use '_ or open_constr:(_) in other contexts *)
  let h' := Fresh.in_goal @hh in
  assert($h':h);subst h.

  let ev := Fresh.in_goal @h in (* this uses base name "h" *)
  epose _ as $ev; (* _ gives a new evar, use '_ or open_constr:(_) in other contexts *)
  Control.new_goal ev.
  evar xxx.

  ltac1:(let ev := open_constr:(_) in
        assert (ev) as h).
  ltac1:(refine (fun (n m p:nat) => _)).
  specialize (H n m p).

  assert (n < m) as h1.
  all:Control.focus 2 2 (fun () => specialize (H h1)).
  all:swap 1 2.
  specialize (H h1).
  assert (n <= m) as h2.
  all:swap 1 2.
  specialize (H h2).
  assert (p > 0) as h3.
  all:swap 1 2.
  specialize (H h3).
*)  

(*
Ltac is_dep_prodOLD H :=
  let t := type of H in
  match goal with
  | |- _ => assert t;
            let h := fresh "__h__" in
            intro h; (tryif clear h then fail 1 else fail)
  | |- _ => idtac
  end.
(* This uses the ltac 2 counterpart *)
Ltac2 call_is_dep_prod_ltac2 (h:Ltac1.t) :=
  let h':ident := Option.get (Ltac1.to_ident h) in
  if ident_of_string.is_dep_prod h' then ()
  else Control.zero (Tactic_failure (Some (fprintf "not dependent"))).

Tactic Notation "is_dep_prod" hyp(h) :=
  let tac := ltac2:(h |- call_is_dep_prod_ltac2 h) in
  tac h.

Goal (forall n m p , n < m -> p =0) -> (1 < 2 -> 3<4 -> False) -> False.
  intros H H'. 
(* Why does this only work for these: *)
  tryif is_dep_prod H then idtac "YES" else idtac "NO".
  tryif is_dep_prod H' then idtac "YES" else idtac "NO".
  (* but not for these *)
  let c1 := constr:(1) in
  let c2 := constr:(2) in

  let x := tryif is_dep_prod H then c1 else c2 in
  assert (forall n, n = x).


Abort.
*)
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

Ltac refine_hd h largs n :=
  let newn := if_is_dep_prod h ltac:(constr:(n)) ltac:(constr:(S n)) in
  (* let newn := tryif is_dep_prod h then constr:(n) else constr:(S n) in *)
  lazymatch largs with
  | nil =>  exact h
  | _ => 
      lazymatch type of h with
      | (forall (x:?t) , _) =>
          lazymatch largs with
          | nil =>  exact h
          | cons Quantif ?largs' => 
              refine (fun x: t => _);
              specialize (h x);
              refine_hd h largs' newn
          | cons QuantifIgnore ?largs' => 
              refine (fun x: t => _);
              specialize (h x);
              clear x;
              refine_hd h largs' newn
          | cons (QuantifAtName ?nme) ?largs' => 
              ident_of_string.if_eqstr ident:(x) nme
              ltac:(idtac;refine_hd h (cons SubGoal largs') n)
              ltac:(idtac;refine_hd h (cons Quantif largs) n)
          | cons (EvarAtName ?nmearg ?nameevar) ?largs' => 
              ident_of_string.if_eqstr ident:(x) nmearg
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
              ident_of_string.evar_as_string ename t;
              (* hackish: this should get the evar just created *)
              let hename := match goal with H:t|-_ => H end in
              specialize (h hename);
              subst hename;
              (* idtac "subst"; *)
              refine_hd h largs' newn
          | cons SubGoal ?largs' =>
              (unshelve ident_of_string.evar_as_string "SubGoal" t);
              (* hackish: this should get the evar just created *)
              [ | let hename := match goal with
                                  H:t|-_ => H
                                end in
                  specialize (h hename);
                  subst hename;
                  (* idtac "subst"; *)
                  refine_hd h largs' newn]
          end
      | _ => idtac "Not enough products." ; fail
      end
  end.



Ltac refine_spec h larg := refine_hd h larg 0.

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
(*
  (* idtac "espec_gen name :=" name;  *)
  assert ev1 as name
  ; [
      (refine_spec H l)
    | 
    match clearb with
      true => 
        clear H;try rename name into H
    | false _ =>
        idtac "ICI false";        
        idtac
    end
    ]. *)
  
Local Ltac especialize_clear H args :=
  let dummy_name := fresh "__" in
  espec_gen H args dummy_name true.

(*
(* Interpretation of strings "fffg?x" *)
Definition nat_of_nth_char (s:string) (i:nat): option nat :=
  let c := String.get i s in
  match c with
    Some ("0"%char) => Some 0%nat
  | Some ("1"%char) => Some 1
  | Some ("2"%char) => Some 2
  | Some ("3"%char) => Some 3
  | Some ("4"%char) => Some 4
  | Some ("5"%char) => Some 5
  | Some ("6"%char) => Some 6
  | Some ("7"%char) => Some 7
  | Some ("8"%char) => Some 8
  | Some ("9"%char) => Some 9
  | _ => None
  end.
  
Fixpoint nat_of_string_rec (s:string) (i:nat) {struct i}: option nat :=
  match i with
    0 => Some 0
  | S i' => 
      match nat_of_nth_char s i' with
        None => None
      | Some n =>
          match nat_of_string_rec s i' with
          | Some res => Some (10 * res + n)
          | None => None
          end
      end
  end
.

Definition nat_of_string (s:string) :=
  nat_of_string_rec s (String.length s).


Eval compute in (nat_of_string "12").


(* bulds a spec arg list from the string s. *)
Fixpoint interp_specialize (s:string): spec_args :=
  match s with
  | "" => nil
  | String " "%char s' => interp_specialize s'
  | String "f"%char s' => cons Quantif (interp_specialize s')
  | String "i"%char s' => cons QuantifIgnore (interp_specialize s')
  | String "g"%char s' => cons SubGoal (interp_specialize s')
  | String "?"%char s' =>
        let (nme,s'') := extract_word s' in
        cons (Evar (string_of_list_ascii nme)) s''
  | String "-"%char ( String ">"%char s') =>
        let (nme,s'') := extract_word s' in
        match nat_of_string (string_of_list_ascii nme) with
          None => cons (QuantifAtName (string_of_list_ascii nme)) s''
        | Some n => cons (QuantifAtNum n) s''
        end
  | _ => nil             (* fixme *)
  end
(* extract the first word of s and the name of the evar and the remaining string. *)
with extract_word (s:string): (list Ascii.ascii * spec_args) :=
       match s with
       | "" => (nil,nil)
       | String " "%char s' => (nil, interp_specialize s')
       | String c s' => 
           let '(nme,s'') := extract_word s' in
           (cons c nme, s'')
       end.


Eval compute in (interp_specialize "->a ->2").
*)
(*
Ltac espec_string H s idH :=
  let specarg := constr:(interp_specialize s) in
  let specarg := eval compute in specarg in
    espec_gen H specarg idH.

Ltac espec_clear_string H s :=
  let specarg := constr:(interp_specialize s) in
  let specarg := (eval compute in specarg) in
  especialize_clear H specarg.


Require Import List.
Import ListNotations.

#[global]Tactic Notation "especialize" constr(H) constr(specarg) "as" ident(idH) :=
  espec_string H specarg idH.

(* permut args *)
(* #[global]Tactic Notation "especialize"  constr(H) "as" ident(idH) "at" constr(specarg)  := *)
  (* especialize H specarg as idH. *)

#[global]Tactic Notation "especialize" constr(H) constr(specarg) :=
  espec_clear_string H specarg.

#[global]Tactic Notation "especialize" constr(H) "at" constr(n1) :=
  especialize_clear H [QuantifAtNum n1].
*)

(* ltac2 int -> constr nat *)
Ltac2 rec int_to_coq_nat n :=
  match Int.equal n 0 with
  | true => constr:(O)
  | false => let n := int_to_coq_nat (Int.sub n 1) in
             constr:(S $n)
  end.

Ltac2 int_to_constr_nat' n :=
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

Require Import IdentParsing.

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

Ltac2 espec_at (h:constr) (occs:Std.occurrences) :=
  let c := occurrences_to_quantifatnum occs in
  ltac1:(h c |- especialize_clear h c) (Ltac1.of_constr h) (Ltac1.of_constr c).

Ltac2 espec_at_using (h:constr) (occs:Std.occurrences) (occsevar:ident list) :=
  let c1 := occurrences_to_quantifatnum occs in  
  let c2 := occurrences_to_evaratname occsevar in
  let c := Std.eval_red constr:(List.app $c2 $c1) in
  ltac1:(h c |- especialize_clear h c) (Ltac1.of_constr h) (Ltac1.of_constr c).


(* Ltac2 Notation "especialize" h(constr) occs(occurrences) := *)
(*   espec_at_using h occs []. *)

(* Ltac2 Notation "especialize" h(constr) occs(occurrences) "evar" levars(list1(ident)):= *)
(*   espec_at_using h occs levars. *)

(* Ltac2 Notation "especialize" h(constr) "using" levars(list1(ident)) occs(occurrences) := *)
(*   espec_at_using h occs levars. *)


(*
Ltac2 espec_until_using_ltac1_gen (h:constr) (li:int list) (occsevar:ident list) (newH: ident opt) (clearb:bool):unit :=
  match identopt,clearb with
  | false => 
  end

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
*)
(* Ltac2 tac1 (li:Ltac1.t list option) := (). *)
Ltac2 espec_at_ltac1 (h:constr) (li:int list) :=
  let cl := li_to_speclist_QAU li in
  ltac1:(h c |- especialize_clear h c) (Ltac1.of_constr h) (Ltac1.of_constr cl).

Ltac2 espec_at_using_ltac1 (h:constr) (li:int list) (occsevar:ident list):unit :=
  let c1 := li_to_speclist_QAU li in
  let c2 := occurrences_to_evaratname occsevar in
  let c := Std.eval_red constr:(List.app $c2 $c1) in
  
  ltac1:(h c |- especialize_clear h c)
          (Ltac1.of_constr h)
          (Ltac1.of_constr c)
.


Ltac2 espec_at_using_ltac1_gen (h:constr) (li:int list) (occsevar:ident list) (newH: ident) (clearb:bool):unit :=
  let c1 := li_to_speclist_QAU li in
  let c2 := occurrences_to_evaratname occsevar in
  let c := Std.eval_red constr:(List.app $c2 $c1) in  
  let clearb := constr:(false) in
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
Ltac2 call_specialize_ltac2_nousing h li :=
  espec_at_using_ltac1 (interp_ltac1_hyp h) (interp_ltac1_int_list li) [].

(* call Ltac2'especialize on argscoming from Ltac1 notation *)
Ltac2 call_specialize_ltac2 h li levars :=
  espec_at_using_ltac1
    (interp_ltac1_hyp h)
    (interp_ltac1_int_list li)
    (interp_ltac1_id_list levars).

(* call Ltac2'especialize on argscoming from Ltac1 notation *)
Ltac2 call_specialize_ltac2_gen h li levars newh clearb :=
  espec_at_using_ltac1_gen
    (interp_ltac1_hyp h)
    (interp_ltac1_int_list li)
    (interp_ltac1_id_list levars)
    (Option.get (Ltac1.to_ident newh))
    clearb.

(* call Ltac2'especialize on argscoming from Ltac1 notation *)

Ltac2 call_specialize_until_ltac2_gen h li levars newh clearb :=
  let li' := interp_ltac1_int_list li in
  if Int.gt (List.length li') 1
  then
    (* msgi (List.length li'); *)
    Control.zero (Tactic_failure (Some (fprintf "In 'specialize X until I', I must be a singleton.")))
  else 
    espec_until_using_ltac1_gen (interp_ltac1_hyp h) li' (interp_ltac1_id_list levars)
         (Option.get (Ltac1.to_ident newh)) clearb.


Tactic Notation "especialize" constr(h) "using" ne_ident_list(levars) "at" ne_integer_list(li)
  "as" ident(newH) :=
  let tac := ltac2:(h li levars newH |- call_specialize_ltac2_gen h li levars newH false) in
  tac h li levars newH.

Tactic Notation "especialize" constr(h) "at" ne_integer_list(li) "using" ne_ident_list(levars) "as" ident(newH) :=
  let tac := ltac2:(h li levars newH |- call_specialize_ltac2_gen h li levars newH false) in
  tac h li levars newH.

Tactic Notation "especialize" constr(h) "at" ne_integer_list(li) "using" ne_ident_list(levars) :=
  let tac := ltac2:(h li levars |- call_specialize_ltac2 h li levars) in
  tac h li levars.


Tactic Notation "especialize" constr(h) "using" ne_ident_list(levars) "at" ne_integer_list(li) :=
  let tac := ltac2:(h li levars |- call_specialize_ltac2 h li levars) in
  tac h li levars.
   
 (*
 Tactic Notation "especialize" constr(h) "at" ne_integer_list(li) :=
  (* let tac := ltac2:(h li |- call_specialize_ltac2_nousing h li) in *)
  (* tac h li. *)
  let dummynewH := fresh "__h__" in
  let levars := ltac2:(Ltac
  let tac := ltac2:(h li levars newH |- call_specialize_ltac2_gen h li levars newH false) in
  tac h li constr:(@nil) dummynewH.
*)


(* "using" must be first, probably because it is not a keyword: *)
Tactic Notation "especialize" constr(h) "until" ne_integer_list(li) "using" ne_ident_list(levars)  "as" ident(newH) :=
  let tac := ltac2:(h li levars newH |- call_specialize_until_ltac2_gen h li levars newH false) in
  tac h li levars newH.

(* "using" must be first, probably because it is not a keyword: *)
Tactic Notation "especialize" constr(h) "until" ne_integer_list(li) "using" ne_ident_list(levars)  "as" ident(newH) :=
  let tac := ltac2:(h li levars newH |- call_specialize_until_ltac2_gen h li levars newH false) in
  tac h li newH.

(* "using" must be first, probably because it is not a keyword: *)
Tactic Notation "especialize" constr(h) "until" ne_integer_list(li) "using" ne_ident_list(levars) "as" "?" :=
  let tac := ltac2:(h li levars newH |- call_specialize_until_ltac2_gen h li levars newH false) in
  let nme := fresh "__h_" in
  tac h li levars ident:(nme).


(* "using" must be first, probably because it is not a keyword: *)
Tactic Notation "especialize" constr(h) "until" ne_integer_list(li) "using" ne_ident_list(levars) :=
  let tac := ltac2:(h li levars newH |- call_specialize_until_ltac2_gen h li levars newH true) in
  let nme := fresh "__h_" in
  tac h li levars ident:(nme).


Definition hidden_product := forall i j :nat, i+1=j -> i+1=j -> i+1=j.

Lemma foo: forall x y : nat,
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

  
  (* especialize H with (n:=0) at 2. *)

  especialize H at 19 20 using p.

  especialize H until 3 using n p.

  


  especialize H at 2 3 using n m.
  1: match goal with
       |- ?lft <= ?rght => is_evar lft; is_evar rght
     end.
  2: match goal with
       H: ?lft < ?rght |- p > 0 => is_evar lft; is_evar rght
     end.
  3: match goal with
       H: nat -> ?lft < ?rght -> hidden_product |- False => is_evar lft; is_evar rght
     end.
  Undo 4.

  especialize H using n m at 2 3.
  1: match goal with
       |- ?lft <= ?rght => is_evar lft; is_evar rght
     end.
  2: match goal with
       H: ?lft < ?rght |- p > 0 => is_evar lft; is_evar rght
     end.
  3: match goal with
       H: nat -> ?lft < ?rght -> hidden_product |- False => is_evar lft; is_evar rght
     end.
  Undo 4.

  especialize H at 2 3.
  1: match goal with
     H: n < m |- n <= m => idtac
     end.
  2: match goal with
       H: n < m |- p > 0 => idtac
     end.
  3: match goal with
       H: forall n m : nat, nat -> n < m -> hidden_product |- False => idtac
     end.
  Undo 4.

  especialize H at 2 3 using n p as hfoo.
  1: match goal with
       |- ?lft <= m => is_evar lft
     end.
  2: match goal with
       H: ?lft < m |- ?rght > 0 => is_evar lft; is_evar rght
     end.
  3: match goal with
       H : (forall n m p : nat, n < m -> n <= m -> p > 0 -> hidden_product),
         H': forall m : nat, ?lft < m -> hidden_product |- False => is_evar lft
     end.
  3: match type of hfoo with
       forall m : nat, ?lft < m -> hidden_product => idtac
     end.
  Undo 5.

  especialize H using n p at 2 3 as hfoo.
  1: match goal with
       |- ?lft <= m => is_evar lft
     end.
  2: match goal with
       H: ?lft < m |- ?rght > 0 => is_evar lft; is_evar rght
     end.
  3: match goal with
       H : (forall n m p : nat, n < m -> n <= m -> p > 0 -> hidden_product),
         H': forall m : nat, ?lft < m -> hidden_product |- False => is_evar lft
     end.
  3: match type of hfoo with
       forall m : nat, ?lft < m -> hidden_product => idtac
     end.
  Undo 5.

Abort.

(*
(* Experimenting a small set of tactic to manipulate a hyp: *)

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
  
