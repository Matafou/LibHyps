# Suggestion by Sylvain Boulme:

## Looks like "exploit" developped in compcert.

exploit creates evars for all premisses of a hyp.
especialize creates evars for ONE premiss.
Maybe we could have the best of both?
like:
```
especialize h at 1,4,6. (* fine grained exploit *)
especialize h at *. (* equivalent to exploit *)
```
# have a true replacement for "as"

Syntax suggestion:

tac : intropattern1 intropattern2 ... intropatternk.

applies tac and then destruct each new hyp with the corresponding
intropattern.

## Remaining question

how to deal with several subgoals?
Is it possible to split a disjunctive intropattern for each subgoal?

# Find a better syntax?

I find "tac1 ; { tac2 }." is nice because it resembles "tac ; [ tac2 ]."

but curly braces are already over-overloaded.

## Maybe keep the square brackets?

tac1 ; [[ tac2 ]].

## or go back to double semi-colon?

tac1 ;; tac2.

but we need 4 variants. ;<; ;!; ;!<; which are quite ugly.

# Are shortcuts reasonable wrt to ssreflect?

tac /sn. may clash with ssreflect.

## go back to prefix "!" ?

we need to have vaiants

/s /n /g /r and all interesting combinations.


# Naming: decide on ids

make possible the fact to decide to use an arg name only if it is an id.

typically: "h_eq_add_add" is not so interesting

# Naming : distinguish sub terms in the name

Typically "h_add_x_y_z" would maybe be better as "h_add_x_y__z"


# Switch to ocaml

## Augment "Arguments" with naming information

- which args to ignore
- Auto ignore implicit args


# ideas for other post-tactic cleaning

## decomp?
## cbn
## ?
