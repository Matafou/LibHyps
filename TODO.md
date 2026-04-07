# Suggestion by Sylvain Boulme:

# have a true replacement for "as"

Syntax suggestion:

tac : [ H 1 H 2 | x y Hx Hy H | ...].

applies tac and then destruct each new hyp with the corresponding
intropattern.

Seems to need ocaml code because tactic notation are not suitable.

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
tac1 ;<; tac2.

We don't need the 4 variants anymore (ltac2 is fast enough to avoid
the list variants).

# Are shortcuts reasonable wrt to ssreflect?

tac /sn. may clash with ssreflect.

## go back to prefix "!" ?

we need to have vaiants

/s /n /g /r and all interesting combinations.


# Naming: decide on ids

make possible the fact to decide to use an arg name only if it is an id.

typically: "h_eq_add_add" is not so interesting

idea yet to be refined: at last level if seeing a hyp name then use it
else don't generate the last level.

# Naming : distinguish sub terms in the name

Typically "h_add_x_y_z" would maybe be better as "h_add_x_y__z"


# Switch to ocaml

## Augment "Arguments" with naming information

- which args to ignore
- Auto ignore implicit args
- make the new "as" implementable?

# ideas for other post-tactic cleaning

## decomp? /d
## cbn
## ?
