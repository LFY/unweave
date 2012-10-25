Dealing with recursive calls.

1. Treat the recursive call as an uninterpreted function symbol. This has
issues with probabilistic programs, since the SMT solver does not allow
_nondeterministic_ functions out of the box, i.e., it does not account for
(geometric-gen ()) != (geometric-gen ()). Not too clear how to deal with this.

2. Track which function is being called at the point of recursion. Once we
get a satisfying assignment for our partially-unrolled trace, i.e., for the
constraint C1 = (= 10 (geometric-gen)):

    (sat
      (model (define-fun Y0 () Int 10)
        (define-fun B1 () Bool true) (define-fun V0 () Int 10)
        (define-fun R0 () Int 9) (define-fun B0 () Bool false)
        (define-fun X0 () Bool false)))

We can augment the trace tree with information about which function is being
called; we use this information to associate R0 with another call
(geometric-gen). Now we know that in order for C1 to be true, we need C2 =
(= 9 (geometric-gen)) (because that was the call associated with R0). This results in a model

    (sat
      (model (define-fun Y0 () Int 9)
        (define-fun B1 () Bool true) (define-fun V0 () Int 9)
        (define-fun R0 () Int 8) (define-fun B0 () Bool false)
        (define-fun X0 () Bool false)))

and so on. This seems cumbersome---it is like asking a SMT solver to do the
interpretation for you, then using the reply to advance the state
just a little bit further---but we are also allowed to expand the tree by
different amounts; in general, if we expand the tree by N steps, we get a
formula representing all possible executions N function calls away.

However, it is difficult to identify random variables here; it is not clear
how to reproduce the "database" of random variables unless there is also an
addressing scheme in play.

If our goal is to simply generate satisfying assignments with the right
probability, probability, however, it might not be so bad---there is no
database, we are just exploring forward gradually.

Inference algorithms.

Look-ahead importance sampling
given a query stmt:
step 1. unfold the tree, convert to formula
step 2. gather satisfying assignments for the first choice, weight by probability
step 3. sample from that
step 4. pick the subtree corresponding to that choice. goto 1.


