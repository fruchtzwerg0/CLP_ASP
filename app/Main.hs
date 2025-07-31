{-# LANGUAGE QuasiQuotes #-}
module Main (main) where

import Parser
import MAlonzo.Code.CLPZ45Zagda

main :: IO ()
main = print (evalTermAgda hanoiProgram hanoiQuery False)

ancestorProgram :: [ClauseTermHs]
ancestorProgram = [prologProgram|
  parent(alice, bob).
  parent(bob, charlie).
  ancestor(X, Y) :- parent(X, Y).
  ancestor(X, Y) :- parent(X, Z), ancestor(Z, Y).
|]

ancestorQuery :: [LiteralTermHs]
ancestorQuery = [prologQuestion| ancestor(Y, X), Y = bob, Y = charlie |]

lastProgram :: [ClauseTermHs]
lastProgram = [prologProgram|
  last(cons(X, nil), X).
  last(cons(X, T), Y) :- last(T, Y).
|]

lastQuery :: [LiteralTermHs]
lastQuery = [prologQuestion| last(cons(a, cons(b, cons(c, cons(d, nil)))), X) |]

elementAtProgram :: [ClauseTermHs]
elementAtProgram = [prologProgram|
  elementAt(X, cons(X, Y), suc(zero)).
  elementAt(X, cons(Y, T), suc(N)) :-
    elementAt(X, T, N).
|]

elementAtQuery :: [LiteralTermHs]
elementAtQuery = [prologQuestion|
  elementAt(X, cons(a, cons(b, cons(c, cons(d, cons(e, nil))))), suc(suc(suc(zero))))
|]

lengthProgram :: [ClauseTermHs]
lengthProgram = [prologProgram|
  length(nil, zero).
  length(cons(X, T), suc(N)) :- length(T, N).
|]

lengthQuery :: [LiteralTermHs]
lengthQuery = [prologQuestion|
  length(cons(a, cons(b, cons(c, cons(d, nil)))), N)
|]

genLength3Query :: [LiteralTermHs]
genLength3Query = [prologQuestion|
  length(L, suc(suc(suc(zero))))
|]

reverseProgram :: [ClauseTermHs]
reverseProgram = [prologProgram|
  reverse(L, R) :- reverseAcc(L, nil, R).

  reverseAcc(nil, Acc, Acc).
  reverseAcc(cons(H, T), Acc, R) :-
    reverseAcc(T, cons(H, Acc), R).
|]

reverseQuery :: [LiteralTermHs]
reverseQuery = [prologQuestion|
  reverse(cons(a, cons(b, cons(c, nil))), R)
|]

appendProgram :: [ClauseTermHs]
appendProgram = [prologProgram|
  append(nil, L, L).
  append(cons(H, T), L2, cons(H, R)) :-
    append(T, L2, R).
|]

appendQuery :: [LiteralTermHs]
appendQuery = [prologQuestion|
  append(cons(a, cons(b, cons(c, nil))), cons(a, cons(b, cons(c, nil))), O)
|]

hanoiProgram0 :: [ClauseTermHs]
hanoiProgram0 = [prologProgram|
  append(nil, L, L).
  append(cons(H, T), L2, cons(H, R)) :-
    append(T, L2, R).

  hanoi(suc(zero), A, B, X, cons(move(A, B), nil)).

  hanoi(suc(N), A, B, C, Moves) :-
    hanoi(N, A, C, B, Moves).

  hanoiMoves(N, Moves) :-
    hanoi(N, a, b, c, Moves).
|]

hanoiProgram :: [ClauseTermHs]
hanoiProgram = [prologProgram|
  append(nil, L, L).
  append(cons(H, T), L2, cons(H, R)) :-
    append(T, L2, R).

  hanoi(suc(zero), A, B, X, cons(move(A, B), nil)).

  hanoi(suc(N), A, B, C, Moves) :-
    hanoi(N, A, C, B, Moves1),
    hanoi(N, C, B, A, Moves2),
    append(Moves1, cons(move(A, B), Moves2), Moves).

  hanoiMoves(N, Moves) :-
    hanoi(N, a, b, c, Moves).
|]

hanoiQuery :: [LiteralTermHs]
hanoiQuery = [prologQuestion|
  hanoiMoves(suc(suc(suc(zero))), Moves)
|]