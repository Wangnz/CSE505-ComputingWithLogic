% This predicate takes the file name as input, performs resolution, and
% prints resolution(success) along with the graph representation of derived clauses if resolution succeeds,
% and prints the single fact resolution(fail) if resolution fails.

resolution(InputFile) :-
  readFileSee(InputFile),
  findall(X, myClause(_, X), L),
  flatten_or(L, Clauses),
  myQuery(_, Q),
  findNegation(Q, QNeg),
  concat(Clauses, QNeg, Set),
  (
    (resolution2(Set, [])) ->
    (writeln('resolution(success).'));
    (writeln('resolution(fail).'))
  ),
  retractall(myClause(_, _)),
  retractall(myQuery(_, _)).


% This predicate reads the input file and asserts all the facts in it.

readFileSee(InputFile) :-
  seeing(OldStream),
  see(InputFile),
  repeat,
  read(Term),
  (
    Term == end_of_file ->
    true ;
    assert(Term), fail
  ),
  seen,
  see(OldStream).


% This predicate takes a list of all the clauses and flattens it into a list of conjuncts,
% where each conjunct is represented by a list of its terms.

flatten_or([], []).
flatten_or(List, NewList) :-
  List = [H | T],
  flatten_or(T, NewT),
  flatten_single(H, NewH),
  NewList = [NewH | NewT].


% This predicate takes a single conjunct and flattens it into a list of its terms.

flatten_single(Term, List) :-
  Term = or(A, B),
  flatten_single(A, NewA),
  flatten_single(B, NewB),
  concat(NewA, NewB, List),
  !.

flatten_single(Term, [Term]).


% This predicate finds the negation of a query.

findNegation(Query, Negation) :-
  flatten_single(Query, New),
  negate_each(New, Negation).

% This predicate negates all the terms in the query.

negate_each([], []).

negate_each(List, NewList) :-
  List = [H | T],
  negate_each(T, NewT),
  negate_single(H, NewH),
  NewList = [NewH | NewT].

% This predicate negates a single term in the query.

negate_single(Term, NegatedTerm) :-
  Term = neg(Term2),
  NegatedTerm = [Term2],
  !.

negate_single(Term, [neg(Term)]).


% This predicate concatenates two lists.

concat([], X, X).
concat([X | Y], Z, [X | W]) :- concat(Y, Z, W).


% This predicate applies resolution to the given set of clauses and negated query.

resolution2(Set, Visited) :-
  findPair(Set, C1, C2, X),
  \+member([C1, C2, X], Visited),
  apply_resolution(C1, C2, X, ResultingClause),
  (
    (ResultingClause = []) ->
        (
          write('')
        );
        (
          \+memberOfSet(ResultingClause, Set),
          concat(Set, [ResultingClause], Set2),
          concat(Visited, [[C1, C2, X]], VisitedNew),
          !,
          resolution2(Set2, VisitedNew)
        )
  ),
  findIndex(Set, C1, Index1),
  findIndex(Set, C2, Index2),
  findPredicateForm(ResultingClause, NewClause),
  findNew(Set, IndexNew),
  write('resolution('),
  write(Index1),
  write(', '),
  write(Index2),
  write(', '),
  write(NewClause),
  write(', '),
  write(IndexNew),
  writeln(').')
  .


% This predicate finds a pair of clauses to which resolution can be applied.

findPair(Set, C1, C2, X) :-
  member(C1, Set),
  member(C2, Set),
  C1 \= C2,
  member(X, C1),
  member(neg(X), C2).


% This predicate checks if an element is a member of a list.

member(X, [X|_]).
member(X, [_|Ys]) :-
  member(X,Ys).


% This predicate applies resolution to two clauses on a specified term and calculates the resulting clause.

apply_resolution(C1, C2, X, Result) :-
  concat(C1, C2, New),
  removeX(X, New, New2),
  removeDup(New2, Result),
  \+containsComplimentary(Result).


% This predicate removes a term and its negation from a list.

removeX(X, List, List2) :-
  List = [H | T],
  H = X,
  removeX(X, T, List2).

removeX(X, List, List2) :-
  List = [H | T],
  H = neg(X),
  removeX(X, T, List2).

removeX(X, List, List2) :-
  List = [H | T],
  H \= X,
  H \= neg(X),
  removeX(X, T, Tnew),
  List2 = [H | Tnew].

removeX(_, [], []).


% This predicate removes duplicate terms from a list.

removeDup([], []).

removeDup(List, NewList) :-
  List = [H | T],
  removeAll(H, T, Tnew),
  removeDup(Tnew, Tnew2),
  NewList = [H | Tnew2].

% This predicate removes all occurrences of a specific term from a list.

removeAll(_, [], []).

removeAll(Elem, List, NewList) :-
  List = [H | T],
  removeAll(Elem, T, Tnew),
  (
    (H = Elem) ->
    (
       NewList = Tnew
    );
    (
      NewList = [H | Tnew]
    )
  ).


% This predicate checks if a list contains a term and its negation.

containsComplimentary(List) :-
  member(X, List),
  member(neg(X), List).


% This predicate checks if a set of terms is a member of a list.
memberOfSet(X, [H|_]):-
  setEqual(X, H),
  !.
memberOfSet(X, [_|Ys]) :-
  memberOfSet(X,Ys).


% This predicate checks if 2 sets are equal.

setEqual(L1, L2) :-
  subset(L1, L2),
  subset(L2, L1),
  !.


% This predicate checks if a set is a subset of another.

subset([], _).
subset(List1, List2) :-
  List1 = [H | T],
  member(H, List2),
  subset(T, List2).


% This predicate finds the index of a particular term in a list.

findIndex(Set, Clause, Index) :-
  helper(Set, Clause, 1, Index).

helper([Clause | _], Clause, Index, Index) :-
  !.

helper([_ | T], Clause, Number, Index) :-
  NewNumber is Number + 1,
  helper(T, Clause, NewNumber, Index).

% This predicate finds the predicate form of a list of terms in a conjunct.

findPredicateForm([], 'empty').

findPredicateForm(Clause, PredicateForm) :-
  Clause = [H],
  PredicateForm = H,
  !.

findPredicateForm(Clause, PredicateForm) :-
  Clause = [E1, E2 | T],
  findPredicateForm(E1, NewE1),
  findPredicateForm(E2, NewE2),
  NewClause = [or(NewE1, NewE2) | T],
  findPredicateForm(NewClause, PredicateForm),
  !.

findPredicateForm(Clause, Clause).

% This predicate finds the position that a new element would have in a list, once it was added.

findNew(Set, IndexNew) :-
  helper2(Set, 1, IndexNew).

helper2([], IndexNew, IndexNew) :-
  !.

helper2([_ | T], Temp, IndexNew) :-
  TempNew is Temp + 1,
  helper2(T, TempNew, IndexNew).
