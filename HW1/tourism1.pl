% This predicate calculates the number of preference violations of the optimal ranking.
violations(X) :-
  getViolationsList(V),
  findMinimum(V, X).

% This predicate finds the number of violations of all possible rankings.
getViolationsList(Violations) :-
  generateInitialList(1, [], List),
  setof(V, getViolationsForAnOrder(List, V), Violations).

% This predicate generates the list of all locations.
generateInitialList(Location, L, L) :-
  locations(Loc),
  Location > Loc,
  !.
generateInitialList(Location, OldList, NewList) :-
  TempList = [Location | OldList],
  NewLocation is Location + 1,
  generateInitialList(NewLocation, TempList, NewList).

% This predicate finds the minumum element of a list.
findMinimum([X], X) :- !.
findMinimum([X,Y|Tail], N):-
    ( X > Y ->
        findMinimum([Y|Tail], N);
        findMinimum([X|Tail], N)
    ).

% This predicate counts the number of violations for a ranking.
getViolationsForAnOrder(List, V) :-
  generatePermutation(List, NewList),
  countTotalViolations(NewList, 0, V).

% This predicate generates all possible permutations of a list.
generatePermutation([], []).
generatePermutation(List, NewList) :-
  member(X, List),
  removeFromList(X, List, TempList),
  generatePermutation(TempList, TempList2),
  NewList = [X | TempList2].

% This predicate checks if X is a member of a list.
member(X, [X|_]).
member(X, [_|Ys]) :-
  member(X,Ys).

% This predicate removes an element from a list.
removeFromList(X, List, NewList) :-
  List = [H | T],
  X is H,
  NewList = T.
removeFromList(X, List, NewList) :-
  List = [H | T],
  removeFromList(X, T, TempList),
  NewList = [H | TempList].

% This predicate counts the total number of violations for a given ranking.
countTotalViolations(Locations, V, V) :-
  Locations = [_ | T],
  T = [].
countTotalViolations(Locations, OldViolations, NewViolations) :-
  Locations = [H | T],
  % for each element in T, count violations of H, element
  funcPerElem(H, T, 0, Count),
  TempViolations is  Count + OldViolations,
  countTotalViolations(T, TempViolations, NewViolations).

% This predicate counts the number of violations for all pairs of locations in a given ranking
funcPerElem(_, [], Count, Count).
funcPerElem(H, T, Count, NewCount) :-
  T = [E | T2],
  calculateViolations(H, E, Violations),
  TempCount is Count + Violations,
  funcPerElem(H, T2, TempCount, NewCount).

% This predicate calculates the number of violations for one pair of locations in a given ranking
calculateViolations(Loc1, Loc2, Violations) :-
  calculatePerPerson(1, Loc1, Loc2, 0, Violations).

% This predicate calculates the number of violations for one person for one pair of locations in a given ranking
calculatePerPerson(Person, _, _, V, V) :-
  people(People),
  Person > People,
  !.
calculatePerPerson(Person, Loc1, Loc2, OldViolations, NewViolations) :-
  % check whether an arc exists for person from loc1 to Loc2
  % if an arc exists, TempViolations is OldViolations + 1
  (
    checkIfArcExists(Person, Loc2, Loc1) ->
      TempViolations is OldViolations + 1
      ;
      TempViolations is OldViolations
  ),
  NewPerson is Person + 1,
  calculatePerPerson(NewPerson, Loc1, Loc2, TempViolations, NewViolations).

% This predicate checks if a person prefers Location 1 over Location 2
% either directly or by transitivity.
checkIfArcExists(Person, Loc1, Loc2) :-
  order(Person, Loc1, Loc2).
checkIfArcExists(Person, Loc1, Loc2) :-
  order(Person, Loc1, Loc3),
  checkIfArcExists(Person, Loc3, Loc2).
