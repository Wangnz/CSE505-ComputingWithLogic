% This predicate returns the optimal satisfaction value.
satisfaction(X) :-
  generateInitialList(1, [], Locations),
  setof(LeastSat, helper(Locations, LeastSat), List),
  findMaximum(List, X).

% This predicate finds the minimum element of a list.
findMinimum([X], X) :- !.
findMinimum([X,Y|Tail], N):-
    ( X > Y ->
        findMinimum([Y|Tail], N);
        findMinimum([X|Tail], N)
    ).

% This predicate finds the maximum element of a list.
findMaximum([X], X) :- !.
findMaximum([X,Y|Tail], N):-
    ( X < Y ->
        findMaximum([Y|Tail], N);
        findMaximum([X|Tail], N)
    ).

% This predicate generates the initial list of locations.
generateInitialList(Location, L, L) :-
  locations(Loc),
  Location > Loc,
  !.
generateInitialList(Location, OldList, NewList) :-
  TempList = [Location | OldList],
  NewLocation is Location + 1,
  generateInitialList(NewLocation, TempList, NewList).

% This predicate generates a tour and finds the least satisfaction value for a particular tour.
helper(Locations, LeastSat) :-
    function(Locations, [], A),
    getLeastSat(A, LeastSat).

% This predicate generates a tour.
function(Locations, A, A) :-
  \+function2(Locations, A),
  % writeln(A),
  !.
function(Locations, Allocations, NewAllocations) :-
  member(X, Locations),
  fits(X, Time),
  location(X, Dur, _, _),
  fitsAllocations(Dur, Time, Allocations),
  TempAllocations = [[X, Time] | Allocations],
  removeFromList(X, Locations, NewLocations),
  function(NewLocations, TempAllocations, NewAllocations).

% This predicate checks if any location can be allocated a time slot to add to a particular tour.
function2(Locations, Allocations) :-
  member(X, Locations),
  fits(X, Time),
  location(X, Dur, _, _),
  fitsAllocations(Dur, Time, Allocations),
  !.

% This predicate checks if a location fits a particular time according to the open and close time.
fits(X, Time) :-
  location(X, Dur, Open, Close),
  EndTime is Close - Dur,
  setof(TempTime, between(TempTime, Open, EndTime), TimeList),
  member(Time, TimeList).

% This predicate checks if a duration of time is free in a particular allocation.
fitsAllocations(0, _, _).
fitsAllocations(Dur, Time, Allocations) :-
  \+occupies(_, Time, Allocations),
  NewDur is Dur - 1,
  NewTime is Time + 1,
  fitsAllocations(NewDur, NewTime, Allocations),
  !.

% This predicate checks if a location occupies a particular hour in a particular allocation.
occupies(Location, Time, Allocations) :-
  member(X, Allocations),
  X = [Location, AllottedTime],
  location(Location, Dur, _, _),
  EndTime is AllottedTime + Dur - 1,
  between(Time, AllottedTime, EndTime),
  !.

% This predicate finds the least satisfaction value for a particular tour.
getLeastSat(Locations, LeastSat) :-
  % Find sat values of all persons
  % Find minimum and return
  getAllSat(1, Locations, [], List),
  findMinimum(List, LeastSat),
  !.

% This predicate calculates the satisfaction values of all people for a particular tour.
getAllSat(Person, _, L, L) :-
  people(P),
  Person > P,
  !.
getAllSat(Person, Locations, OldList, NewList) :-
  getPersonSat(Person, 1, Locations, 0, H),
  TempList = [H | OldList],
  NewPerson is Person + 1,
  getAllSat(NewPerson, Locations, TempList, NewList).

% This predicate calculates the satisfaction value of a particular person for a particular tour.
getPersonSat(Person, _, Locations, _, Max) :-
  locations(Max),
  \+getProof(Person, Locations).
getPersonSat(_, Place, _, S, S) :-
  locations(P),
  Place > P,
  !.
getPersonSat(Person, Place, Locations, OldSat, NewSat) :-
  prefer(Person, Place),
  member([Place, _], Locations),
  TempSat is OldSat + 1,
  NewPlace is Place + 1,
  getPersonSat(Person, NewPlace, Locations, TempSat, NewSat),
  !.
getPersonSat(Person, Place, Locations, OldSat, NewSat) :-
  TempSat is OldSat,
  NewPlace is Place + 1,
  getPersonSat(Person, NewPlace, Locations, TempSat, NewSat),
  !.

% This predicate checks if a person prefers a place, and it is not included in the tour.
getProof(Person, Locations) :-
  prefer(Person, Place),
  \+member([Place, _], Locations).

% This predicate checks if X is a member of a list.
member(X, [X|_]).
member(X, [_|Ys]) :-
  member(X,Ys).

% This predicate checks if a number is between two numbers.
between(X, Min, _) :- X is Min.
between(X, Min, Max) :- NewMin is Min + 1, NewMin < Max, between(X, NewMin, Max).
between(X, Min, Max) :- X is Min + 1, X < Max.
between(X, _, Max) :- X is Max.

% This predicate removes an element from a list.
removeFromList(X, List, NewList) :-
  List = [H | T],
  X is H,
  NewList = T.
removeFromList(X, List, NewList) :-
  List = [H | T],
  removeFromList(X, T, TempList),
  NewList = [H | TempList].
