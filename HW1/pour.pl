% This predicate returns the appropriate value according to whether a split is possible or not.
split(X) :-
  split -> X=yes ; X=no.

% This predicate checks if a split is possbible or not.
split :-
  generateInitialList(List),
  split1(List, 0).

% This predicate generates the initial list of quantities in all the glasses.
generateInitialList(List) :-
  beforeSource([], 1, ListPrev),
  source(S),
  capacity(S, C),
  SourceList = [C],
  concat(ListPrev, SourceList, ListWithSource),
  NewS is S + 1,
  afterSource([], NewS, ListAfterSource),
  concat(ListWithSource, ListAfterSource, List),
  !.

% This predicate appends 0 to a list as the initial quantity of glass i, where i < Source.
beforeSource(List, Index, List) :-
  source(Index).
beforeSource(List, S, List2) :-
  % append 0 to list
  NewS is S + 1,
  beforeSource(List, NewS, NewList),
  List2 = [0 | NewList],
  !.

% This predicate concatenates 2 lists.
concat([],L1,L1).
concat([X|Tail],L2,[X|Tail1]):-
    concat(Tail,L2,Tail1).

% This predicate appends 0 to a list as the initial quantity of glass i, where i > Source.
afterSource(List, Index, List) :-
  vessels(V),
  V is Index - 1.
afterSource(List, Index, List2) :-
  NewIndex is Index + 1,
  afterSource(List, NewIndex, NewList),
  List2 = [0 | NewList],
  !.


% This predicate is True if the list passed to it is a goal state.
split1(List, _) :-
  isGoal(List).

% This predicate is True if one action results in a goal state.
split1(Listin, Moves) :-
  horizon(H),
  Moves =< H,
  capacity(From, _),
  capacity(To, _),
  From \= To,
  pour(From, To, Listin, Listout),
  isGoal(Listout),
  !.

% This predicate calls itself recursively to check if a split can be made within the horizon.
split1(Listin, Moves) :-
  horizon(H),
  Moves =< H,
  capacity(From, _),
  capacity(To, _),
  From \= To,
  pour(From, To, Listin, Listout),
  NewMoves is Moves + 1,
  split1(Listout, NewMoves).

% This predicate pours the maximum amount of beer possible from one glass to another.
pour(From, To, OldList, NewList) :-
  nth(From, OldList, Fromval),
  nth(To, OldList, Toval),
  capacity(To, Tocap),
  Torem is Tocap - Toval,
  Torem < Fromval,
  Newval is Fromval - Torem,
  replace(OldList, From, Newval, TempList),
  replace(TempList, To, Tocap, NewList).
pour(From, To, OldList, NewList) :-
  nth(From, OldList, Fromval),
  nth(To, OldList, Toval),
  capacity(To, Tocap),
  Torem is Tocap - Toval,
  Torem >= Fromval,
  Newval is Toval + Fromval,
  replace(OldList, From, 0, TempList),
  replace(TempList, To, Newval, NewList).

% This predicate returns the nth element of a list.
nth(1, [H|_], H) :-
    !.
nth(N, [_|T], H) :-
    N > 1, %add for loop prevention
    N1 is N-1,
    nth(N1, T, H).

% This predicate replaces an element at a particular position in a list by a new value.
replace([_ | T], 1, X, [X | T]).
replace([H | T], I, X, [H | R]) :-
  I > 1,
  I1 is I - 1,
  replace(T, I1, X, R).

% This predicate checks if a state is a goal state.
isGoal(List) :-
  % num = number of units per person = capacity of source / number of people.
  % remove elements which add up to num
  source(S),
  capacity(S, Total),
  people(People),
  NumUnits is round(Total / People),
  findNum(List, NumUnits, People).

% This predicate checks if the addition of all elements of a list is equal to a particular number.
findNum(List, NumUnits, 1) :-
  % Check if addition of all elements = NumUnits.
  findAddition(List, Addition),
  Addition is NumUnits.
findNum(List, NumUnits, People) :-
  removeElem(List, NumUnits, List1),
  NewPeople is People - 1,
  findNum(List1, NumUnits, NewPeople).

% This predicate finds the addition of all elements in a list.
findAddition([], 0).
findAddition(List, Addition) :-
  List = [H | T],
  findAddition(T, NewAddition),
  Addition is H + NewAddition.

% This predicate removes an element from a list.
removeElem(List, 0, List).
removeElem(List, NumUnits, NewList) :-
  List = [H | T],
  NewUnits is NumUnits - H,
  NewUnits >= 0,
  removeElem(T, NewUnits, NewList).
removeElem(List, NumUnits, NewList) :-
  List = [H | T],
  NewUnits is NumUnits - H,
  NewUnits < 0,
  removeElem(T, NumUnits, List1),
  NewList = [H | List1].
