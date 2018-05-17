% This predicate returns the minimum number of tables required to arrange the dishes.
tables(X) :-
  generateInitialList(List),
  allmoves(List, RetList),
  findMinimum(RetList, X).

% This predicate generates the initial list of dishes.
generateInitialList(List) :-
  addedDishes(1, [], List),
  !.

% This predicate finds all possible number of tables for arranging the dishes.
allmoves(List, RetList) :- setof(X, getTableCount(List, 0, X), RetList).

% This predicate finds the minimum element in a list.
findMinimum([X], X) :- !.
findMinimum([X,Y|Tail], N):-
    ( X > Y ->
        findMinimum([Y|Tail], N);
        findMinimum([X|Tail], N)
    ).

% This predicate adds remaining dishes to a list.
addedDishes(X, List, List) :-
  dishes(Dishes),
  X > Dishes.
addedDishes(X, OldList, NewList) :-
  demand(X, D),
  addDemand(X, D, OldList, TempList),
  NewX is X + 1,
  addedDishes(NewX, TempList, NewList).

% This predicate adds dish N to a list D times, where D is the demand of dish N.
addDemand(_, 0, List, List).
addDemand(X, D, OldList, NewList) :-
  TempList = [X | OldList],
  NewD is D - 1,
  addDemand(X, NewD, TempList, NewList).

% This predicate finds the number of tables required in an arrangement.
getTableCount([], T, T).
getTableCount(DishesRemaining, InitialTables, NewTables) :-
  table_width(TableWidth),
  getTables(TableWidth, DishesRemaining, NewDishesRemaining),
  TempTables is InitialTables + 1,
  getTableCount(NewDishesRemaining, TempTables, NewTables).

% This predicate places dishes on a table and returns the list of remaining dishes.
getTables(TableWidth, DishesRemaining, NewDishesRemaining) :-
  member(X, DishesRemaining),
  removeFromList(X, DishesRemaining, TempDishesRemaining),
  dish_width(X, DishWidth),
  TempTableWidth is TableWidth - DishWidth,
  (
    isHot(X) ->
      prevHot(TempTableWidth, TempDishesRemaining, NewDishesRemaining)
      ;
      prevCold(TempTableWidth, TempDishesRemaining, NewDishesRemaining)
  ).

% This predicate places a dish on the table if possible, when the previous dish was hot.
prevHot(0, D, D).
prevHot(TableWidth, DishesRemaining, NewDishesRemaining) :-
  member(X, DishesRemaining),
  removeFromList(X, DishesRemaining, TempDishesRemaining),
  dish_width(X, DishWidth),
  TempTableWidth is TableWidth - DishWidth,
  TempTableWidth >= 0,
  % Current dish is hot
  isHot(X),
  !,
  prevHot(TempTableWidth, TempDishesRemaining, NewDishesRemaining).
prevHot(TableWidth, DishesRemaining, NewDishesRemaining) :-
  member(X, DishesRemaining),
  removeFromList(X, DishesRemaining, TempDishesRemaining),
  dish_width(X, DishWidth),
  TempTableWidth is TableWidth - DishWidth,
  TempTableWidth >= 0,
  % Current dish is cold
  \+ isHot(X),
  separation(S),
  TempTableWidth2 is TempTableWidth - S,
  prevCold(TempTableWidth2, TempDishesRemaining, NewDishesRemaining).
prevHot(_, D, D).

% This predicate places a dish on the table if possible, when the previous dish was cold.
prevCold(0, D, D).
prevCold(TableWidth, DishesRemaining, NewDishesRemaining) :-
  member(X, DishesRemaining),
  removeFromList(X, DishesRemaining, TempDishesRemaining),
  dish_width(X, DishWidth),
  TempTableWidth is TableWidth - DishWidth,
  TempTableWidth >= 0,
  % Current dish is hot
  isHot(X),
  !,
  separation(S),
  TempTableWidth2 is TempTableWidth - S,
  prevHot(TempTableWidth2, TempDishesRemaining, NewDishesRemaining).
prevCold(TableWidth, DishesRemaining, NewDishesRemaining) :-
  member(X, DishesRemaining),
  removeFromList(X, DishesRemaining, TempDishesRemaining),
  dish_width(X, DishWidth),
  TempTableWidth is TableWidth - DishWidth,
  TempTableWidth >= 0,
  % Current dish is cold
  \+ isHot(X),
  prevCold(TempTableWidth, TempDishesRemaining, NewDishesRemaining).
prevCold(_, D, D).

% This predicate checks if a dish is hot.
isHot(X) :-
  hot(H),
  X =< H,
  !.

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
