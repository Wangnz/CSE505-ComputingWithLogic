% This predicate returns the minimum number of moves required to rearrange the displays.
moves(X) :-
  allmoves(L),
  findMinimum(L, X).

% This predicate finds all possible number of moves in which the solution state can be obtained.
allmoves(List) :- setof(X, countMoves(X), List).

% This predicate finds the minimum element of a list.
findMinimum([X], X) :- !.
findMinimum([X,Y|Tail], N):-
    ( X > Y ->
        findMinimum([Y|Tail], N);
        findMinimum([X|Tail], N)
    ).

% This predicate counts the number of moves required to reach the solution.
countMoves(X) :-
  generateInitialPositions(InitialList),
  makeMove(InitialList, 0, X, []).

% This predicate generates a list containing the initial positions of all the booths
% in the format [Booth, X, Y].
generateInitialPositions(List) :-
  findall([P, Px, Py], position(P, Px, Py), List).

% This predicate generates all successor states, checks if one by one if they are the target state, and exits with the new number of moves.
makeMove(List, Moves, NewMoves, Visited):-
  horizon(H),
  Moves < H,
  member(BoothWithPos, List),
  BoothWithPos = [B, Bx, By],
  generateSuccessor(B, Bx, By, List, NewList, Visited),
  checkGoal(NewList),
  NewMoves is Moves + 1.

% This predicate generates a successor state, increments the number of moves, and calls itself recursively.
% Here, we know that the successor state is not the target state, as that had been checked in the previous definition of the predicate.
makeMove(List, Moves, NewMoves, Visited):-
  horizon(H),
  Moves < H,
  member(BoothWithPos, List),
  BoothWithPos = [B, Bx, By],
  generateSuccessor(B, Bx, By, List, NewList, Visited),
  NewVisited = [NewList | Visited],
  TempMoves is Moves + 1,
  makeMove(NewList, TempMoves, NewMoves, NewVisited).

% This predicate checks if a booth can be moved upwards,
% and if yes, it checks if the state was already visited,
% and if not visited, returns with the new position.
generateSuccessor(B, Bx, By, List, NewList, Visited) :-
  dimension(B, W, H),
  NewY is By + 1,
  room(_, Ry),
  RoomY is Ry - 1,
  between(NewY, 0, RoomY),
  EndY is NewY + H - 1,
  between(EndY, 0, RoomY),
  removeBooth(B, List, RemovedList),
  isVerticalMovementFree(Bx, W, NewY, RemovedList),
  newPosition(B, Bx, NewY, List, TempList),
  \+member(TempList, Visited),
  NewList = TempList.

% This predicate checks if a booth can be moved downwards,
% and if yes, it checks if the state was already visited,
% and if not visited, returns with the new position.
generateSuccessor(B, Bx, By, List, NewList, Visited) :-
  dimension(B, W, H),
  NewY is By - 1,
  room(_, Ry),
  RoomY is Ry - 1,
  between(NewY, 0, RoomY),
  EndY is NewY + H - 1,
  between(EndY, 0, RoomY),
  removeBooth(B, List, RemovedList),
  isVerticalMovementFree(Bx, W, NewY, RemovedList),
  newPosition(B, Bx, NewY, List, TempList),
  \+member(TempList, Visited),
  NewList = TempList.

% This predicate checks if a booth can be moved to the right,
% and if yes, it checks if the state was already visited,
% and if not visited, returns with the new position.
generateSuccessor(B, Bx, By, List, NewList, Visited) :-
  dimension(B, W, H),
  NewX is Bx + 1,
  room(Rx, _),
  RoomX is Rx - 1,
  between(NewX, 0, RoomX),
  EndX is NewX + W - 1,
  between(EndX, 0, RoomX),
  removeBooth(B, List, RemovedList),
  isHorizontalMovementFree(By, H, NewX, RemovedList),
  newPosition(B, NewX, By, List, TempList),
  \+member(TempList, Visited),
  NewList = TempList.

% This predicate checks if a booth can be moved to the left,
% and if yes, it checks if the state was already visited,
% and if not visited, returns with the new position.
generateSuccessor(B, Bx, By, List, NewList, Visited) :-
  dimension(B, W, H),
  NewX is Bx - 1,
  room(Rx, _),
  RoomX is Rx - 1,
  between(NewX, 0, RoomX),
  EndX is NewX + W - 1,
  between(EndX, 0, RoomX),
  removeBooth(B, List, RemovedList),
  isHorizontalMovementFree(By, H, NewX, RemovedList),
  newPosition(B, NewX, By, List, TempList),
  \+member(TempList, Visited),
  NewList = TempList.

% This predicate checks if a state is the target state.
checkGoal([]).
checkGoal(List) :-
  List = [H | T],
  H = [B, Bx, By],
  target(B, Bx, By),
  checkGoal(T).
checkGoal(List) :-
  List = [H | T],
  H = [B, Bx, By],
  \+target(B, _, _),
  position(B, Bx, By),
  checkGoal(T).

% This predicate checks if a number is between two other numbers.
between(X, Min, Max) :- X is Min + 1, X < Max.
between(X, Min, Max) :- NewMin is Min + 1, NewMin < Max, between(X, NewMin, Max).
between(X, Min, Max) :- X is Min; X is Max.

% This predicate removes a booth from a list containing booths and their corresponding positions.
removeBooth(B, List, NewList) :-
  List = [H | T],
  H = [Booth, _, _],
  Booth = B,
  NewList = T.

removeBooth(B, List, NewList) :-
  List = [H | T],
  removeBooth(B, T, TempList),
  NewList = [H | TempList].

% This predicate checks if a group of vertical cells is free, so that a booth can move horizontally.
isHorizontalMovementFree(_, 0, _, _).
isHorizontalMovementFree(Y, H, X, List) :-
  H > 0,
  \+occupies(_, X, Y, List),
  NewY is Y + 1,
  NewH is H - 1,
  isHorizontalMovementFree(NewY, NewH, X, List).

% This predicate checks if a group of horizontal cells is free, so that a booth can move vertically.
isVerticalMovementFree(_, 0, _, _).
isVerticalMovementFree(X, W, Y, List) :-
  W > 0,
  \+occupies(_, X, Y, List),
  NewX is X + 1,
  NewW is W - 1,
  isVerticalMovementFree(NewX, NewW, Y, List).

% This predicate changes the position of a booth in a list.
newPosition(B, X, Y, List, NewList) :-
  List = [H | T],
  H = [Booth, _, _],
  B is Booth,
  NewList = [[B, X, Y] | T].
newPosition(B, X, Y, List, NewList) :-
  List = [H | T],
  newPosition(B, X, Y, T, TempList),
  NewList = [H | TempList].

% This member checks if X is an element of a list.
member(X, [X|_]).
member(X, [_|Ys]) :-
  member(X,Ys).

% This predicate checks if a booth occupies a particular position in a state.
occupies(Booth, X, Y, List) :-
  dimension(Booth, Length, Height),
  member(BoothWithPos, List),
  BoothWithPos = [Booth, Xloc, Yloc],
  Xsum is Xloc + Length - 1,
  Ysum is Yloc + Height - 1,
  between(X, Xloc, Xsum),
  between(Y, Yloc, Ysum).
