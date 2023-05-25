from copy import deepcopy
from heapq import heappush, heappop
import time
import argparse
import sys
from typing import List, Any

char_single = '2'
char_goal = '1'


# ====================================================================================


class Chess:
    """
    定义棋子
    x_length: 长
    x_length: 宽
    x_coord: 坐标x
    x_coord: 坐标y
    """

    def __init__(self, x_length, y_length, x_coord, y_coord, goal, name):
        self.x_length = x_length
        self.y_length = y_length
        self.x_coord = x_coord
        self.y_coord = y_coord
        self.goal = goal
        self.name = name

    def update(self, new_x_coord, new_y_coord):
        self.x_coord = new_x_coord
        self.y_coord = new_y_coord

    def get_x_cod(self):
        return self.x_coord

    def get_y_cod(self):
        return self.y_coord

    def get_name(self):
        return self.name


class Board:
    """
    定义这个board，这个board有几个parameter
    :width: 宽度 (default 4)
    :height: 长度 (default 5)
    :board: list of list [] 存棋子的list
    """
    empty: list[Any]

    def __init__(self):
        self.width = 4
        self.height = 5
        self.board = [[".", ".", ".", "."],
                      [".", ".", ".", "."],
                      [".", ".", ".", "."],
                      [".", ".", ".", "."],
                      [".", ".", ".", "."]]

        self.chess_xx = 0
        self.chess_yy = 0
        self.chess_z = 0

    def __eq__(self, other):
        """
        Return Ture if all items in other's map are same as self's
        """
        for y in range(5):
            for x in range(4):
                if self.board[y][x] != other.board[y][x]:
                    return False
        return True

    def __str__(self):
        result = ""
        for y in self.board:
            for x in y:
                result += x
            result += '\n'
        return result

    def move_up(self, y_pos, x_pos):
        x = x_pos
        if self.board[y_pos][x_pos] != '.':
            return

        if 0 < y_pos < 5:
            y = y_pos - 1
        else:
            return

        if self.board[y][x] == '1':
            if x > 0 and self.board[y][x - 1] == '1' and self.board[y + 1][x - 1] == '.':
                self.board[y - 1][x] = '.'
                self.board[y - 1][x - 1] = '.'
                self.board[y + 1][x] = '1'
                self.board[y + 1][x - 1] = '1'

            elif x < 3 and self.board[y][x + 1] == '1' and self.board[y + 1][x + 1] == '.':
                self.board[y - 1][x] = '.'
                self.board[y - 1][x + 1] = '.'
                self.board[y + 1][x] = '1'
                self.board[y + 1][x + 1] = '1'

        elif self.board[y][x] == '2':
            self.board[y][x] = '.'
            self.board[y + 1][x] = '2'

        elif self.board[y][x] == '<':
            if self.board[y + 1][x + 1] == '.':
                self.board[y][x] = '.'
                self.board[y][x + 1] = '.'
                self.board[y + 1][x] = '<'
                self.board[y + 1][x + 1] = '>'
            else:
                return

        elif self.board[y][x] == '>':
            if self.board[y + 1][x - 1] == '.':
                self.board[y][x] = '.'
                self.board[y][x - 1] = '.'
                self.board[y + 1][x] = '>'
                self.board[y + 1][x - 1] = '<'

        elif self.board[y][x] == 'v':
            self.board[y][x] = '^'
            self.board[y - 1][x] = '.'
            self.board[y + 1][x] = 'v'

        else:
            return

    def move_down(self, y_pos, x_pos):
        x = x_pos
        if self.board[y_pos][x_pos] != '.':
            return

        if 0 <= y_pos < 4:
            y = y_pos + 1
        else:
            return

        if self.board[y][x] == '1':
            if x > 0 and self.board[y][x - 1] == '1' and self.board[y - 1][x - 1] == '.':
                self.board[y + 1][x] = '.'
                self.board[y + 1][x - 1] = '.'
                self.board[y - 1][x] = '1'
                self.board[y - 1][x - 1] = '1'

            elif x < 3 and self.board[y][x + 1] == '1' and self.board[y - 1][x + 1] == '.':
                self.board[y + 1][x] = '.'
                self.board[y + 1][x + 1] = '.'
                self.board[y - 1][x] = '1'
                self.board[y - 1][x + 1] = '1'

        elif self.board[y][x] == '2':
            self.board[y][x] = '.'
            self.board[y - 1][x] = '2'

        elif self.board[y][x] == '<':
            if self.board[y - 1][x + 1] == '.':
                self.board[y][x] = '.'
                self.board[y][x + 1] = '.'
                self.board[y - 1][x] = '<'
                self.board[y - 1][x + 1] = '>'
            else:
                return

        elif self.board[y][x] == '>':
            if self.board[y - 1][x - 1] == '.':
                self.board[y][x] = '.'
                self.board[y][x - 1] = '.'
                self.board[y - 1][x] = '>'
                self.board[y - 1][x - 1] = '<'

        elif self.board[y][x] == '^':
            self.board[y][x] = 'v'
            self.board[y - 1][x] = '^'
            self.board[y + 1][x] = '.'

        else:
            return

    def move_left(self, y_pos, x_pos):
        y = y_pos
        if self.board[y_pos][x_pos] != '.':
            return

        if 0 < x_pos < 4:
            x = x_pos - 1
        else:
            return

        if self.board[y][x] == '1':
            if 0 < y <= 4 and self.board[y - 1][x] == '1' and self.board[y - 1][x + 1] == '.':
                self.board[y][x - 1] = '.'
                self.board[y - 1][x - 1] = '.'
                self.board[y][x + 1] = '1'
                self.board[y - 1][x + 1] = '1'

            elif 0 <= y < 4 and self.board[y + 1][x] == '1' and self.board[y + 1][x + 1] == '.':
                self.board[y][x - 1] = '.'
                self.board[y + 1][x - 1] = '.'
                self.board[y][x + 1] = '1'
                self.board[y + 1][x + 1] = '1'

        elif self.board[y][x] == '2':
            self.board[y][x] = '.'
            self.board[y][x + 1] = '2'

        elif self.board[y][x] == '^':
            if self.board[y + 1][x + 1] == '.':
                self.board[y][x] = '.'
                self.board[y + 1][x] = '.'
                self.board[y][x + 1] = '^'
                self.board[y + 1][x + 1] = 'v'
            else:
                return

        elif self.board[y][x] == 'v':
            if self.board[y - 1][x + 1] == '.':
                self.board[y][x] = '.'
                self.board[y - 1][x] = '.'
                self.board[y][x + 1] = 'v'
                self.board[y - 1][x + 1] = '^'

        elif self.board[y][x] == '>':
            self.board[y][x] = '<'
            self.board[y][x + 1] = '>'
            self.board[y][x - 1] = '.'

        else:
            return

    def move_right(self, y_pos, x_pos):
        y = y_pos
        if self.board[y_pos][x_pos] != '.':
            return

        if 0 <= x_pos < 3:
            x = x_pos + 1
        else:
            return

        if self.board[y][x] == '1':
            if 0 < y <= 4 and self.board[y - 1][x] == '1' and self.board[y - 1][x - 1] == '.':
                self.board[y][x + 1] = '.'
                self.board[y - 1][x + 1] = '.'
                self.board[y][x - 1] = '1'
                self.board[y - 1][x - 1] = '1'

            elif 0 <= y < 4 and self.board[y + 1][x] == '1' and self.board[y + 1][x - 1] == '.':
                self.board[y][x + 1] = '.'
                self.board[y + 1][x + 1] = '.'
                self.board[y][x - 1] = '1'
                self.board[y + 1][x - 1] = '1'

        elif self.board[y][x] == '2':
            self.board[y][x] = '.'
            self.board[y][x - 1] = '2'

        elif self.board[y][x] == '^':
            if self.board[y + 1][x - 1] == '.':
                self.board[y][x] = '.'
                self.board[y + 1][x] = '.'
                self.board[y][x - 1] = '^'
                self.board[y + 1][x - 1] = 'v'
            else:
                return

        elif self.board[y][x] == 'v':
            if self.board[y - 1][x - 1] == '.':
                self.board[y][x] = '.'
                self.board[y - 1][x] = '.'
                self.board[y][x - 1] = 'v'
                self.board[y - 1][x - 1] = '^'

        elif self.board[y][x] == '<':
            self.board[y][x] = '>'
            self.board[y][x - 1] = '<'
            self.board[y][x + 1] = '.'

        else:
            return

    """finish move"""

    def append_(self, chess_list):
        for chess in chess_list:
            if self.board[chess.y_coord][chess.x_coord] != ".":
                return "the positon has already been used"
            if chess.goal is True:
                self.board[chess.y_coord][chess.x_coord] = '1'
                self.board[chess.y_coord][chess.x_coord + 1] = '1'
                self.board[chess.y_coord + 1][chess.x_coord] = '1'
                self.board[chess.y_coord + 1][chess.x_coord + 1] = '1'

            else:
                if chess.x_length == 2:
                    self.board[chess.y_coord][chess.x_coord] = '<'
                    self.board[chess.y_coord][chess.x_coord + 1] = '>'
                    self.chess_xx += 1
                elif chess.y_length == 2:
                    self.board[chess.y_coord][chess.x_coord] = '^'
                    self.board[chess.y_coord + 1][chess.x_coord] = 'v'
                    self.chess_yy += 1
                elif chess.x_length == 1 and chess.y_length == 1:
                    self.board[chess.y_coord][chess.x_coord] = '2'
                    self.chess_z += 1

    def display(self):
        for item_ in self.board:
            print(item_)

    def display_empty(self):
        return print(self.empty)

    def show_empty(self):
        return self.empty

    def is_goal(self):
        if self.board[3][1] == '1' and self.board[4][1] == '1' and self.board[3][2] == '1' and self.board[4][2] == '1':
            return True
        return False

    def get_item(self, y, x):
        return self.board[y][x]


def copy(old_board: Board) -> Board:
    board2 = Board()
    for y in range(5):
        for x in range(4):
            board2.board[y][x] = old_board.get_item(y, x)
    return board2


def cost(states: Board, traveled: dict) -> int:
    """计算总共走了多少步"""
    parent = traveled[states.__str__()]  # Previous state
    c = 0
    while parent is not None:
        c += 1
        parent = traveled[parent]
    return c


def moveable(states: Board) -> List[Board]:
    result = []
    empty = []
    for y in range(5):
        for x in range(4):
            if states.get_item(y, x) == '.':
                empty.append((y, x))
    for empty_point in empty:
        w = copy(states)
        s = copy(states)
        a = copy(states)
        d = copy(states)
        s.move_down(empty_point[0], empty_point[1])
        a.move_left(empty_point[0], empty_point[1])
        d.move_right(empty_point[0], empty_point[1])
        w.move_up(empty_point[0], empty_point[1])
        for i in [w, a, d, s]:
            if i != states and i not in result:
                result.append(i)
    return result


def dfs(init_state: Board) -> List[str]:
    frontier = []
    traveled = dict()
    frontier.append(init_state)
    traveled[init_state.__str__()] = None
    total_cost = None
    solution = []
    final = None
    while frontier:
        curr = frontier.pop()
        if curr.is_goal():
            total_cost = cost(curr, traveled)
            final = curr.__str__()
            break
        moveable_ = moveable(curr)

        for candidate in moveable_:
            if candidate.__str__() not in traveled:
                traveled[candidate.__str__()] = curr.__str__()
                frontier.insert(0, candidate)

    while final is not None:
        solution.insert(0, final)
        final = traveled[final]
    return solution


# dp part
def find_target_state(states: Board) -> tuple:
    for y in range(5):
        for x in range(4):
            if states.get_item(y, x) == '1':
                return y, x


def h_value(states: Board) -> int:
    target_post = find_target_state(states)
    return abs(3 - target_post[0]) + abs(1 - target_post[1])


class HeapItem:
    def __init__(self, item, priority):
        self.item = item
        self.priority = priority

    def __lt__(self, other):
        return self.priority < other.priority

    def get_item(self):
        return self.item


def astart_search(states: Board):
    return heuristic_search(states, h_value)


def heuristic_search(init_state: Board, function) -> List[str]:
    frontier = []
    traveled = dict()
    heappush(frontier, HeapItem(init_state, 4))
    traveled[init_state.__str__()] = None
    total_cost = None
    solution = []
    final = None
    while frontier:
        curr = heappop(frontier)
        item = curr.get_item()
        if item.is_goal():
            total_cost = cost(item, traveled)
            final = item.__str__()
            break

        moveable_ = moveable(item)
        for candidate in moveable_:
            g_value = cost(item, traveled) + 1
            if candidate.__str__() not in traveled:
                traveled[candidate.__str__()] = item.__str__()
                priority = g_value + function(candidate)
                heappush(frontier, HeapItem(candidate, priority))

    while final is not None:
        solution.insert(0, final)
        final = traveled[final]
    return solution


def read_from_file(filename):
    """
    Load initial board from a given file.

    :param filename: The name of the given file.
    :type filename: str
    :return: A loaded board
    :rtype: Board
    """

    puzzle_file = open(filename, "r")

    line_index = 0
    pieces = []
    g_found = False
    xx = 0
    yy = 0
    z = 0

    for line in puzzle_file:

        for x, ch in enumerate(line):

            if ch == '^':  # found vertical piece
                pieces.append(Chess(1, 2, x, line_index, False, 'xx' + str(xx)))
                xx += 1

            elif ch == '<':  # found horizontal piece
                pieces.append(Chess(2, 1, x, line_index, False, 'yy' + str(yy)))
                yy += 1
            elif ch == char_single:
                pieces.append(Chess(1, 1, x, line_index, False, 'z' + str(z)))
                z += 1
            elif ch == char_goal:
                if not g_found:
                    pieces.append(Chess(2, 2, x, line_index, True, 'goal'))
                    g_found = True
        line_index += 1

    puzzle_file.close()

    board = Board()
    board.append_(pieces)
    return board


if __name__ == "__main__":
    # read the board from the file
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--inputfile",
        type=str,
        required=True,
        help="The input file that contains the puzzle."
    )
    parser.add_argument(
        "--outputfile",
        type=str,
        required=True,
        help="The output file that contains the solution."
    )
    parser.add_argument(
        "--algo",
        type=str,
        required=True,
        choices=['astar', 'dfs'],
        help="The searching algorithm."
    )
    args = parser.parse_args()

    # read the board from the file
    board = read_from_file(args.inputfile)
    if args.algo == 'dfs':
        dfs_sol = dfs(board)
        dfs_file = open(args.outputfile, 'w')
        dfs_file.write(dfs_sol[0])
        for step in dfs_sol[1:]:
            dfs_file.write(f'{step}\n')
        dfs_file.close()
    if args.algo == 'astar':
        astart_sol = astart_search(board)
        astart_file = open(args.outputfile, 'w')
        astart_file.write(astart_sol[0])
        for step in astart_sol[1:]:
            astart_file.write(f'{step}\n')
