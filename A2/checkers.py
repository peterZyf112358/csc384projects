import argparse
import copy
import sys
import time
import math

cache = {}


class State:

    def __init__(self) -> None:
        self.red = dict()
        self.black = dict()

    def display(self) -> str:

        lst = []
        result = ''
        for _ in range(8):
            lst.append(['.', '.', '.', '.', '.', '.', '.', '.'])

        for key in self.black:
            lst[key[1]][key[0]] = self.black[key]

        for key in self.red:
            lst[key[1]][key[0]] = self.red[key]

        for i in range(8):
            result += ''.join(lst[i])
            result += '\n'

        return result

    def __eq__(self, other):
        if len(self.red) != len(other.red) \
                or len(self.black) != len(other.black):
            return False

        for pix in self.red:
            if pix not in other.red:
                return False
            elif self.red[pix] != other.red[pix]:
                return False
        for pix in self.black:
            if pix not in other.black:
                return False
            elif self.black[pix] != other.black[pix]:
                return False
        return True

    def move(self, position: tuple, destination: tuple):

        x_dis = destination[0] - position[0]
        y_dis = destination[1] - position[1]
        if abs(x_dis) != 1 or abs(y_dis) != 1:
            return None

        if (destination not in self.red) and (destination not in self.black):
            if position in self.red:
                chess = self.red.pop(position)
                if destination[1] == 0:
                    self.red[destination] = 'R'
                else:
                    self.red[destination] = chess
            else:
                chess = self.black.pop(position)
                if destination[1] == 7:
                    self.black[destination] = 'B'
                else:
                    self.black[destination] = chess
            return destination

        if position in self.red and destination in self.black:
            new_des = (destination[0] + x_dis, destination[1] + y_dis)
            if 0 <= new_des[0] <= 7 and 0 <= new_des[1] <= 7 \
                    and new_des not in self.black and new_des not in self.red:
                chess = self.red.pop(position)
                if new_des[1] == 0:
                    self.red[new_des] = 'R'
                else:
                    self.red[new_des] = chess
                self.black.pop(destination)
                return new_des

        elif position in self.black and destination in self.red:
            new_des = (destination[0] + x_dis, destination[1] + y_dis)
            if 0 <= new_des[0] <= 7 and 0 <= new_des[1] <= 7 \
                    and new_des not in self.black and new_des not in self.red:
                chess = self.black.pop(position)
                if new_des[1] == 7:
                    self.black[new_des] = 'B'
                else:
                    self.black[new_des] = chess
                self.red.pop(destination)
                return new_des
        return None


def terminal(state: State) -> bool:
    if len(state.red) == 0 or len(state.black) == 0:
        return True
    if len(spread(state, 'r')) == 0 or len(spread(state, 'b')) == 0:
        return True
    return False


def read_from_file(file: str) -> State:
    f = open(file, 'r')
    lines = f.readlines()
    result = State()
    for y in range(8):
        for x in range(8):
            if lines[y][x] == 'r':
                result.red[(x, y)] = 'r'
            elif lines[y][x] == 'R':
                result.red[(x, y)] = 'R'
            elif lines[y][x] == 'b':
                result.black[(x, y)] = 'b'
            elif lines[y][x] == 'B':
                result.black[(x, y)] = 'B'
    f.close()
    return result


def spread(state: State, player: str) -> list[State]:
    result = []
    if player == 'r':
        for key in state.red:
            s1 = clone(state)
            s1_lst = spread_single(s1, key, 'r')
            for i in [s1_lst]:
                for s in i:
                    if s != state and s not in result:
                        result.append(s)
    else:
        for key in state.black:
            s1 = clone(state)
            s1_lst = spread_single(s1, key, 'b')
            for i in [s1_lst]:
                for s in i:
                    if s != state and s not in result:
                        result.append(s)
    return result


def spread_single(state: State, position: tuple, player: str) -> list[State]:
    result = []
    d_lst = []
    x, y = position[0], position[1]
    if player == 'r':
        assert position in state.red
        if 0 <= (x + 1) <= 7 and 0 <= (y - 1) <= 7:
            d_lst.insert(0, (x + 1, y - 1))
        if 0 <= (x - 1) <= 7 and 0 <= (y - 1) <= 7:
            d_lst.insert(0, (x - 1, y - 1))
        if state.red[position] == 'R':
            if 0 <= (x + 1) <= 7 and 0 <= (y + 1) <= 7:
                d_lst.insert(0, (x + 1, y + 1))
            if 0 <= (x - 1) <= 7 and 0 <= (y + 1) <= 7:
                d_lst.insert(0, (x - 1, y + 1))

        for destination in d_lst:
            next_state = clone(state)
            curr_position = next_state.move(position, destination)
            if next_state != state:
                if destination != curr_position:
                    if state.red[position] != next_state.red[curr_position]:
                        if next_state not in result:
                            result.append(next_state)
                    else:
                        multi_return = multi_jump(next_state, curr_position,
                                                  get_surr(next_state, curr_position, player),
                                                  player, next_state.red[curr_position])
                        for s in multi_return:
                            if s not in result:
                                result.append(s)
                else:
                    if next_state not in result:
                        result.append(next_state)
    else:
        assert position in state.black
        if 0 <= (x + 1) <= 7 and 0 <= (y + 1) <= 7:
            d_lst.insert(0,(x + 1, y + 1))
        if 0 <= (x - 1) <= 7 and 0 <= (y + 1) <= 7:
            d_lst.insert(0,(x - 1, y + 1))


        if state.black[position] == 'B':
            if 0 <= (x + 1) <= 7 and 0 <= (y - 1) <= 7:
                d_lst.insert(0, (x + 1, y - 1))
            if 0 <= (x - 1) <= 7 and 0 <= (y - 1) <= 7:
                d_lst.insert(0, (x - 1, y - 1))


        for destination in d_lst:
            next_state = clone(state)
            curr_position = next_state.move(position, destination)
            if next_state != state:
                if destination != curr_position:
                    if state.black[position] != next_state.black[curr_position]:
                        if next_state not in result:
                            result.append(next_state)
                    else:
                        multi_return = multi_jump(next_state, curr_position,
                                                  get_surr(next_state, curr_position, player),
                                                  player, next_state.black[curr_position])
                        for s in multi_return:
                            if s not in result:
                                result.append(s)
                else:
                    if next_state not in result:
                        result.append(next_state)
    return result


def multi_jump(state: State, position: tuple,
               surr: list[tuple], player: str, chess: str) -> list[State]:
    result = []
    if not surr:
        return [state]
    else:
        for neighbour in surr:
            next_state = clone(state)
            curr_pos = next_state.move(position, neighbour)
            if state != next_state:
                if (chess == 'r' and curr_pos[1] == 0) or (chess == 'b' and curr_pos[1] == 7):
                    if next_state not in result:
                        result.append(next_state)
                else:
                    multi_return = multi_jump(next_state, curr_pos,
                                              get_surr(next_state, curr_pos, player), player, chess)
                    for s in multi_return:
                        if s not in result:
                            result.append(s)
            else:
                if next_state not in result:
                    result.append(next_state)
        return result


def get_surr(state: State, position: tuple, player: str):
    result = []
    x, y = position[0], position[1]
    if player == 'r':
        if 0 <= (x - 1) <= 7 and 0 <= (y - 1) <= 7 and \
                (x - 1, y - 1) in state.black:
            result.append((x - 1, y - 1))
        if 0 <= (x + 1) <= 7 and 0 <= (y - 1) <= 7 and \
                (x + 1, y - 1) in state.black:
            result.append((x + 1, y - 1))

        if state.red[position] == 'R':
            if 0 <= (x - 1) <= 7 and 0 <= (y + 1) <= 7 and \
                    (x - 1, y + 1) in state.black:
                result.append((x - 1, y + 1))
            if 0 <= (x + 1) <= 7 and 0 <= (y + 1) <= 7 and \
                    (x + 1, y + 1) in state.black:
                result.append((x + 1, y + 1))
    else:
        if 0 <= (x - 1) <= 7 and 0 <= (y + 1) <= 7 and \
                (x - 1, y + 1) in state.red:
            result.append((x - 1, y + 1))
        if 0 <= (x + 1) <= 7 and 0 <= (y + 1) <= 7 and \
                (x + 1, y + 1) in state.red:
            result.append((x + 1, y + 1))

        if state.black[position] == 'B':
            if 0 <= (x - 1) <= 7 and 0 <= (y - 1) <= 7 and \
                    (x - 1, y - 1) in state.red:
                result.append((x - 1, y - 1))
            if 0 <= (x + 1) <= 7 and 0 <= (y - 1) <= 7 and \
                    (x + 1, y - 1) in state.red:
                result.append((x + 1, y - 1))
    return result


def clone(state: State) -> State:
    c = State()
    for key in state.red:
        c.red[key] = state.red[key]
    for key in state.black:
        c.black[key] = state.black[key]
    return c


def utility(state: State) -> float:
    value = 0
    for key in state.red:
        if state.red[key] == 'r':
            value += 1
        else:
            value += 2
    for key in state.black:
        if state.black[key] == 'b':
            value -= 1
        else:
            value -= 2
    return value


def alphabeta(state, depth, alpha, beta, maximizing_player, evl_fn, cache):
    if depth == 0 or terminal(state):
        return evl_fn(state), None
    if state.display() in cache:
        return cache[state.display()], None

    if maximizing_player:
        value = -math.inf
        best_move = None
        spr_lst = spread(state, 'r')
        spr_lst = helper_sort(spr_lst, True)
        for child_state in spr_lst:
            child_value, _ = alphabeta(child_state, depth - 1, alpha, beta, False, evl_fn, cache)
            if child_value > value:
                value = child_value
                best_move = child_state
            alpha = max(alpha, value)
            if alpha >= beta:
                break
        cache[state.display()] = value
        return value, best_move
    else:
        value = math.inf
        best_move = None
        spr_lst = spread(state, 'b')
        spr_lst = helper_sort(spr_lst, False)
        for child_state in spr_lst:
            if child_state.display() in cache:
                continue
            child_value, _ = alphabeta(child_state, depth - 1, alpha, beta, True, evl_fn, cache)
            if child_value < value:
                value = child_value
                best_move = child_state
            beta = min(beta, value)
            if alpha >= beta:
                break
        cache[state.display()] = value
        return value, best_move


def helper_sort(ex_lst: list[State], reverse: bool) -> list[State]:
    return sorted(ex_lst, key=utility, reverse=reverse)


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--inputfile",
        type=str,
        required=True,
        help="The input file that contains the puzzles."
    )
    parser.add_argument(
        "--outputfile",
        type=str,
        required=True,
        help="The output file that contains the solution."
    )
    args = parser.parse_args()

    initial_state = read_from_file(args.inputfile)

    cache = {}
    player = True
    x = 8
    result_list = [initial_state]
    next_successor = alphabeta(initial_state, x, -math.inf, math.inf, player, utility, cache)[1]
    result_list.append(next_successor)
    print(next_successor.display())
    while next_successor is not None:
        cache = {}
        if player:
            player = False
        elif not player:
            player = True
        temp = alphabeta(next_successor, x, -math.inf, math.inf, player, utility, cache)
        print(temp)
        print(next_successor.display())
        next_successor = temp[1]

        if next_successor is not None:
            result_list.append(next_successor)

    sys.stdout = open(args.outputfile, 'w')
    for item in result_list:
        sys.stdout.write(item.display())
        sys.stdout.write('\n')
    sys.stdout.close()

