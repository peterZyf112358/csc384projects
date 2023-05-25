import argparse
import sys
import copy


class Variable:
    '''Class for defining CSP variables.

      On initialization the variable object can be given a name and a
      list containing variable's domain of values. You can reset the
      variable's domain if you want to solve a similar problem where
      the domains have changed.

      To support CSP propagation, the class also maintains a current
      domain for the variable. Values pruned from the variable domain
      are removed from the current domain but not from the original
      domain. Values can be also restored.
    '''

    undoDict = dict()  # stores pruned values indexed by a

    # (variable,value) reason pair
    def __init__(self, name, domain):

        '''Create a variable object, specifying its name (a
        string) and domain of values.
        使用给定的名称和域初始化一个新的变量对象。
        '''
        self._name = name  # text name for variable
        self._dom = list(domain)  # Make a copy of passed domain
        self._curdom = list(domain)  # using list
        self._value = None

    def __str__(self):
        return "Variable {}".format(self._name)

    def domain(self):
        '''return copy of variable domain
        返回变量的原始域的副本'''
        return (list(self._dom))

    def domainSize(self):
        '''Return the size of the domain
        返回 domain 的大小'''
        return (len(self.domain()))

    def resetDomain(self, newdomain):
        '''reset the domain of this variable
        把domain变成新域'''
        self._dom = newdomain

    def getValue(self):
        '''返回value的值'''
        return self._value

    def setValue(self, value):
        '''设置value'''
        if value != None and not value in self._dom:
            print("Error: tried to assign value {} to variable {} that is not in {}'s domain".format(value, self._name,
                                                                                                     self._name))
        else:
            self._value = value

    def unAssign(self):
        '''取消value的赋值'''
        self.setValue(None)

    def isAssigned(self):
        '''返回value是不是等于None'''
        return self.getValue() != None

    def name(self):
        return self._name

    def curDomain(self):
        '''return copy of variable current domain. But if variable is assigned
           return just its assigned value (this makes implementing hasSupport easier
           返回变量的当前域的副本，它会在修剪值时更新
           '''
        if self.isAssigned():
            return ([self.getValue()])
        return (list(self._curdom))

    def curDomainSize(self):
        '''Return the size of the current domain
            返回curDomain的size，如果assign了return1
            如果没，return self._curdom的size'''
        if self.isAssigned():
            return (1)
        return (len(self._curdom))

    def inCurDomain(self, value):
        '''check if value is in current domain
        查value是不是在 cur_dom'''
        if self.isAssigned():
            return (value == self.getValue())
        return (value in self._curdom)

    def pruneValue(self, value, reasonVar, reasonVal):
        '''Remove value from current domain
        在curdom里删除一个value
        如果(resonVar, reasonVal）不在 undoDict
        创建一个，然后把value加在 (resonVar, reasonVal）的list里'''
        try:
            self._curdom.remove(value)
        except:
            print("Error: tried to prune value {} from variable {}'s domain, but value not present!".format(value,
                                                                                                            self._name))
        dkey = (reasonVar, reasonVal)
        if not dkey in Variable.undoDict:
            Variable.undoDict[dkey] = []
        Variable.undoDict[dkey].append((self, value))

    def restoreVal(self, value):
        '''将修剪的值恢复到变量的当前域'''
        self._curdom.append(value)

    def restoreCurDomain(self):
        '''将变量的当前域恢复为其原始域'''
        self._curdom = self.domain()

    def reset(self):
        '''通过恢复其当前域和取消分配其值来重置变量'''
        self.restoreCurDomain()
        self.unAssign()

    def dumpVar(self):
        '''打印变量名称、分配值、域和当前域的字符串表示形式'''
        print("Variable\"{}={}\": Dom = {}, CurDom = {}".format(self._name, self._value, self._dom, self._curdom))

    @staticmethod
    def clearUndoDict():
        '''清除用于存储修剪值及其原因的静态字典'''
        undoDict = dict()

    @staticmethod
    def restoreValues(reasonVar, reasonVal):
        '''将与给定原因变量和值相关联的所有修剪值恢复'''
        dkey = (reasonVar, reasonVal)
        if dkey in Variable.undoDict:
            for (var, val) in Variable.undoDict[dkey]:
                var.restoreVal(val)
            del Variable.undoDict[dkey]


# implement various types of constraints
class Constraint:
    '''Base class for defining constraints. Each constraint can check if
       it has been satisfied, so each type of constraint must be a
       different class. For example a constraint of notEquals(V1,V2)
       must be a different class from a constraint of
       greaterThan(V1,V2), as they must implement different checks of
       satisfaction.

       However one can define a class of general table constraints, as
       below, that can capture many different constraints.

       On initialization the constraint's name can be given as well as
       the constraint's scope. IMPORTANT, the scope is ordered! E.g.,
       the constraint greaterThan(V1,V2) is not the same as the
       contraint greaterThan(V2,V1).
    '''

    def __init__(self, name, scope):
        '''create a constraint object, specify the constraint name (a
        string) and its scope (an ORDERED list of variable
        objects).'''
        self._scope = list(scope)
        self._name = "baseClass_" + name  # override in subconstraint types!

    def scope(self):
        return list(self._scope)

    def arity(self):
        return len(self._scope)

    def numUnassigned(self):
        i = 0
        for var in self._scope:
            if not var.isAssigned():
                i += 1
        return i

    def unAssignedVars(self):
        return [var for var in self.scope() if not var.isAssigned()]

    # def check(self):
    #     util.raiseNotDefined()

    def name(self):
        return self._name

    def __str__(self):
        return "Cnstr_{}({})".format(self.name(), map(lambda var: var.name(), self.scope()))

    def printConstraint(self):
        print("Cons: {} Vars = {}".format(
            self.name(), [v.name() for v in self.scope()]))


# object for holding a constraint problem
class CSP:
    '''CSP class groups together a set of variables and a set of
       constraints to form a CSP problem. Provides a usesful place
       to put some other functions that depend on which variables
       and constraints are active'''

    def __init__(self, name, variables, constraints):
        '''create a CSP problem object passing it a name, a list of
           variable objects, and a list of constraint objects'''
        self._name = name
        self._variables = variables
        self._constraints = constraints
        self.size = 0
        self.solutions = []
        self.count = 0

        # some sanity checks
        varsInCnst = set()
        for c in constraints:
            varsInCnst = varsInCnst.union(c.scope())
        for v in variables:
            if v not in varsInCnst:
                print("Warning: variable {} is not in any constraint of the CSP {}".format(v.name(), self.name()))
        for v in varsInCnst:
            if v not in variables:
                print(
                    "Error: variable {} appears in constraint but specified as one of the variables of the CSP {}".format(
                        v.name(), self.name()))

        self.constraints_of = [[] for i in range(len(variables))]
        for c in constraints:
            for v in c.scope():
                i = variables.index(v)
                self.constraints_of[i].append(c)

    def name(self):
        return self._name

    def variables(self):
        return list(self._variables)

    def constraints(self):
        return list(self._constraints)

    def constraintsOf(self, var):
        '''return constraints with var in their scope'''
        try:
            i = self.variables().index(var)
            return list(self.constraints_of[i])
        except:
            print("Error: tried to find constraint of variable {} that isn't in this CSP {}".format(var, self.name()))

    def unAssignAllVars(self):
        '''unassign all variables'''
        for v in self.variables():
            v.unAssign()

    def check(self, solutions):
        '''each solution is a list of (var, value) pairs. Check to see
           if these satisfy all the constraints. Return list of
           erroneous solutions'''

        # save values to restore later
        current_values = [(var, var.getValue()) for var in self.variables()]
        errs = []

        for s in solutions:
            s_vars = [var for (var, val) in s]

            if len(s_vars) != len(self.variables()):
                errs.append([s, "Solution has incorrect number of variables in it"])
                continue

            if len(set(s_vars)) != len(self.variables()):
                errs.append([s, "Solution has duplicate variable assignments"])
                continue

            if set(s_vars) != set(self.variables()):
                errs.append([s, "Solution has incorrect variable in it"])
                continue

            for (var, val) in s:
                var.setValue(val)

            for c in self.constraints():
                if not c.check():
                    errs.append([s, "Solution does not satisfy constraint {}".format(c.name())])
                    break

        for (var, val) in current_values:
            var.setValue(val)

        return errs

    def __str__(self):
        return "CSP {}".format(self.name())


class TableConstraint(Constraint):
    '''General type of constraint that can be use to implement any type of
       constraint. But might require a lot of space to do so.

       A table constraint explicitly stores the set of satisfying
       tuples of assignments.'''

    def __init__(self, name, scope, satisfyingAssignments):
        '''Init by specifying a name and a set variables the constraint is over.
           Along with a list of satisfying assignments.
           Each satisfying assignment is itself a list, of length equal to
           the number of variables in the constraints scope.
           If sa is a single satisfying assignment, e.g, sa=satisfyingAssignments[0]
           then sa[i] is the value that will be assigned to the variable scope[i].


           Example, say you want to specify a constraint alldiff(A,B,C,D) for
           three variables A, B, C each with domain [1,2,3,4]
           Then you would create this constraint using the call
           c = TableConstraint('example', [A,B,C,D],
                               [[1, 2, 3, 4], [1, 2, 4, 3], [1, 3, 2, 4],
                                [1, 3, 4, 2], [1, 4, 2, 3], [1, 4, 3, 2],
                                [2, 1, 3, 4], [2, 1, 4, 3], [2, 3, 1, 4],
                                [2, 3, 4, 1], [2, 4, 1, 3], [2, 4, 3, 1],
                                [3, 1, 2, 4], [3, 1, 4, 2], [3, 2, 1, 4],
                                [3, 2, 4, 1], [3, 4, 1, 2], [3, 4, 2, 1],
                                [4, 1, 2, 3], [4, 1, 3, 2], [4, 2, 1, 3],
                                [4, 2, 3, 1], [4, 3, 1, 2], [4, 3, 2, 1]])
          as these are the only assignments to A,B,C respectively that
          satisfy alldiff(A,B,C,D)
        '''

        Constraint.__init__(self, name, scope)
        self._name = "TableCnstr_" + name
        self.satAssignments = satisfyingAssignments

    def check(self):
        '''check if current variable assignments are in the satisfying set'''
        assignments = []
        for v in self.scope():
            if v.isAssigned():
                assignments.append(v.getValue())
            else:
                return True
        return assignments in self.satAssignments

    def hasSupport(self, var, val):
        '''check if var=val has an extension to an assignment of all variables in
           constraint's scope that satisfies the constraint. Important only to
           examine values in the variable's current domain as possible extensions'''
        if var not in self.scope():
            return True  # var=val has support on any constraint it does not participate in
        vindex = self.scope().index(var)
        found = False
        for assignment in self.satAssignments:
            if assignment[vindex] != val:
                continue  # this assignment can't work it doesn't make var=val
            found = True  # Otherwise it has potential. Assume found until shown otherwise
            for i, v in enumerate(self.scope()):
                if i != vindex and not v.inCurDomain(assignment[i]):
                    found = False  # Bummer...this assignment didn't work it assigns
                    break  # a value to v that is not in v's curDomain
                    # note we skip checking if val in in var's curDomain
            if found:  # if found still true the assigment worked. We can stop
                break
        return found  # either way found has the right truth value


def findvals(remainingVars, assignment, finalTestfn, partialTestfn=lambda x: True):
    '''Helper function for finding an assignment to the variables of a constraint
       that together with var=val satisfy the constraint. That is, this
       function looks for a supporing tuple.

       findvals uses recursion to build up a complete assignment, one value
       from every variable's current domain, along with var=val.

       It tries all ways of constructing such an assignment (using
       a recursive depth-first search).

       If partialTestfn is supplied, it will use this function to test
       all partial assignments---if the function returns False
       it will terminate trying to grow that assignment.

       It will test all full assignments to "allVars" using finalTestfn
       returning once it finds a full assignment that passes this test.

       returns True if it finds a suitable full assignment, False if none
       exist. (yes we are using an algorithm that is exactly like backtracking!)'''

    # print "==>findvars([",
    # for v in remainingVars: print v.name(), " ",
    # print "], [",
    # for x,y in assignment: print "({}={}) ".format(x.name(),y),
    # print ""

    # sort the variables call the internal version with the variables sorted
    remainingVars.sort(reverse=True, key=lambda v: v.curDomainSize())
    return findvals_(remainingVars, assignment, finalTestfn, partialTestfn)

def findvals_(remainingVars, assignment, finalTestfn, partialTestfn):
    '''findvals_ internal function with remainingVars sorted by the size of
       their current domain'''
    if len(remainingVars) == 0:
        return finalTestfn(assignment)
    var = remainingVars.pop()
    for val in var.curDomain():
        assignment.append((var, val))
        if partialTestfn(assignment):
            if findvals_(remainingVars, assignment, finalTestfn, partialTestfn):
                return True
        assignment.pop()  # (var,val) didn't work since we didn't do the return
    remainingVars.append(var)
    return False


class NValuesConstraint(Constraint):
    '''NValues constraint over a set of variables.  Among the variables in
       the constraint's scope the number that have been assigned
       values in the set 'required_values' is in the range
       [lower_bound, upper_bound] (lower_bound <= #of variables
       assigned 'required_value' <= upper_bound)

       For example, if we have 4 variables V1, V2, V3, V4, each with
       domain [1, 2, 3, 4], then the call
       NValuesConstraint('test_nvalues', [V1, V2, V3, V4], [1,4], 2,
       3) will only be satisfied by assignments such that at least 2
       the V1, V2, V3, V4 are assigned the value 1 or 4, and at most 3
       of them have been assigned the value 1 or 4.

    '''

    def __init__(self, name, scope, required_values, lower_bound, upper_bound):
        Constraint.__init__(self, name, scope)
        self._name = "NValues_" + name
        self._required = required_values
        self._lb = lower_bound
        self._ub = upper_bound

    def check(self):
        assignments = []
        for v in self.scope():
            if v.isAssigned():
                assignments.append(v.getValue())
            else:
                return True
        rv_count = 0

        # print "Checking {} with assignments = {}".format(self.name(), assignments)

        for v in assignments:
            if v in self._required:
                rv_count += 1

        # print "rv_count = {} test = {}".format(rv_count, self._lb <= rv_count and self._ub >= rv_count)

        return self._lb <= rv_count and self._ub >= rv_count

    def hasSupport(self, var, val):
        '''check if var=val has an extension to an assignment of the
           other variable in the constraint that satisfies the constraint

           HINT: check the implementation of AllDiffConstraint.hasSupport
                 a similar approach is applicable here (but of course
                 there are other ways as well)
        '''
        if var not in self.scope():
            return True  # var=val has support on any constraint it does not participate in

        # define the test functions for findvals
        def valsOK(l):
            '''tests a list of assignments which are pairs (var,val)
               to see if they can satisfy this sum constraint'''
            rv_count = 0
            vals = [val for (var, val) in l]
            for v in vals:
                if v in self._required:
                    rv_count += 1
            least = rv_count + self.arity() - len(vals)
            most = rv_count
            return self._lb <= least and self._ub >= most

        varsToAssign = self.scope()
        varsToAssign.remove(var)
        x = findvals(varsToAssign, [(var, val)], valsOK, valsOK)
        return x


class IfAllThenOneConstraint(Constraint):
    '''if each variable in left_side equals each value in left_values
    then one of the variables in right side has to equal one of the values in right_values.
    hasSupport tested only, check() untested.'''

    def __init__(self, name, left_side, right_side, left_values, right_values):
        Constraint.__init__(self, name, left_side + right_side)
        self._name = "IfAllThenOne_" + name
        self._ls = left_side
        self._rs = right_side
        self._lv = left_values
        self._rv = right_values


#code start here
def constraint_creat(board, row_con, col_con, var_dict):
    size = len(board[0])
    constraints = []
    for y in range(size):
        y_row = []
        x_col = []
        ships_row = ['S', '<', '>', '^', 'v', 'M']
        ships_col = ['S', '<', '>', '^', 'v', 'M']
        for x in range(size):
            y_row.append(var_dict[str(y * size + x)])
            x_col.append(var_dict[str(y + x * size)])
            # Create water/proper ship formation constraints using binary table constraints
            constraints += arround_check(board, y, x, var_dict)

        if y == 0:
            # first row and column
            ships_row.remove('v')
            ships_col.remove('>')
        elif y == size - 1:
            # last row and column
            ships_row.remove('^')
            ships_col.remove('<')

        constraints.append(NValuesConstraint('row_' + str(y), y_row, ships_row, row_con[y], row_con[y]))
        constraints.append(NValuesConstraint('col_' + str(y), x_col, ships_col, col_con[y], col_con[y]))

    return constraints

def item_creation(board):
    size = len(board[0])
    item_list = []
    var_dict = {}
    # y = row, x = column
    for y in range(size):
        for x in range(size):
            if board[y][x] != '0':
                v = Variable(str(y * size + x), [board[y][x]])
            else:
                v = Variable(str(y * size + x), ['S', '.', '<', '>', '^', 'v', 'M'])

            item_list.append(v)
            var_dict[str(y * size + x)] = v

    return item_list, var_dict


def arround_check(board, row, col, var_dict):
    M = len(board[0])
    constraint = []
    if row == 0 and col == 0:
        # right
        constraint.append(TableConstraint('box_' + str(row) + str(col) + '_and_' + str(row) + str(col + 1),
                                          [var_dict[str(row * M + col)], var_dict[str((row) * M + col + 1)]],
                                          [['S', '.'], ['.', '^'], ['.', '<'], ['.', 'S'], ['.', '.'], ['<', '>'],
                                           ['<', 'M'], ['^', '.']]))
        #  down right
        constraint.append(TableConstraint('box_' + str(row) + str(col) + '_and_' + str(row + 1) + str(col + 1),
                                          [var_dict[str(row * M + col)], var_dict[str((row + 1) * M + col + 1)]],
                                          [['S', '.'], ['.', '^'], ['.', 'v'], ['.', '<'], ['.', 'S'], ['.', '.'],
                                           ['.', 'M'], ['.', '>'], ['<', '.'], ['^', '.']]))
        # down
        constraint.append(TableConstraint('box_' + str(row) + str(col) + '_and_' + str(row + 1) + str(col),
                                          [var_dict[str(row * M + col)], var_dict[str((row + 1) * M + col)]],
                                          [['S', '.'], ['.', '^'], ['.', '<'], ['.', 'S'], ['.', '.'], ['<', '.'],
                                           ['^', 'v'], ['^', 'M']]))
    elif row == 0 and col == M - 1:
        # left
        constraint.append(TableConstraint('box_' + str(row) + str(col) + '_and_' + str(row) + str(col - 1),
                                          [var_dict[str(row * M + col)], var_dict[str((row) * M + col - 1)]],
                                          [['S', '.'], ['.', '^'], ['.', '>'], ['.', 'S'], ['.', '.'], ['>', '<'],
                                           ['>', 'M'], ['^', '.']]))
        #  down left
        constraint.append(TableConstraint('box_' + str(row) + str(col) + '_and_' + str(row + 1) + str(col - 1),
                                          [var_dict[str(row * M + col)], var_dict[str((row + 1) * M + col - 1)]],
                                          [['S', '.'], ['.', '^'], ['.', 'v'], ['.', '<'], ['.', 'S'], ['.', '.'],
                                           ['.', 'M'], ['.', '>'], ['>', '.'], ['^', '.']]))
        # down
        constraint.append(TableConstraint('box_' + str(row) + str(col) + '_and_' + str(row + 1) + str(col),
                                          [var_dict[str(row * M + col)], var_dict[str((row + 1) * M + col)]],
                                          [['S', '.'], ['.', '^'], ['.', '>'], ['.', 'S'], ['.', '.'], ['>', '.'],
                                           ['^', 'v'], ['^', 'M']]))

    elif row == M - 1 and col == 0:
        # right
        constraint.append(TableConstraint('box_' + str(row) + str(col) + '_and_' + str(row) + str(col + 1),
                                          [var_dict[str(row * M + col)], var_dict[str((row) * M + col + 1)]],
                                          [['S', '.'], ['.', 'v'], ['.', '<'], ['.', 'S'], ['.', '.'], ['<', '>'],
                                           ['<', 'M'], ['v', '.']]))
        # top right
        constraint.append(TableConstraint('box_' + str(row) + str(col) + '_and_' + str(row - 1) + str(col + 1),
                                          [var_dict[str(row * M + col)], var_dict[str((row - 1) * M + col + 1)]],
                                          [['S', '.'], ['.', '^'], ['.', 'v'], ['.', '<'], ['.', 'S'], ['.', '.'],
                                           ['.', 'M'], ['.', '>'], ['<', '.'], ['v', '.']]))
        # top
        constraint.append(TableConstraint('box_' + str(row) + str(col) + '_and_' + str(row - 1) + str(col),
                                          [var_dict[str(row * M + col)], var_dict[str((row - 1) * M + col)]],
                                          [['S', '.'], ['.', 'v'], ['.', '<'], ['.', 'S'], ['.', '.'], ['<', '.'],
                                           ['v', '^'], ['v', 'M']]))
    elif row == M - 1 and col == M - 1:
        # left
        constraint.append(TableConstraint('box_' + str(row) + str(col) + '_and_' + str(row) + str(col - 1),
                                          [var_dict[str(row * M + col)], var_dict[str((row) * M + col - 1)]],
                                          [['S', '.'], ['.', 'v'], ['.', '>'], ['.', 'S'], ['.', '.'], ['>', '<'],
                                           ['>', 'M'], ['v', '.']]))

        # top left
        constraint.append(TableConstraint('box_' + str(row) + str(col) + '_and_' + str(row - 1) + str(col - 1),
                                          [var_dict[str(row * M + col)], var_dict[str((row - 1) * M + col - 1)]],
                                          [['S', '.'], ['.', '^'], ['.', 'v'], ['.', '<'], ['.', 'S'], ['.', '.'],
                                           ['.', 'M'], ['.', '>'], ['>', '.'], ['v', '.']]))

        # top
        constraint.append(TableConstraint('box_' + str(row) + str(col) + '_and_' + str(row - 1) + str(col),
                                          [var_dict[str(row * M + col)], var_dict[str((row - 1) * M + col)]],
                                          [['S', '.'], ['.', 'v'], ['.', '>'], ['.', 'S'], ['.', '.'], ['>', '.'],
                                           ['v', '^'], ['v', 'M']]))
    elif row == 0:
        # down
        constraint.append(TableConstraint('box_' + str(row) + str(col) + '_and_' + str(row + 1) + str(col),
                                          [var_dict[str(row * M + col)], var_dict[str((row + 1) * M + col)]],
                                          [['S', '.'], ['.', '^'], ['.', '>'], ['.', '<'], ['.', 'S'], ['.', '.'],
                                           ['.', 'M'], ['>', '.'], ['^', 'v'], ['^', 'M'], ['<', '.'], ['M', '.']]))
        # left
        constraint.append(TableConstraint('box_' + str(row) + str(col) + '_and_' + str(row) + str(col - 1),
                                          [var_dict[str(row * M + col)], var_dict[str(row * M + col - 1)]],
                                          [['S', '.'], ['.', '^'], ['.', '>'], ['.', 'S'], ['.', '.'], ['>', '<'],
                                           ['>', 'M'], ['^', '.'], ['<', '.'], ['M', '<'], ['M', 'M']]))
        # right
        constraint.append(TableConstraint('box_' + str(row) + str(col) + '_and_' + str(row) + str(col + 1),
                                          [var_dict[str(row * M + col)], var_dict[str(row * M + col + 1)]],
                                          [['S', '.'], ['.', '^'], ['.', '<'], ['.', 'S'], ['.', '.'], ['<', '>'],
                                           ['<', 'M'], ['^', '.'], ['>', '.'], ['M', '>'], ['M', 'M']]))
        #  down left
        constraint.append(TableConstraint('box_' + str(row) + str(col) + '_and_' + str(row + 1) + str(col - 1),
                                          [var_dict[str(row * M + col)], var_dict[str((row + 1) * M + col - 1)]],
                                          [['S', '.'], ['.', '^'], ['.', 'v'], ['.', '<'], ['.', 'S'], ['.', '.'],
                                           ['.', 'M'], ['.', '>'], ['>', '.'], ['^', '.'], ['<', '.'], ['M', '.']]))
        #  down right
        constraint.append(TableConstraint('box_' + str(row) + str(col) + '_and_' + str(row + 1) + str(col + 1),
                                          [var_dict[str(row * M + col)], var_dict[str((row + 1) * M + col + 1)]],
                                          [['S', '.'], ['.', '^'], ['.', 'v'], ['.', '<'], ['.', 'S'], ['.', '.'],
                                           ['.', 'M'], ['.', '>'], ['>', '.'], ['^', '.'], ['<', '.'], ['M', '.']]))

    elif row == M - 1:
        # top
        constraint.append(TableConstraint('box_' + str(row) + str(col) + '_and_' + str(row - 1) + str(col),
                                          [var_dict[str(row * M + col)], var_dict[str((row - 1) * M + col)]],

                                          [['S', '.'], ['.', 'v'], ['.', '>'], ['.', '<'], ['.', 'S'], ['.', '.'],
                                           ['.', 'M'], ['>', '.'], ['<', '.'], ['v', '^'], ['v', 'M'], ['M', '.']]))

        # left
        constraint.append(TableConstraint('box_' + str(row) + str(col) + '_and_' + str(row) + str(col - 1),
                                          [var_dict[str(row * M + col)], var_dict[str(row * M + col - 1)]],

                                          [['S', '.'], ['.', 'v'], ['.', '>'], ['.', 'S'], ['.', '.'], ['>', '<'],
                                           ['>', 'M'], ['v', '.'], ['<', '.'], ['M', '<'], ['M', 'M']]))

        # right
        constraint.append(TableConstraint('box_' + str(row) + str(col) + '_and_' + str(row) + str(col + 1),
                                          [var_dict[str(row * M + col)], var_dict[str(row * M + col + 1)]],

                                          [['S', '.'], ['.', 'v'], ['.', '<'], ['.', 'S'], ['.', '.'], ['<', '>'],
                                           ['<', 'M'], ['v', '.'], ['>', '.'], ['M', '>'], ['M', 'M']]))

        #  top left
        constraint.append(TableConstraint('box_' + str(row) + str(col) + '_and_' + str(row - 1) + str(col - 1),
                                          [var_dict[str(row * M + col)], var_dict[str((row - 1) * M + col - 1)]],

                                          [['S', '.'], ['.', 'v'], ['.', '^'], ['.', '<'], ['.', 'S'], ['.', '.'],
                                           ['.', 'M'], ['.', '>'], ['>', '.'], ['v', '.'], ['<', '.'], ['M', '.']]))

        #  top right

        constraint.append(TableConstraint('box_' + str(row) + str(col) + '_and_' + str(row - 1) + str(col + 1),
                                          [var_dict[str(row * M + col)], var_dict[str((row - 1) * M + col + 1)]],

                                          [['S', '.'], ['.', 'v'], ['.', '^'], ['.', '<'], ['.', 'S'], ['.', '.'],
                                           ['.', 'M'], ['.', '>'], ['>', '.'], ['v', '.'], ['<', '.'], ['M', '.']]))

    elif col == 0:
        # down
        constraint.append(TableConstraint('box_' + str(row) + str(col) + '_and_' + str(row + 1) + str(col),
                                          [var_dict[str(row * M + col)], var_dict[str((row + 1) * M + col)]],
                                          [['S', '.'], ['.', '^'], ['.', '<'], ['.', 'S'], ['.', '.'], ['^', 'v'],
                                           ['^', 'M'], ['<', '.'], ['M', 'M'], ['M', 'v'], ['v', '.']]))
        # right
        constraint.append(TableConstraint('box_' + str(row) + str(col) + '_and_' + str(row) + str(col + 1),
                                          [var_dict[str(row * M + col)], var_dict[str(row * M + col + 1)]],
                                          [['S', '.'], ['.', 'v'], ['.', '<'], ['.', 'S'], ['.', '.'], ['<', '>'],
                                           ['<', 'M'], ['v', '.'], ['^', '.'], ['.', '^'], ['M', '.'], ['.', 'M']]))
        #  top right
        constraint.append(TableConstraint('box_' + str(row) + str(col) + '_and_' + str(row - 1) + str(col + 1),
                                          [var_dict[str(row * M + col)], var_dict[str((row - 1) * M + col + 1)]],
                                          [['S', '.'], ['.', 'v'], ['.', '^'], ['.', '<'], ['.', 'S'], ['.', '.'],
                                           ['.', 'M'], ['.', '>'], ['v', '.'], ['^', '.'], ['<', '.'], ['M', '.']]))
        #  down right
        constraint.append(TableConstraint('box_' + str(row) + str(col) + '_and_' + str(row + 1) + str(col + 1),
                                          [var_dict[str(row * M + col)], var_dict[str((row + 1) * M + col + 1)]],
                                          [['S', '.'], ['.', 'v'], ['.', '^'], ['.', '<'], ['.', 'S'], ['.', '.'],
                                           ['.', 'M'], ['.', '>'], ['v', '.'], ['^', '.'], ['<', '.'], ['M', '.']]))
        # top
        constraint.append(TableConstraint('box_' + str(row) + str(col) + '_and_' + str(row - 1) + str(col),
                                          [var_dict[str(row * M + col)], var_dict[str((row - 1) * M + col)]],
                                          [['S', '.'], ['.', 'v'], ['.', '<'], ['.', 'S'], ['.', '.'], ['v', '^'],
                                           ['v', 'M'], ['<', '.'], ['M', 'M'], ['M', '^'], ['^', '.']]))
    elif col == M - 1:
        # left
        constraint.append(TableConstraint('box_' + str(row) + str(col) + '_and_' + str(row) + str(col - 1),
                                          [var_dict[str((row) * M + col)], var_dict[str((row) * M + col - 1)]],
                                          [['S', '.'], ['.', 'v'], ['.', '>'], ['.', 'S'], ['.', '.'], ['>', '<'],
                                           ['>', 'M'], ['v', '.'], ['^', '.'], ['.', '^'], ['M', '.'], ['.', 'M']]))
        #  top left
        constraint.append(TableConstraint('box_' + str(row) + str(col) + '_and_' + str(row - 1) + str(col - 1),
                                          [var_dict[str((row) * M + col)], var_dict[str((row - 1) * M + col - 1)]],
                                          [['S', '.'], ['.', 'v'], ['.', '^'], ['.', '<'], ['.', 'S'], ['.', '.'],
                                           ['.', 'M'], ['.', '>'], ['v', '.'], ['^', '.'], ['>', '.'], ['M', '.']]))
        #  down left
        constraint.append(TableConstraint('box_' + str(row) + str(col) + '_and_' + str(row + 1) + str(col - 1),
                                          [var_dict[str((row) * M + col)], var_dict[str((row + 1) * M + col - 1)]],
                                          [['S', '.'], ['.', 'v'], ['.', '^'], ['.', '<'], ['.', 'S'], ['.', '.'],
                                           ['.', 'M'], ['.', '>'], ['v', '.'], ['^', '.'], ['>', '.'], ['M', '.']]))
        # top
        constraint.append(TableConstraint('box_' + str(row) + str(col) + '_and_' + str(row - 1) + str(col),
                                          [var_dict[str((row) * M + col)], var_dict[str((row - 1) * M + col)]],
                                          [['S', '.'], ['.', 'v'], ['.', '>'], ['.', 'S'], ['.', '.'], ['v', '^'],
                                           ['v', 'M'], ['>', '.'], ['M', 'M'], ['M', '^'], ['^', '.']]))
        # down
        constraint.append(TableConstraint('box_' + str(row) + str(col) + '_and_' + str(row + 1) + str(col),
                                          [var_dict[str((row) * M + col)], var_dict[str((row + 1) * M + col)]],
                                          [['S', '.'], ['.', '^'], ['.', '>'], ['.', 'S'], ['.', '.'], ['^', 'v'],
                                           ['^', 'M'], ['>', '.'], ['M', 'M'], ['M', 'v'], ['v', '.']]))

    else:
        # right
        constraint.append(TableConstraint('box_' + str(row) + str(col) + '_and_' + str(row) + str(col + 1),
                                          [var_dict[str((row) * M + col)], var_dict[str((row) * M + col + 1)]],
                                          [['S', '.'], ['.', 'v'], ['.', '<'], ['.', 'S'], ['.', '.'], ['<', '>'],
                                           ['<', 'M'], ['v', '.'], ['^', '.'], ['.', '^'], ['M', '.'],
                                           ['.', 'M'], ['>', '.'], ['M', 'M'], ['M', '>']]))
        # left
        constraint.append(TableConstraint('box_' + str(row) + str(col) + '_and_' + str(row) + str(col - 1),
                                          [var_dict[str((row) * M + col)], var_dict[str((row) * M + col - 1)]],
                                          [['S', '.'], ['.', 'v'], ['.', '>'], ['.', 'S'], ['.', '.'], ['>', '<'],
                                           ['>', 'M'],
                                           ['v', '.'], ['^', '.'], ['.', '^'], ['M', '.'],
                                           ['.', 'M'], ['<', '.'], ['M', 'M'], ['M', '<']]))
        # up
        constraint.append(TableConstraint('box_' + str(row) + str(col) + '_and_' + str(row - 1) + str(col),
                                          [var_dict[str((row) * M + col)], var_dict[str((row - 1) * M + col)]],
                                          [['S', '.'], ['.', 'v'], ['.', '>'], ['.', '<'], ['.', 'S'], ['.', '.'],
                                           ['v', '^'],
                                           ['v', 'M'], ['>', '.'], ['M', 'M'], ['M', '^'], ['^', '.'],
                                           ['<', '.'], ['M', '.'], ['.', 'M']]))

        # down
        constraint.append(TableConstraint('box_' + str(row) + str(col) + '_and_' + str(row + 1) + str(col),
                                          [var_dict[str((row) * M + col)], var_dict[str((row + 1) * M + col)]],
                                          [['S', '.'], ['.', '^'], ['.', '>'], ['.', '<'], ['.', 'S'], ['.', '.'],
                                           ['^', 'v'],
                                           ['^', 'M'], ['>', '.'], ['M', 'M'], ['M', 'v'], ['v', '.'],
                                           ['<', '.'], ['M', '.'], ['.', 'M']]))
        # diag up right
        constraint.append(TableConstraint('box_' + str(row) + str(col) + '_and_' + str(row - 1) + str(col + 1),
                                          [var_dict[str((row) * M + col)], var_dict[str((row - 1) * M + col + 1)]],
                                          [['S', '.'], ['.', 'v'], ['.', '^'], ['.', '<'], ['.', 'S'], ['.', '.'],
                                           ['.', 'M'],
                                           ['.', '>'], ['v', '.'], ['^', '.'], ['<', '.'], ['M', '.'], ['>', '.']]))

        # diag up left
        constraint.append(TableConstraint('box_' + str(row) + str(col) + '_and_' + str(row - 1) + str(col - 1),
                                          [var_dict[str((row) * M + col)], var_dict[str((row - 1) * M + col - 1)]],
                                          [['S', '.'], ['.', 'v'], ['.', '^'], ['.', '<'], ['.', 'S'], ['.', '.'],
                                           ['.', 'M'],
                                           ['.', '>'], ['v', '.'], ['^', '.'], ['>', '.'], ['M', '.'], ['<', '.']]))

        # diag down left
        constraint.append(TableConstraint('box_' + str(row) + str(col) + '_and_' + str(row + 1) + str(col - 1),
                                          [var_dict[str((row) * M + col)], var_dict[str((row + 1) * M + col - 1)]],
                                          [['S', '.'], ['.', 'v'], ['.', '^'], ['.', '<'], ['.', 'S'], ['.', '.'],
                                           ['.', 'M'],
                                           ['.', '>'], ['v', '.'], ['^', '.'], ['>', '.'], ['M', '.'], ['<', '.']]))

        # diag down right
        constraint.append(TableConstraint('box_' + str(row) + str(col) + '_and_' + str(row + 1) + str(col + 1),
                                          [var_dict[str((row) * M + col)], var_dict[str((row + 1) * M + col + 1)]],
                                          [['S', '.'], ['.', 'v'], ['.', '^'], ['.', '<'], ['.', 'S'], ['.', '.'],
                                           ['.', 'M'],
                                           ['.', '>'], ['v', '.'], ['^', '.'], ['<', '.'], ['M', '.'], ['>', '.']]))

    return constraint


def shipNumberCheckCon(csp_, ship_cons):
    variables = csp_.variables()
    count = 0
    result = []
    size = csp_.size
    for y in range(size):
        add_row = []
        for x in range(size):
            add_row.append(count)
            count += 1
        result.append(add_row)
    for var in variables:
        var_pos = copy.copy(int(var.name()))
        col_ = var_pos % size
        row_ = var_pos // size
        result[row_][col_] = var.getValue()

    csp_.count += 1
    # check 'M' state ship
    for y in range(size):
        for x in range(size):
            # check M not at edges
            if result[y][x] == 'M' and y not in [0, size - 1] and x not in [0, size - 1]:
                # vertical ship
                if result[y][x - 1] == '.' and result[y][x + 1] == '.':
                    if result[y - 1][x] in ['M', '^'] and result[y + 1][x] in ['M', 'v']:
                        if result[y - 1][x] == 'M' and result[y + 1][x] != 'v':
                            return
                        if result[y + 1][x] == 'M' and result[y - 1][x] != '^':
                            return
                    else:
                        return
                # horizontal ship
                elif result[y - 1][x] == '.' and result[y + 1][x] == '.':
                    if result[y][x - 1] in ['M', '<'] and result[y][x + 1] in ['M', '>']:
                        if result[y][x - 1] == 'M' and result[y][x + 1] != '>':
                            return
                        if result[y][x + 1] == 'M' and result[y][x - 1] != '<':
                            return
                    else:
                        return

    # Now check if solution adheres to ship number constraint
    sub_ship = ship_cons[0]
    des_ship = ship_cons[1]
    cru_ship = ship_cons[2]
    bat_ship = ship_cons[3]

    sub_num = 0
    des_num = 0
    cru_num = 0
    bat_num = 0

    for y in range(size):
        for x in range(size):
            if sub_num > sub_ship or des_num > des_ship or cru_num > cru_ship or bat_num > bat_ship:
                # if any ship constraint not satisfied, return
                return
            if result[y][x] == 'S':
                sub_num += 1
            elif result[y][x] == 'M':
                # check for horizontal
                if result[y][x - 1] == '<' and result[y][x + 1] == '>':
                    cru_num += 1
                # check for vertical
                elif result[y - 1][x] == '^' and result[y + 1][x] == 'v':
                    cru_num += 1
            elif result[y][x] == '^' and result[y + 1][x] == 'v':
                des_num += 1
            elif result[y][x] == '<' and result[y][x + 1] == '>':
                des_num += 1
            elif result[y][x] == 'M' and result[y][x + 1] == 'M' and result[y][x - 1] == '<':
                bat_num += 1
            elif result[y][x] == 'M' and result[y - 1][x] == '^' and result[y + 1][x] == 'M':
                bat_num += 1
    if sub_num > sub_ship or des_num > des_ship or cru_num > cru_ship or bat_num > bat_ship:
        return
    csp_.solutions.append(result)


def AC3(unassignedVars, csp, ship_const):
    if not unassignedVars:
        shipNumberCheckCon(csp, ship_const)
        return
    # Assign a variable
    v = unassignedVars.pop(0)
    for val in v.curDomain():
        v.setValue(val)
        check = True
        if AC3helper(csp.constraintsOf(v), v, val, csp) == 'no_solution':
            check = False
        if check:
            AC3(unassignedVars, csp, ship_const)
        Variable.restoreValues(v, val)
    v.setValue(None)
    unassignedVars.append(v)
    return


def AC3helper(constraints, assvar, assval, csp):
    while constraints != []:
        cons = constraints.pop(0)
        for itme in cons.scope():
            # check each item satisfy the constraint
            for value in itme.curDomain():
                if not cons.hasSupport(itme, value):
                    itme.pruneValue(value, assvar, assval)
                    if itme.curDomainSize() == 0:
                        return 'no_solution'
                    for recheck in csp.constraintsOf(itme):
                        if recheck != cons and (not recheck in constraints):
                            constraints.append(recheck)
    return 'pass'


def board_creation(filename):
    f = open(filename)
    lines = f.readlines()
    count = 0
    board_ = []
    for line in lines:
        if count == 0:
            row_con = [int(x) for x in line.rstrip()]
            count += 1
        elif count == 1:
            col_con = [int(x) for x in line.rstrip()]
            count += 1
        elif count == 2:
            ship_con = [int(x) for x in line.rstrip()]
            count += 1
        else:
            board_ += [[str(x) for x in line.rstrip()]]
            count += 1
    f.close()

    return board_, row_con, col_con, ship_con


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

    board, row_con, col_con, ship_con = board_creation(args.inputfile)
    unassigned_vars, var_dict = item_creation(board)
    c = constraint_creat(board, row_con, col_con, var_dict)
    csp = CSP('battleship', unassigned_vars, c)
    csp.size = len(board[0])
    AC3(csp.variables(), csp, ship_con)
    sys.stdout = open(args.outputfile, 'w')
    for sol in csp.solutions:
        for row in sol:
            sys.stdout.writelines(row)
            sys.stdout.write("\n")

    sys.stdout.close()
