# --------------------------------------- Imports ---------------------------------------

from itertools import product
from numpy import array

# ---------------------------------------------------------------------------------------

# ----------------------------------- Helper Functions ----------------------------------

# Checks If A Given Variable Assignment Satisfies The Clause Set
def isSat(clauseSet, literalAssignment):
    for variable in literalAssignment:
        variableNegation = (-1 * variable)
        for i in range(len(clauseSet) - 1, -1, -1):
            clause = clauseSet[i]

            # If The Assignment Matches The Literal
            if variable in clause: clauseSet.remove(clause)

            # If The Assignment Matches The Negation Of The Literal
            while variableNegation in clause:
                clause.remove(variableNegation)

                # If, By Negation Elimination, The Clause Becomes Empty, Return UNSAT
                if len(clause) == 0:
                    return False

        # If All Clauses Are Satisfied
        if len(clauseSet) == 0:
            return True

# Get Number Of Variables In A Given Clause Set
def getNumVariables(clause_set):
    numVariables = 0
    for clause in clause_set:
        for literal in clause:
            if abs(literal) > numVariables:
                numVariables = abs(literal)
    return numVariables

# ---------------------------------------------------------------------------------------

# --------------------------------- Q3 - DIMACS Parser ----------------------------------

# Function To Parse DIMACS Files
def parseDIMACS(filename):
    clauseSet = [[]]

    # Load File
    with open(filename, "rt") as f:
        for line in f.readlines():
            lineElements = line.split()

            # Import Clause Data
            if lineElements[0] not in ["c", "p"]:
                for element in [int(i) for i in lineElements]:
                    if element != 0: clauseSet[-1].append(element)
                    else: clauseSet.append([])
    
    # Tidy Up
    if clauseSet[-1] == []:
        clauseSet.pop()

    return clauseSet

# ---------------------------------------------------------------------------------------

# ------------------------------- Q4 -> Q8 - SAT Solvers --------------------------------

# Basic Brute Force SAT Solver
def simple_sat_solve(clause_set):

    # Get Number Of Variables
    numVariables = getNumVariables(clause_set)

    # Test All Assignments
    baseList = array([i for i in range(1, numVariables + 1)])
    for i in product(*([[1, -1]] * numVariables)):
        literalAssignment = list(array(i) * baseList)

        # Check If Assignment Satifies The Problem
        if isSat([list(i) for i in clause_set], literalAssignment) == True:
            return literalAssignment

    # If No Assignments Satify The Problem, Return UNSAT
    return None

# Branching Sat Solver
def branching_sat_solve(clause_set, partial_assignment):

    # Reduce Clauses
    for literal in partial_assignment:
        for i in range(len(clause_set) - 1, -1, -1):
            clause = clause_set[i]
            if literal in clause: clause_set.remove(clause)
            while -literal in clause: clause.remove(-literal)

    # Check Base Cases
    if getNumVariables(clause_set) == 0:
        if len(clause_set) == 0: return partial_assignment
        else: return None
    else:
        # If Any Clauses Are Empty Due To Elimination Of Negated Literals, Return UNSAT
        if [] in clause_set: return None

        # Branch On +/- Literal;
        nextLiteral = abs(sum(clause_set, [])[0])
        for m in [1, -1]:
            literalAssignment = branching_sat_solve([list(c) for c in clause_set], [*partial_assignment, m*nextLiteral])
            if literalAssignment != None: return sorted(literalAssignment, key = abs)

        # If No Assignments Satify The Problem, Return UNSAT
        return None

# Applys Unit Propogation To A Clause Set
def unit_propagate(clause_set):
    newClauseSet = [list(c) for c in clause_set]

    # Apply Unit Propagation
    for unitClause in [clause for clause in clause_set if len(clause) == 1]:
        for clause in newClauseSet:
            if unitClause[0] in clause: newClauseSet.remove(clause)
            while -unitClause[0] in clause: clause.remove(-unitClause[0])
        newClauseSet.append(unitClause)

    # Recursion Check
    if sorted(newClauseSet) == sorted(clause_set): return clause_set
    else: return unit_propagate(newClauseSet)

# Applys Pure Literal Elimination
def pure_literal_eliminate(clause_set):

    # Find Pure Literals
    literalList = set(sum(clause_set, []))
    pureLiterals = [l for l in literalList if -l not in literalList]

    # Remove Cluases Containing Pure Literals
    newClauseSet = [list(c) for c in clause_set]
    for literal in pureLiterals:
        for i in range(len(newClauseSet) - 1, -1, -1):
            clause = newClauseSet[i]
            if literal in clause: newClauseSet.remove(clause)
        newClauseSet.append([literal])
    
    # Recursion Check
    if sorted(newClauseSet) == sorted(clause_set): return newClauseSet
    else: return pure_literal_eliminate(newClauseSet)

# DPLL Sat Solver
def dpll_sat_solve(clause_set, partial_assignment):

    # Apply Unit Propagation & Pure Literal Elimination
    clause_set = pure_literal_eliminate(unit_propagate(clause_set))

    # Reduce Clauses
    for literal in partial_assignment:
        for i in range(len(clause_set) - 1, -1, -1):
            clause = clause_set[i]
            if literal in clause: clause_set.remove(clause)
            while -literal in clause: clause.remove(-literal)

    # Check Base Cases
    if getNumVariables(clause_set) == 0:
        if len(clause_set) == 0: return partial_assignment
        else: return None
    else:
        # If Any Clauses Are Empty Due To Elimination Of Negated Literals, Return UNSAT
        if [] in clause_set: return None

        # Branch On +/- Literal;
        nextLiteral = abs(sum(clause_set, [])[0])
        for m in [1, -1]:
            literalAssignment = dpll_sat_solve([list(c) for c in clause_set], [*partial_assignment, m*nextLiteral])
            if literalAssignment != None: return sorted(literalAssignment, key = abs)

        # If No Assignments Satify The Problem, Return UNSAT
        return None

# ---------------------------------------------------------------------------------------