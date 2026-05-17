#! /usr/bin/env python3

import sys
import os
sys.path.insert(1, os.path.join(os.path.dirname(__file__), '..'))

from typing import Set, List, Union, Tuple
from pysat.solvers import Minisat22

from translate.pddl.conditions import Atom, Condition, Truth, Falsity
from translate.pddl.f_expression import Assign
from translate.pddl import Conjunction, Disjunction, Literal

import instantiate
import pddl

var_map = dict()

def check_SAT(candidates: Set[Disjunction], regression: Conjunction):
    solver = Minisat22()

    # the regression simplifies to constant true / false or a conjunction
    if isinstance(regression, Truth): 
        # don't need to add to solver
        pass
    elif isinstance(regression, Falsity): 
        # Conjunction with constant false cannot be satisfied
        return False
    else: 
        for r in regression.parts:
            if isinstance(r, Truth): 
                continue
            elif isinstance(r, Falsity): 
                return False
            else:
                solver.add_clause([var_map[r]])
    # candidates only contain clauses of literals, so each clause can be added as is
    for c in candidates:
        clause = []
        for l in c.parts:
            clause.append(var_map[l])
        solver.add_clause(clause)

    return solver.solve()

# strips regression from the planning lecture
# since the regression is always called for the negation of a disjunction the formula here has to be a conjunction
# def strips_regression(operator: pddl.PropositionalAction, formula: Conjunction):
#     add_effects = [eff for _, eff in operator.add_effects]
#     del_effects = [eff for _, eff in operator.del_effects]
#     for atom in formula.parts:
#         if atom in del_effects:
#             return Falsity()

#     result = Conjunction(operator.precondition + [atom for atom in formula.parts if atom not in add_effects])
#     return result.simplified()

# regr(o, phi) = pre(o) and regr(eff(o), phi)
def regression(operator: pddl.PropositionalAction, formula: Conjunction):
    return Conjunction(operator.precondition + [_regression(operator.add_effects + [(condition, effect.negate()) for condition, effect in operator.del_effects], formula)]).simplified()
    

# since the regression is always called for the negation of a disjunction the formula here has to be a conjunction
def _regression(effect: List[Tuple[List[Literal], Literal]], formula: Conjunction):
    if len(formula.parts) == 1:
        var = formula.parts[0]
        # regr(True, e) = True
        if isinstance(var, Truth): return Truth() 
        # regr(False, e) = False
        elif isinstance(var, Falsity): return Falsity()
        # elif var.negated:
        #     return _regression(effect, Conjunction([var.negate()])).negate()
        else:
            # regr(literal, e) = effcond(literal, e) or (literal and not effcond(negative literal, e))
            # if effcond(literal, e) = True and not effcond(negative literal, e) = True the whole formula evaluates to true
            # -> True or (literal and not True) = True or (literal and False) = True or False = True
            # so an add-after-delete semantic is given
            return Disjunction([
                effcond(var, effect), 
                Conjunction([
                    var, 
                    effcond(var.negate(), effect).negate()
                    ])
                ]).simplified()
    else:
        # regr(phi and psi, e) = regr(phi, e) and regr(psi, e)
        # we know that the formula is a conjunction, so we can disregard the rule for the regression of a disjunction
        return Conjunction([_regression(effect, Conjunction([part])) for part in formula.parts]).simplified()

# the condition under which an effect makes a literal true
def effcond(var: Literal, effects: List[Tuple[List[Literal], Literal]]) -> Disjunction:
    parts = []
    for condition, effect in effects:
        part = None
        # effcond(literal, True) = False 
        if isinstance(effect, Truth): 
            part = Falsity()
        # effcond(literal, e) = True, if e = literal
        elif var == effect: 
            part = Truth()
        # effcond(literal, e) = False, if e = literal' != literal
        elif var != effect: 
            part = Falsity()
        
        # effconf(literal, psi -> e) = psi and effcond(literal, e)
        if condition:
            part = Conjunction(condition + [part])
        
        parts.append(part)
    # effcond(literal, e and e') = effcond(literal, e) or effcond(literal, e')
    return Disjunction(parts).simplified()

def create_new_candidates(candidates, c, new_atom):
    new_c = None
    # check if the new atom is not already present in the discarded candidate c to avoid candidates of the form (a or a)
    if not new_atom in c.parts:
        new_c = Disjunction(list(c.parts) + [new_atom])
        # check that the candidate is not already in the set
        for other_c in candidates:
            if set(new_c.parts) == set(other_c.parts):
                return None
    return new_c
    
# remove invariants that contain another invariant, often tautologies
# given (a or not a), (b or a or not a) the second one will be removed, since a stronger invariant is already present
def remove_supersets(invariants: Set[Disjunction]):
    res = set()
    for c1 in invariants:
        superset = False
        for c2 in invariants:
            if c1.size() > c2.size():
                if set(c2.parts).issubset(set(c1.parts)):
                    superset = True
                    break
        if not superset:
            res.add(c1)
    return res

def remove_tautology(invariants: Set[Disjunction]):
    res = set()
    for c in invariants:
        contains_tautology = False
        for l in c.parts:
            if l.negate() in c.parts:
                contains_tautology = True
                break
        if not contains_tautology:
            res.add(c)
    return res


# invariant algorithm as introduced by J. Rintanen 2008
def invariants(
        state_variables: Set[pddl.Literal], 
        initial_state: List[Union[Atom, Assign]], 
        operators: List[pddl.PropositionalAction], 
        limit: int =2,
        reduce: bool =True):

    # initiate mapping from atoms to integers for the SAT solver
    for i in range(len(state_variables)):
        var_map.update({i+1: list(state_variables)[i]})
        var_map.update({-1*(i+1): list(state_variables)[i].negate()})
        var_map.update({list(state_variables)[i]:i+1})
        var_map.update({list(state_variables)[i].negate():-1*(i+1)})

    # initial candidates are all literals that are true in the initial state
    candidates_current = {Disjunction([Atom(v.predicate, v.args)]) for v in state_variables if v in initial_state}
    candidates_current |= {Disjunction([Atom(v.predicate, v.args).negate()]) for v in state_variables if v not in initial_state}
    print("initial candidates:")
    for c in candidates_current:
        print(f"{list(c.parts)}")

    # outer loop
    while True:
        candidates_copy = candidates_current.copy()
        candidates_new = set()
        # inner loop
        while candidates_current:
            # pick any candidate
            c = candidates_current.pop()
            valid = True
            # check if candidate is invariant to all operator applications
            for o in operators:
                reg = regression(o, c.negate())
                sat_check = check_SAT(candidates_copy, reg)
                if sat_check:
                    # check limit
                    if c.size() < limit:
                        # add new candidates
                        for atom in ([Atom(v.predicate, v.args) for v in state_variables] + [Atom(v.predicate, v.args).negate() for v in state_variables]):
                            new_candidate = create_new_candidates(candidates_new, c, atom)
                            if new_candidate:
                                candidates_new |= {new_candidate}
                    # break from the operator loop, since we already know candidate is not an invariant
                    valid = False
                    break
            # candidate may remain if it survived the loop through all operators
            if valid: candidates_new |= {c}

        candidates_current = candidates_new

        # stop if a fixpoint is reached
        if candidates_current == candidates_copy: 
            break

    if reduce:
        return remove_supersets(remove_tautology(candidates_current))
    else:
        return candidates_current

if __name__ == "__main__":
    from translate import pddl_parser
    from translate.options import set_options

    set_options()
    task = pddl_parser.open()
    relaxed_reachable, atoms, actions, goals, axioms, _ = instantiate.explore(task)

    # build
    print("calculating invarints\n")
    inv = invariants(state_variables=atoms, initial_state=task.init, operators=actions, limit=3, reduce=False)
    print("\nFinal invariants")
    for invariant in inv:
        print(invariant.parts)

    inv = remove_tautology(inv)
    print("\nWithout tautologies")
    for invariant in inv:
        print(invariant.parts)
    inv = remove_supersets(inv)
    print("\nReduced invariants")
    for invariant in inv:
        print(invariant.parts)
