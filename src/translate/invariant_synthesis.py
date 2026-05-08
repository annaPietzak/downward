#! /usr/bin/env python3

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
    for c in candidates:
        clause = []
        for l in c.parts:
            clause.append(var_map[l])
        solver.add_clause(clause)

    return solver.solve()

# strips regression from the planning lecture
# since the regression is always called for the negation of a disjunction the formula here has to be a conjunction
def strips_regression(operator: pddl.PropositionalAction, formula: Conjunction):
    add_effects = [eff for _, eff in operator.add_effects]
    del_effects = [eff for _, eff in operator.del_effects]
    for atom in formula.parts:
        if atom in del_effects:
            return Falsity()

    result = Conjunction(operator.precondition + [atom for atom in formula.parts if atom not in add_effects])
    return result.simplified()

def regression(operator: pddl.PropositionalAction, formula: Conjunction):
    # TODO check add after delete semantic somewhere
    return Conjunction(operator.precondition + [_regression(operator.add_effects + [(condition, effect.negate()) for condition, effect in operator.del_effects], formula)]).simplified()
    

# since the regression is always called for the negation of a disjunction the formula here has to be a conjunction
def _regression(effect: List[Tuple[List[Literal], Literal]], formula: Conjunction):
    if len(formula.parts) == 1:
        var = formula.parts[0]
        if isinstance(var, Truth): return Truth() 
        elif isinstance(var, Falsity): return Falsity()
        # elif var.negated:
        #     return _regression(effect, Conjunction([var.negate()])).negate()
        else:
            return Disjunction([
                effcond(var, effect), 
                Conjunction([
                    var, 
                    effcond(var.negate(), effect).negate()
                    ])
                ]).simplified()
    else:
        return Conjunction([_regression(effect, Conjunction([part])) for part in formula.parts]).simplified()

def effcond(var: Literal, effects: List[Tuple[List[Literal], Literal]]) -> Disjunction:
    parts = []
    for condition, effect in effects:
        part = None
        if isinstance(effect, Truth): 
            part = Falsity()
        elif var == effect: 
            part = Truth()
        elif var != effect: 
            part = Falsity()
        
        if condition:
            part = Conjunction(condition + [part])
        
        parts.append(part)
    
    return Disjunction(parts).simplified()

def invariants(
        state_variables: Set[pddl.Literal], 
        initial_state: List[Union[Atom, Assign]], 
        operators: List[pddl.PropositionalAction], 
        limit: int =2):

    # initiate mapping from atoms to integers for the SAT solver
    for i in range(len(state_variables)):
        var_map.update({i+1: list(state_variables)[i]})
        var_map.update({-1*(i+1): list(state_variables)[i].negate()})
        var_map.update({list(state_variables)[i]:i+1})
        var_map.update({list(state_variables)[i].negate():-1*(i+1)})

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
            # print(f"candidates: {[c.parts for c in candidates_current]}")
            c = candidates_current.pop()
            # print(f"picked candidate {c.parts}")

            valid = True
            for o in operators:
                reg = regression(o, c.negate())
                # print(f"regression of {c.negate().parts} through p {o.precondition} a {o.add_effects} d {o.del_effects} equals")
                # reg.dump()
                sat_check = check_SAT(candidates_copy, reg)
                # print(f"candidates and regression is satisfiable: {sat_check}")
                if sat_check:
                    # check limit
                    if c.size() < limit:
                        # add new candidates
                        for v in state_variables:
                            candidates_new |= {Disjunction(list(c.parts) + [Atom(v.predicate, v.args)])}
                            candidates_new |= {Disjunction(list(c.parts) + [Atom(v.predicate, v.args).negate()])}
                    # break from the operator loop, since we already know candidate is not an invariant
                    valid = False
                    break
            # candidate may remain if it survived the loop through all operators
            if valid: candidates_new |= {c}

        candidates_current = candidates_new
        # print(f"current candidates: {[c.parts for c in candidates_current]}")
        # print(f"copied candidates: {[c.parts for c in candidates_copy]}")
        # print(f"new candidates: {[c.parts for c in candidates_new]}")

        # stop if a fixpoint is reached
        if candidates_current == candidates_copy: 
            break
    print("Final invariants")
    for c in candidates_current:
        print(f"{c.parts}")
    return candidates_current

if __name__ == "__main__":
    from translate import pddl_parser
    from translate.options import set_options

    set_options()
    task = pddl_parser.open()
    relaxed_reachable, atoms, actions, goals, axioms, _ = instantiate.explore(task)

    # print("goal relaxed reachable: %s" % relaxed_reachable)
    # print("%d atoms:" % len(atoms))
    # for atom in atoms:
    #     print(" ", atom)
    # print()
    # print("%d actions:" % len(actions))
    # for action in actions:
    #     for condition, effect in action.add_effects:
    #         condition.dump()
    #         effect.dump()
    #     # action.dump()
    #     print()
    # print("%d axioms:" % len(axioms))
    # for axiom in axioms:
    #     axiom.dump()
    #     print()
    # print()
    # if goals is None:
    #     print("impossible goal")
    # else:
    #     print("%d goals:" % len(goals))
    #     for literal in goals:
    #         literal.dump()
    # print()
    # print(f"initial state (?): {task.init}")
    # clause = Disjunction([list(atoms)[2]])
    # print(f"atom {clause.parts}")
    # for o in actions:
    #     reg = regression(o, clause)
    #     print(f"operator p {o.precondition}, a {o.add_effects}, d {o.del_effects}")
    #     print(reg.parts)
    #     print(f"Truth: {isinstance(reg, Truth)}")
    #     print(f"Falsity: {isinstance(reg, Falsity)}")

    print("calculating invarints\n")
    invariants(state_variables=atoms, initial_state=task.init, operators=actions, limit=3)