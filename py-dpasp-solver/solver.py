'''
Represents, manipulates and solves a Probabilistic Answer Set Program

heavily inpisred by ASPM: https://github.com/raki123/aspmc/blob/main/aspmc/programs/program.py
'''
from dataclasses import dataclass
from lark import Lark
import parser
import clingo
from clingo.symbol import Function, parse_term
import re
from typing import List, Iterable, Union, Dict
import networkx as nx
from groundprogram import *

class Program:
    ''' A class for manipulating PASP Programs.

    Language features supported:
        - Ground annotaded disjunctions (body-free).
        - Disjunctive rules (with variables) with arithmetic constraints.
        - Choice rules.
        - Constraints.

    No direcrives are supported (query, semantics, etc), as the purpose is to
    compile the program into a circuit (which can then be used to answer queries
    under an appropriate semantics).

    Args:
        - program_str: A (possibly empty) string containing the possibly non-ground part of the program. 
        - database_str: A (possibly empty) string containing the ground part of the program. 
       
    '''
    def __init__(self, program_str:str, database_str:str, verbosity=0):
        # self._anotated_disjunctions = []
        self._weight_function = {} # choices to weights
        self._rules = []
        self.grounded_program = None
        if not program_str and not database_str:
            return
        # parse program string
        self.parse(program_str + database_str)
        # then ground it
        self.ground()

    def parse(self,program_str:str) -> None:
        the_parser = Lark(parser.GRAMMAR, start='program', parser='lalr', transformer=parser.PaspTransformer())
        self.program = the_parser.parse(program_str)

    def _to_asp(self) -> str:
        ''' Translates PASP to ASP for grounding.

        Converts annotated disjunction into choice rules
        and stores weights of probabilistic choices.
        '''
        # TO-DO: translate choice rules to normal rules
        # TO-DO: accept probabilistic rules with (positive) bodies.
        asp_program = []
        for line,r in enumerate(self.program):
            if isinstance(r, parser.ProbabilisticRule):
                # rewrite probabilistic rules as choice rules
                asp_program.append(r.get_asp_string())
                # we assume that probabilistic rules are ground and their atoms do not 
                # unify with atoms in other rule's head, i.e., 
                # there is a function probabilistic fact -> weight
                for atom, weight in zip(r.head, r.weights):
                    #TODO: allow for annotated disjunctions by assigning weights and exactly_one_of contraints
                    if len(atom.get_variables()) > 0:
                        raise Exception(f"Syntax Error: Found non-ground probabilistic rule in Line {line+1}\n>>\t" + str(r))
                    # self._probabilistic_atoms.add(atom)
                    self._weight_function[str(atom)] = float(weight)
            elif isinstance(r, parser.Rule):
                asp_program.append(str(r))
        return asp_program

    def ground(self) -> None:
        'Ground program' 
        # apply translation to ASP (so that gringo can be called on)        
        asp_program_str = '\n'.join(str(r) for r in self._to_asp())
        self.grounded_program = GroundProgram(asp_program_str, self._weight_function)

    def shift(self):
        ''''
        Apply shifting to disjunctive rules (Ben-Eliyahu and Dechter, 1994), 
        Assumes (but does not check) that the program is head cycle free.
        '''
        if self.grounded_program:
            return self.grounded_program.shift()
            
    def __str__(self):
        max_lines = 30 # TODO: make this configurable somewhere else
        lines = []
        for i,r in enumerate(self.program):
            if i >= max_lines:
                lines.append(f'and {len(self.grounded_program.rules)-i+1} other rules...') 
                break
            lines.append(str(r))
        return '\n'.join(lines)


if __name__ == '__main__':
    '''
    Represents a dPASP program in asp, calling the clingo solver with diferent assumptions 
    ( all possible words given the set of Probabilistic Rules ) to solve the dPASP program
    '''

    '''
    converts dpasp to asp program + set of probabilistic rules and its weights
    '''
    import sys
    program_str = ''
    with open(sys.argv[1]) as infile:
        program_str = infile.read()
    database_str = ''
    if len(sys.argv) > 2:
        with open(sys.argv[2]) as infile:
            database_str = infile.read()
    program = Program(program_str, database_str)



    prob_rules = {}
    prob_func = {}

    ctl = clingo.Control(["0"])
    
    '''
    Adds all the rules to the clingo model. In case it is a normal rule, it is just added,
    in case it's a probabilistic one, it is first treated in this for loop, and it will be added
    to clingo on the next.

    The dict prob_rules is maintained with the key as the str of the rule, the value is a list
    [Clingo Symbol, probability, 0], meanwhile prob_func will be a dict with all the atoms and 
    their probabilities in the future, so we already add the probabilistic atoms and their 
    probabilities right now.
    '''
    for r in program.program: 
        if isinstance(r, parser.Rule): 
            ctl.add(str(r))
        elif isinstance(r, parser.ProbabilisticRule):
            for i in range(0, len(r.head)):
                prob_rules[str(r.head[i])] = []
                prob_rules[str(r.head[i])].append(parse_term(str(r.head[i])))
                prob_rules[str(r.head[i])].append(float(r.weights[i]))
                prob_rules[str(r.head[i])].append(0)
                prob_func[str(r.head[i])] = r.weights[i]
    
    '''
    Adds each probabilistic rule as a external atom with a Free TruthValue to te clingo model,
    this allows us to then set their values to True or False as we please
    '''
    with ctl.backend() as backend:
        for r in prob_rules:
                tba_int = backend.add_atom(prob_rules[r][0])
                backend.add_external(tba_int, clingo.TruthValue.Free)

    ctl.ground()

    '''
    This counter loops for all possible words, setting each probabilitisc rule to
    True or False, then calling the clingo solver that returns the model.

    The probability of the world is added to the prob_func of all atoms true in the model.
    '''
    world_probability = 1
    carry = False
    first_atm = True
    while True:

        for i in prob_rules:
            if prob_rules[i][2] == 0:
                if carry == True or first_atm == True:
                    ctl.assign_external(prob_rules[i][0], True)
                    prob_rules[i][2] = 1
                    world_probability *= prob_rules[i][1]
                    carry = False
                    first_atm = False
                else:
                    ctl.assign_external(prob_rules[i][0], False)
                    world_probability *= (1-prob_rules[i][1])
            elif prob_rules[i][2] == 1:
                if carry == True or first_atm == True:
                    ctl.assign_external(prob_rules[i][0], False)
                    prob_rules[i][2] = 0
                    world_probability *= (1-prob_rules[i][1])
                    carry = True
                    first_atm = False
                else:
                    ctl.assign_external(prob_rules[i][0], True)
                    world_probability *= prob_rules[i][1]

        with ctl.solve(yield_=True) as handle:
            for model in handle:
                for atm in model.symbols(atoms = True):
                    if str(atm) not in prob_rules:
                        if str(atm) in prob_func: prob_func[str(atm)] += world_probability
                        else: prob_func[str(atm)] = world_probability

        world_probability = 1
        if carry == True: break
        first_atm = True


    '''
    As the parser doesn't support #queries yet, all the probabilities are simply printed
    '''
    alrd_printed = []
    for r in program.program:
        for i in range(0, len(r.head)):
            if str(r.head[i]) not in alrd_printed:
                if str(r.head[i]) in prob_func:
                    print(f'The probability of {r.head[i]} is {prob_func[str(r.head[i])]}')
                    alrd_printed.append(str(r.head[i]))
                else:
                    print(f'The probability of {r.head[i]} is 0')