from dataclasses import dataclass
import clingo
from typing import List, Iterable, Union, Dict
import networkx as nx
import numpy as np
from loop import *

class GroundObject(object):
    pass

@dataclass
class GroundAtom(GroundObject):
    symbol: clingo.Symbol
    atom: int
    order: int = 0

    def __lt__(self, other):
        if self.__class__ == other.__class__:
            return (self.symbol, self.atom) < (other.symbol, other.atom)
        elif isinstance(other, GroundObject):
            return self.order < other.order
        raise Exception("Incomparable type")

@dataclass
class LoopFormula:
    def __init__(self, loop):
        self._loop = loop
        self._disjunction_of_RL = []
    
    def _add_RL(self, RL):
        self._disjunction_of_RL.append(RL) 

@dataclass
class GroundRule(GroundObject):
    choice: bool
    head: List[int]
    body: List[int]
    order: int = 1
    
    def __lt__(self, other):
        if self.__class__ == other.__class__:
            return (self.choice, self.head, self.body) < (other.choice, other.head, other.body)
        elif isinstance(other, GroundObject):
            return self.order < other.order
        raise Exception("Incomparable types")
    
    def __str__(self):
        head = "; ".join([f"X{a}" for a in self.head])
        if self.choice:
            head = "{" + head + "}"
        body = ", ".join([ ("not X" if b < 0 else "X") + str(abs(b)) for b in self.body])
        if body:
            head += ":-" + body 
        return head + "."


class Observer:
    def __init__(self, program):
        self.program = program

    def rule(self, choice: bool, head: List[int], body: List[int]) -> None:
        self.program.rules.append(GroundRule(choice=choice, head=head, body=body))

    def output_atom(self, symbol: clingo.Symbol, atom: int) -> None:
        self.program.atoms.append(GroundAtom(symbol=symbol, atom=atom))

@dataclass
class GroundProgram():
    ''' A class to compactly represent a ground program, as one output by gringo.

    Atoms are represented as positive integers, and rules are 
    represented as lists of signed integers, with negative numbers
    denoting negated literals.
    '''
    rules: List[GroundRule]
    atoms: List[GroundAtom]
    _atom_to_txt: Dict[int,str]
    _derived_from: Dict[int,GroundRule]
    _atom_to_weight: Dict[int,float]

    ''' Initializes and obtains a ground program by calling gringo
    on a given ASP program string. Ground atoms that have weights are interpreted
    as probabilistic choices and expected not to unify with a single rule head.
    '''  
    def __init__(self, program_str:str, weight_function:Dict[str,float]):
        # initialize variables
        self.rules = []
        self.atoms = []   
        self.num_of_atoms = 0
        # maps each atom index to its weight
        self._atom_to_weight = {}
        # maps each atom index to its textual representation
        self._atom_to_txt = {}
        # for each head atom, which rules can derive it?
        self._derived_from = {}
        """
        Loop Formulas
        """
        self.dep_graph = nx.DiGraph()
        # strongly connected components of positive dependncy graph
        self._Has_pos_cycles = False
        # if string is empty, there's nothing to do
        if not program_str:
            return
        self._ground(program_str, weight_function)

    def _ground(self, program_str:str, weight_function:Dict[str,float]) -> None:    
        # ground program
        control = clingo.Control()
        control.add("base", [], program_str)
        control.register_observer(Observer(self))
        control.ground([('base', [])])
        self._process_output(control, weight_function)

    def _process_output(self, control:clingo.Control, weight_function:Dict[str,float]) -> None:
        # process output
        for sym in control.symbolic_atoms:
            symbol = str(sym.symbol)
            self._atom_to_txt[sym.literal] = symbol
            if symbol in weight_function:
                self._atom_to_weight[sym.literal] = weight_function[symbol]
        for r in self.rules: 
            if not(r.choice and len(r.head) > 0 and len(r.body) == 0 and self._atom_to_txt[abs(r.head[0])] in weight_function):
                # it is a normal rule
                for a in r.head:
                    if a not in self._derived_from:
                        self._derived_from[a] = []
                    self._derived_from[a].append(r)
        choices = set(self._atom_to_weight.keys())
        if len(choices.intersection(self._derived_from.keys())) != 0:
            raise Exception("Syntax Error: Probabilistic choice unifies with rule head")

    def add_rule(self, choice: bool = False, head: Iterable[int] = [], body: Iterable[int] = []) -> None: # pylint: disable=dangerous-default-value
        self.rules.append(GroundRule(choice=choice, head=list(head), body=list(body)))

    def add_rules(self, rules: Iterable[GroundRule]) -> None:
        self.rules.extend(rules)

    def _remove_tautologies(self):
        rules = []
        for r in self.rules:
            if set(r.head).intersection(set(r.body)) == set():
                rules.append(r)
        self.rules = rules

    def _Verify_pos_dep(self):
        self.dep_graph.add_nodes_from(self._atom_to_txt.keys())
        for r in self.rules:
            for a in r.head:
                for b in r.body:
                    if b > 0:
                        self.dep_graph.add_edge(b, a)

        try:
            _ = nx.find_cycle(self.dep_graph, orientation="original")
            self._Has_pos_cycles = True
        except:
            self._Has_pos_cycles = False

    def check_tightness(self) -> bool:
        'Checks if grounded program is tight (or head-cycle free)'
        self._Verify_pos_dep()
        if not self._Has_pos_cycles: #
            return True
        return False

    def shift(self):
        ''''
        Apply shifting to disjunctive rules (Ben-Eliyahu and Dechter, 1994), 
        Assumes (but does not check) that the program is head cycle free.
        '''
        new_rules = []
        for r in self.rules:
            if len(r.head) > 1:          
                for a in r.head:
                    ext = [b for b in r.head if b != a]
                    new_rules.append( GroundRule(a, r.body + ext) )
            else:
                new_rules.append(r)
        self.rules = new_rules

   
    def _pretty_print_literal(self, literal:int) -> str:
        if literal < 0:
            atom_str = "not "
            literal = abs(literal)
        else:
            atom_str = ""
        if literal in self._atom_to_txt:
            atom_str += self._atom_to_txt[literal]
        else:
            atom_str += "UNKNOWN"
        return atom_str
    
    def _pretty_print_rule(self,r: GroundRule) -> str:
        if r.choice and len(r.head) > 0 and len(r.body) == 0 and abs(r.head[0]) in self._atom_to_weight:
            # probabilistic choice
            return ';'.join( f"{self._atom_to_weight[a]}::{self._atom_to_txt[abs(a)]}" for a in r.head) + "."
        # non-probabilistic rule
        head = ';'.join(self._pretty_print_literal(literal) for literal in r.head)
        body = ','.join(self._pretty_print_literal(literal) for literal in r.body)
        if body:
            return head + ':-' + body + '.'
        else:
            return head + '.'

    def __str__(self):
        return '\n'.join(self._pretty_print_rule(r) for r in self.rules)

    def __iter__(self):
        return iter(self.rules)
    