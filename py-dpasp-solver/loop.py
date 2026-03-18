from dataclasses import dataclass
import networkx as nx
import numpy as np

@dataclass
class Loop:
    Cycles = [] # Array of cycles/ loop
    num_of_atoms : int

    """
        Matrix of R x (A + 1) dimension, where R := number of rules, A := number of atoms
        For each line of matrix: is a rule from program
        For each column of matrix : if atom is in rule, value is 1, else 0
    """
    Head_Rules = [] # Description of Rules
    Pos_Body_Rules = []
    Neg_Body_Rules = []

    Loop_Formulas = []

    def __rule2vector(self, rule) -> None: # Auxiliary Function
        """
            @brief: Given a rule, identify which atoms is in head, in positive body and in negative body
        """
        Head = [0]*(self.num_of_atoms)
        Pos_Body = [0]*(self.num_of_atoms)
        Neg_Body = [0]*(self.num_of_atoms)

        for atom in rule.head:
            Head[atom - 1] = 1
        for atom in rule.body:
            if atom > 0: # Is positive rule
                Pos_Body[atom - 1] = 1
            else:
                Neg_Body[(-atom) - 1] = 1
        
        self.Head_Rules.append(Head)
        self.Pos_Body_Rules.append(Pos_Body)
        self.Neg_Body_Rules.append(Neg_Body)

    def __init_matrix(self, Rules): # Auxiliary Function
        for r in Rules:
            if r.body and r.head:
                self.__rule2vector(r)
        
        np.array(self.Head_Rules)
        np.array(self.Pos_Body_Rules)
        np.array(self.Neg_Body_Rules)

    def __init__(self, DepGraph : nx.DiGraph, Rules, Atoms):
        self.Cycles = nx.simple_cycles(DepGraph)
        self.num_of_atoms = len(Atoms)

        self.__init_matrix(Rules)
    
