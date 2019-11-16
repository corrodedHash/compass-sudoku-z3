"""Contains CompassProblem class"""
from collections import OrderedDict
from typing import Dict

import z3
from .util import Coord2D



class CompassProblem:
    """Wraps the compass sudoku problem"""

    cells: Dict[Coord2D, z3.Int]
    solver: z3.Solver
    dimensions: Coord2D

    def get_result(self) -> Dict[Coord2D, int]:
        """Get result for problem"""
        self.solver.check()
        my_model = self.solver.model()
        result: Dict[Coord2D, int] = OrderedDict()
        for index, expression in self.cells.items():
            result[index] = my_model[expression]
        return result
