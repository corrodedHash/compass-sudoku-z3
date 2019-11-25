"""Contains CompassProblemBuilder class"""
import logging
from typing import Dict, List, Tuple, Union

import z3

from .problem import CompassProblem
from .util import (CardinalDirection, Coord2D, DIRECTION_MAP, add_coords,
                   get_direction_cells, in_bounds)

MODULE_LOGGER = logging.getLogger(__name__)


class CompassProblemBuilder:
    """Builder class for CompassProblem"""

    cells: Dict[Coord2D, z3.Int]
    solver: z3.Solver
    dimensions: Coord2D
    compass_count: int

    def __init__(self, dimensions: Coord2D):
        self.dimensions = dimensions
        self.last_compass_id = -1
        self.compass_count = 0
        self.cells = {}
        self._base_compass_problem()

    def finalize(self) -> "CompassProblem":
        """Finalize the building process, return actual problem"""

        for cell in self.cells.values():
            self.solver.add(cell < self.compass_count)

        result = CompassProblem()
        result.cells = self.cells
        result.dimensions = self.dimensions
        result.solver = self.solver
        return result

    def add_compass(
        self,
        cell: Coord2D,
        compass_info: Union[Dict[CardinalDirection, int], List[int]],
    ) -> None:
        """Add compass to field"""
        if not isinstance(compass_info, dict):
            actual_info = {}
            assert len(compass_info) == 4
            for direction, amount in zip(CardinalDirection, compass_info):
                if amount >= 0:
                    actual_info[direction] = amount
            compass_info = actual_info

        compass_id = self.compass_count
        self.compass_count += 1

        self.solver.add(self.cells[cell] == compass_id)
        for direction, count in compass_info.items():
            cell_list = get_direction_cells(cell, self.dimensions, direction)
            current_compass_counter = 0
            for index, cell_coord in enumerate(cell_list):
                last_compass_counter = current_compass_counter
                current_compass_counter = z3.Int(
                    f"compass_{compass_id}_{direction.name}_[{index:02}]"
                    f"_({cell_coord[0]},{cell_coord[1]})"
                )
                self.solver.add(
                    current_compass_counter
                    == (
                        last_compass_counter
                        + z3.If(self.cells[cell_coord] == compass_id, 1, 0)
                    )
                )
            self.solver.add(current_compass_counter == count)
        MODULE_LOGGER.debug('Added compass')

    def _base_compass_problem(self) -> None:
        """Generate base compass sudoku problem"""
        self.solver = z3.Solver()
        x_dim, y_dim = self.dimensions

        self.cells = {
            (x, y): z3.Int(f"cell_({x},{y})") for x in range(x_dim) for y in range(y_dim)
        }
        MODULE_LOGGER.debug('Created cell variables')

        for cell in self.cells.values():
            self.solver.add(cell >= 0)
        MODULE_LOGGER.debug('Created cell constraints')



        connectivity = {
            ((x1, y1), (x2, y2)): z3.Int(f"conn_({x1},{y1})->({x2}_{y2})")
            for x1 in range(x_dim)
            for y1 in range(y_dim)
            for x2 in range(x_dim)
            for y2 in range(y_dim)
            if y2 > y1 or (y2 == y1 and x2 > x1)
        }
        MODULE_LOGGER.debug('Created connectivity variables')

        def get_conn_index(c1: Coord2D, c2: Coord2D) -> Tuple[Coord2D, Coord2D]:
            if c2[1] > c1[1] or (c2[1] == c1[1] and c2[0] > c1[0]):
                return (c1, c2)
            return (c2, c1)

        for (c1, c2), conn in connectivity.items():
            distance = abs(c2[0] - c1[0]) + abs(c2[1] - c1[1])
            assert distance > 0
            self.solver.add((self.cells[c1] != self.cells[c2]) == (conn == -1))
            if distance == 1:
                self.solver.add((self.cells[c1] == self.cells[c2]) == (conn == 1))
            if distance > 1:
                self.solver.add((self.cells[c1] == self.cells[c2]) == (conn > 1))
                neighbors = []
                for direction_vector in DIRECTION_MAP.values():
                    new_cell = add_coords(c2, direction_vector)
                    if in_bounds(new_cell, self.dimensions):
                        neighbors.append(connectivity[get_conn_index(c1, new_cell)])
                assert len(neighbors) >= 2
                self.solver.add(
                    z3.Implies(
                        conn > 1,
                        z3.Or([x == conn - 1 for x in neighbors]),
                    )
                )
        MODULE_LOGGER.debug('Created connectivity constraints')
