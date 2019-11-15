"""Contains CompassProblem class"""
import enum
from collections import OrderedDict
from typing import Dict, List, Tuple

import z3

Coord2D = Tuple[int, int]


class CardinalDirection(enum.Enum):
    """Cardinal directions"""

    north = enum.auto()
    east = enum.auto()
    south = enum.auto()
    west = enum.auto()


DirectionMap = {
    CardinalDirection.north: (0, -1),
    CardinalDirection.east: (1, 0),
    CardinalDirection.south: (0, 1),
    CardinalDirection.west: (-1, 0),
}
OrthogonalDirectionMap = {
    CardinalDirection.north: (1, 0),
    CardinalDirection.east: (0, 1),
    CardinalDirection.south: (-1, 0),
    CardinalDirection.west: (0, -1),
}


def in_bounds(cell: Coord2D, bounds: Coord2D) -> bool:
    """Check that coordinate is in [0, bounds)"""
    return cell[0] >= 0 and cell[0] < bounds[0] and cell[1] >= 0 and cell[1] < bounds[1]


def add_coords(summand1: Coord2D, summand2: Coord2D) -> Coord2D:
    """Add two tuples"""
    return (summand1[0] + summand2[0], summand1[1] + summand2[1])


def get_direction_cells(
    origin: Coord2D, dimensions: Coord2D, direction: CardinalDirection
) -> List[Coord2D]:
    """List all cells in the given direction"""
    result = []
    current = add_coords(origin, DirectionMap[direction])
    while in_bounds(current, dimensions):
        result.append(current)
        current = add_coords(current, OrthogonalDirectionMap[direction])
        current = (current[0] % dimensions[0], current[1] % dimensions[1])
        if current[0] == origin[0] or current[1] == origin[1]:
            current = add_coords(current, DirectionMap[direction])

    return result


class CompassProblem:
    """Wraps the compass sudoku problem"""

    cells: Dict[Coord2D, z3.Int]
    connectivity: Dict[Tuple[Coord2D, Coord2D], z3.Int]
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

    def add_compass(
        self, cell: Coord2D, compass_id: int, compass_info: Dict[CardinalDirection, int]
    ) -> None:
        """Add compass to field"""
        self.solver.add(self.cells[cell] == compass_id)
        for direction, count in compass_info.items():
            cell_list = get_direction_cells(cell, self.dimensions, direction)
            current_compass_helper = 0
            for index, cell_coord in enumerate(cell_list):
                last_compass_helper = current_compass_helper
                current_compass_helper = z3.Int(
                    f"compass_{compass_id}_{direction.name}_#{index}"
                    f"_{cell_coord[0]}_{cell_coord[1]}"
                )
                self.solver.add(
                    z3.If(
                        self.cells[cell_coord] == compass_id,
                        current_compass_helper == last_compass_helper + 1,
                        current_compass_helper == last_compass_helper,
                    )
                )
            self.solver.add(current_compass_helper == count)


def base_compass_problem(
    region_count: int, dimensions: Tuple[int, int]
) -> CompassProblem:
    """Generate base compass sudoku problem"""
    solver = z3.Solver()
    x_dim, y_dim = dimensions

    cells = {
        (x, y): z3.Int(f"cells_{x}_{y}") for x in range(x_dim) for y in range(y_dim)
    }

    connectivity = {
        ((x1, y1), (x2, y2)): z3.Int(f"conn_{x1}_{y1}-{x2}_{y2}")
        for x1 in range(x_dim)
        for y1 in range(y_dim)
        for x2 in range(x_dim)
        for y2 in range(y_dim)
        if y2 > y1 or (y2 == y1 and x2 > x1)
    }

    for cell in cells.values():
        solver.add(cell >= 0)
        solver.add(cell < region_count)

    def get_conn_index(c1: Coord2D, c2: Coord2D) -> Tuple[Coord2D, Coord2D]:
        if c2[1] > c1[1] or (c2[1] == c1[1] and c2[0] > c1[0]):
            return (c1, c2)
        return (c2, c1)

    for (c1, c2), conn in connectivity.items():
        distance = abs(c2[0] - c1[0]) + abs(c2[1] - c1[1])
        assert distance > 0
        solver.add((cells[c1] != cells[c2]) == (conn == -1))
        if distance == 1:
            solver.add((cells[c1] == cells[c2]) == (conn == 1))
        if distance > 1:
            solver.add((cells[c1] == cells[c2]) == (conn > 1))
            neighbors = []
            for direction_vector in DirectionMap.values():
                new_cell = add_coords(c2, direction_vector)
                if in_bounds(new_cell, dimensions):
                    neighbors.append(connectivity[get_conn_index(c1, new_cell)])
            assert len(neighbors) >= 2
            solver.add(
                z3.Implies(
                    conn != -1,
                    z3.Or([z3.And(x == conn - 1, x != -1) for x in neighbors]),
                )
            )
    result = CompassProblem()
    result.cells = cells
    result.solver = solver
    result.connectivity = connectivity
    result.dimensions = dimensions
    return result
