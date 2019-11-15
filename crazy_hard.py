"""Solve crazy hard problem"""
# https://cracking-the-cryptic.web.app/sudoku/pqg8LG64Tn
import compass_problem

my_problem = compass_problem.base_compass_problem(4, (8, 8))
print("Generated problem")

my_problem.add_compass(
    (1, 1),
    0,
    {
        compass_problem.CardinalDirection.north: 2,
        compass_problem.CardinalDirection.east: 5,
        compass_problem.CardinalDirection.south: 3,
        compass_problem.CardinalDirection.west: 0,
    },
)
print("Add compass")
my_problem.add_compass(
    (5, 2),
    1,
    {
        compass_problem.CardinalDirection.north: 1,
        compass_problem.CardinalDirection.east: 2,
        compass_problem.CardinalDirection.west: 8,
    },
)
print("Add compass")
my_problem.add_compass(
    (2, 5),
    2,
    {
        compass_problem.CardinalDirection.east: 22,
        compass_problem.CardinalDirection.south: 8,
        compass_problem.CardinalDirection.west: 9,
    },
)
print("Add compass")
my_problem.add_compass(
    (6, 6),
    3,
    {
        compass_problem.CardinalDirection.north: 2,
        compass_problem.CardinalDirection.east: 3,
        compass_problem.CardinalDirection.south: 0,
        compass_problem.CardinalDirection.west: 4,
    },
)
print("Add compass")
print("Solving...")

print(*my_problem.get_result().items(), sep="\n")
