"""Solve easy compass sudoku puzzle"""
#https://cracking-the-cryptic.web.app/sudoku/qbQq9d9JDm
import compass_problem

my_problem = compass_problem.base_compass_problem(4, (5, 5))
print("generated base problem")

my_problem.add_compass(
    (1, 0),
    0,
    {
        compass_problem.CardinalDirection.east: 3,
        compass_problem.CardinalDirection.south: 5,
    },
)
print("Added compass 1")
my_problem.add_compass(
    (1, 1),
    1,
    {
        compass_problem.CardinalDirection.north: 0,
        compass_problem.CardinalDirection.east: 2,
        compass_problem.CardinalDirection.south: 0,
        compass_problem.CardinalDirection.west: 0,
    },
)
print("Added compass 2")
my_problem.add_compass(
    (2, 2),
    2,
    {
        compass_problem.CardinalDirection.north: 0,
        compass_problem.CardinalDirection.east: 2,
        compass_problem.CardinalDirection.south: 1,
        compass_problem.CardinalDirection.west: 0,
    },
)
print("Added compass 3")
my_problem.add_compass(
    (0, 3), 3, {compass_problem.CardinalDirection.north: 3,},
)
print("Added compass 4")

print(*my_problem.get_result().items(), sep="\n")
