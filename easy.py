"""Solve easy compass sudoku puzzle"""
# https://cracking-the-cryptic.web.app/sudoku/qbQq9d9JDm
import compasssudoku.builder

my_problem_builder = compasssudoku.builder.CompassProblemBuilder((5, 5))
print("Generated base problem")

my_problem_builder.add_compass((1, 0), [-1, 3, 5, -1])
my_problem_builder.add_compass((1, 1), [0, 2, 0, 0])
my_problem_builder.add_compass((2, 2), [0, 2, 1, 0])
my_problem_builder.add_compass((0, 3), [3, -1, -1, -1])
print("Added compasses")

my_problem = my_problem_builder.finalize()
print("Solving...")

print(*my_problem.get_result().items(), sep="\n")
