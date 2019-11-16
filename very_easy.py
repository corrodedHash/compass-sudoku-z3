"""Solve easy compass sudoku puzzle"""
# https://cracking-the-cryptic.web.app/sudoku/qbQq9d9JDm
import compasssudoku.builder

my_problem_builder = compasssudoku.builder.CompassProblemBuilder((2, 2))
print("Generated base problem")

my_problem_builder.add_compass((1, 0), [0, 0, 2,2])
print("Added compasses")

my_problem = my_problem_builder.finalize()
print("Solving...")

print(my_problem.get_result().table())
