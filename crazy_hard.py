"""Solve crazy hard problem"""
# https://cracking-the-cryptic.web.app/sudoku/pqg8LG64Tn
import compasssudoku.builder

my_problem_builder = compasssudoku.builder.CompassProblemBuilder((8, 8))
print("Generated problem")

my_problem_builder.add_compass((1, 1), [2, 5, 3, 0])
my_problem_builder.add_compass((5, 2), [1, 2, -1, 8])
my_problem_builder.add_compass((2, 5), [-1, 22, 8, 9])
my_problem_builder.add_compass((6, 6), [2, 3, 0, 4])
print("Added compasses")

my_problem = my_problem_builder.finalize()
print("Solving...")
print(*my_problem.get_result().items(), sep="\n")
