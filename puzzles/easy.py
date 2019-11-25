"""Solve easy compass sudoku puzzle"""
# https://cracking-the-cryptic.web.app/sudoku/qbQq9d9JDm
from compasssudoku.builder import Compass, CompassProblemBuilder


def main():
    """Main function"""
    my_problem_builder = CompassProblemBuilder((5, 5))
    print("Generated base problem")

    my_problem_builder.add_compass(Compass((1, 0), [-1, 3, 5, -1]))
    my_problem_builder.add_compass(Compass((1, 1), [0, 2, 0, 0]))
    my_problem_builder.add_compass(Compass((2, 2), [0, 2, 1, 0]))
    my_problem_builder.add_compass(Compass((0, 3), [3, -1, -1, -1]))
    print("Added compasses")

    my_problem = my_problem_builder.finalize()
    print("Solving...")
    print(my_problem.solver.sexpr())
    my_result = my_problem.get_result()
    print(my_result.table())


if __name__ == "__main__":
    main()
