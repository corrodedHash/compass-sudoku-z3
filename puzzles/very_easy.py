"""Solve easy compass sudoku puzzle"""
# https://cracking-the-cryptic.web.app/sudoku/qbQq9d9JDm
from compasssudoku.builder import Compass, CompassProblemBuilder


def main():
    """Main function"""
    my_problem_builder = CompassProblemBuilder((2, 2))
    print("Generated base problem")

    my_problem_builder.add_compass(Compass((1, 0), [0, 0, 2, 2]))
    print("Added compasses")

    my_problem = my_problem_builder.finalize()
    print("Solving...")

    print(my_problem.get_result().table())


if __name__ == "__main__":
    main()
