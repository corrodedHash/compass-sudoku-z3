"""Solve crazy hard problem"""
# https://cracking-the-cryptic.web.app/sudoku/pqg8LG64Tn
from compasssudoku.builder import Compass, CompassProblemBuilder


def main():
    """Main function"""
    my_problem_builder = CompassProblemBuilder((8, 8))
    print("Generated problem")

    my_problem_builder.add_compass(Compass((1, 1), [2, 5, 3, 0]))
    my_problem_builder.add_compass(Compass((5, 2), [1, 2, -1, 8]))
    my_problem_builder.add_compass(Compass((2, 5), [-1, 22, 8, 9]))
    my_problem_builder.add_compass(Compass((6, 6), [2, 3, 0, 4]))
    print("Added compasses")

    my_problem = my_problem_builder.finalize()
    print("Solving...")
    print(my_problem.get_result().table())


if __name__ == "__main__":
    main()
