"""
Solve championship compass sudoku puzzle
https://cracking-the-cryptic.web.app/sudoku/P68BrQPTp7

Known solution:
  7  7  7  7  7  7  7  7  7
  7  5  0  2  4  4  4  4  7
  7  5  0  2  4  3  1  4  7
  7  5  2  2  4  3  1  1  7
  7  5  2  4  4  6  6  1  7
  7  5  5  5  4  6  8  1  7
  7  7  7  4  4  6  8  1  7
  7  7  4  4  6  6  1  1  7
  7  7  7  6  6  6  1  1  7
"""
import logging

from compasssudoku.builder import Compass, CompassProblemBuilder
import compasssudoku.builder


def main() -> None:
    """Main function"""
    logging.basicConfig(
        format="%(asctime)s %(message)s",
        datefmt="%m/%d/%Y %I:%M:%S %p",
        level=logging.DEBUG,
    )
    compasssudoku.builder.MODULE_LOGGER.setLevel(logging.DEBUG)

    my_problem_builder = CompassProblemBuilder((9, 9))

    my_problem_builder.add_compass(Compass((2, 2), [1, -1, -1, -1]))
    my_problem_builder.add_compass(Compass((6, 2), [-1, -1, -1, 0]))
    my_problem_builder.add_compass(Compass((3, 3), [2, -1, 1, 2]))
    my_problem_builder.add_compass(Compass((5, 3), [1, 0, -1, -1]))
    my_problem_builder.add_compass(Compass((4, 4), [-1, 4, 5, 4]))
    my_problem_builder.add_compass(Compass((3, 5), [-1, -1, -1, 6]))
    my_problem_builder.add_compass(Compass((5, 5), [2, 1, -1, 3]))
    my_problem_builder.add_compass(Compass((2, 6), [-1, -1, 7, -1]))
    my_problem_builder.add_compass(Compass((6, 6), [1, 0, 0, -1]))

    my_problem = my_problem_builder.finalize()
    print("Solving...")
    my_result = my_problem.get_result()
    print(my_result.table())


if __name__ == "__main__":
    main()
