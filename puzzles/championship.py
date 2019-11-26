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

from compasssudoku.builder import Compass, build_compass_problem
import compasssudoku.builder


def main() -> None:
    """Main function"""
    logging.basicConfig(
        format="%(asctime)s %(message)s",
        datefmt="%m/%d/%Y %I:%M:%S %p",
        level=logging.DEBUG,
    )
    compasssudoku.builder.MODULE_LOGGER.setLevel(logging.DEBUG)

    my_problem = build_compass_problem(
        (9, 9),
        [
            Compass((2, 2), [1, -1, -1, -1]),
            Compass((6, 2), [-1, -1, -1, 0]),
            Compass((3, 3), [2, -1, 1, 2]),
            Compass((5, 3), [1, 0, -1, -1]),
            Compass((4, 4), [-1, 4, 5, 4]),
            Compass((3, 5), [-1, -1, -1, 6]),
            Compass((5, 5), [2, 1, -1, 3]),
            Compass((2, 6), [-1, -1, 7, -1]),
            Compass((6, 6), [1, 0, 0, -1]),
        ],
    )
    print("Solving...")
    my_result = my_problem.get_result()
    print(my_result.table())


if __name__ == "__main__":
    main()
