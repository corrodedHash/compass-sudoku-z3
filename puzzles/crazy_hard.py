"""Solve crazy hard problem"""
# https://cracking-the-cryptic.web.app/sudoku/pqg8LG64Tn
from compasssudoku.builder import Compass, build_compass_problem


def main() -> None:
    """Main function"""
    my_problem = build_compass_problem(
        (8, 8),
        [
            Compass((1, 1), [2, 5, 3, 0]),
            Compass((5, 2), [1, 2, -1, 8]),
            Compass((2, 5), [-1, 22, 8, 9]),
            Compass((6, 6), [2, 3, 0, 4]),
        ],
    )

    print("Solving...")
    print(my_problem.get_result().table())


if __name__ == "__main__":
    main()
