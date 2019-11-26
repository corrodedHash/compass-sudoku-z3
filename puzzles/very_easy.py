"""Solve easy compass sudoku puzzle"""
# https://cracking-the-cryptic.web.app/sudoku/qbQq9d9JDm
from compasssudoku.builder import Compass, build_compass_problem


def main() -> None:
    """Main function"""
    my_problem = build_compass_problem((2, 2), [Compass((1, 0), [0, 0, 2, 2])])

    print(my_problem.get_result().table())


if __name__ == "__main__":
    main()
