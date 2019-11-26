"""Solve easy compass sudoku puzzle"""
# https://cracking-the-cryptic.web.app/sudoku/qbQq9d9JDm
from compasssudoku.builder import Compass, build_compass_problem


def main() -> None:
    """Main function"""
    my_problem = build_compass_problem(
        (5, 5),
        [
            Compass((1, 0), [-1, 3, 5, -1]),
            Compass((1, 1), [0, 2, 0, 0]),
            Compass((2, 2), [0, 2, 1, 0]),
            Compass((0, 3), [3, -1, -1, -1]),
        ],
    )
    print("Solving...")
    print(my_problem.solver.sexpr())
    my_result = my_problem.get_result()
    print(my_result.table())


if __name__ == "__main__":
    main()
