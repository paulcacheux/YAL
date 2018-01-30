extern fn printf(string, ...) -> int;
extern fn scanf(string, ...) -> int;

fn printInt(x: int) {
    printf("%d\n", x);
}

fn printDouble(x: double) {
    printf("%.1f\n", x);
}

fn printString(x: string) {
    printf("%s\n", x);
}

fn readInt() -> int {
    let res: int;
    scanf("%d", &res);
    return res;
}

fn readDouble() -> double {
    let res: double;
    scanf("%lf", &res);
    return res;
}
