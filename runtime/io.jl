extern int printf(string, ...);
extern int scanf(string, ...);
extern int puts(string, ...);

void printInt(int x) {
    printf("%d\n", x);
}

void printDouble(double x) {
    printf("%.1f\n", x);
}

void printString(string x) {
    puts(x);
}

int readInt() {
    int res;
    scanf("%d", &res);
    return res;
}

double readDouble() {
    double res;
    scanf("%lf", &res);
    return res;
}
