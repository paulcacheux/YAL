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

// for the read functions we need pointer types
