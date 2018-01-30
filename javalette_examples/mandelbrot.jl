int main() {
    double y = -1.2;
    while (y < 1.2) {
        
        double x = -2.05;
        while (x < 0.55) {
            double real = 0.0;
            double imag = 0.0;
            int iter = 0;
            
            while (iter < 100) {
                double next_real = real * real - imag * imag + x;
                double next_imag = 2.0 * real * imag + y;

                real = next_real;
                imag = next_imag;

                iter = iter + 1;
            }
            
            if (real * real + imag * imag < 4.0) {
                printf("#");
            } else {
                printf(".");
            }

            x = x + 0.03;
        }
        printf("\n");

        y = y + 0.05;
    }
        

    return 0;
}
