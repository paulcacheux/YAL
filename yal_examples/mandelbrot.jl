fn main() -> int {
    let y: double = -1.2;
    while (y < 1.2) {
        let x: double = -2.05;
        while (x < 0.55) {
            let real: double = 0.0;
            let imag: double = 0.0;
            let iter: int = 0;

            while (iter < 100) {
                let next_real: double = real * real - imag * imag + x;
                let next_imag: double = 2.0 * real * imag + y;

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
