fn main() -> int {
    let y: double = 1.0;
    while (y >= -1.0) {
        let x: double = -2.5;
        while (x < 1.0) {
            let real: double = 0.0;
            let imag: double = 0.0;
            let iter: int = 0;
            let max_iter: int = 1000;

            while (real * real + imag * imag < 4.0 && iter < max_iter) {
                let next_real: double = real * real - imag * imag + x;
                let next_imag: double = 2.0 * real * imag + y;

                real = next_real;
                imag = next_imag;

                iter++;
            }
            
            if (iter == max_iter) {
                printf("#");
            } else {
                printf(".");
            }

            x = x + 0.03;
        }
        printf("\n");

        y = y - 0.05;
    }
        

    return 0;
}
