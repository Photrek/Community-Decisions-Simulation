// Include standard libraries for input/output, limits, standard library functions, math functions, and time functions.
#include <stdio.h>
#include <limits.h>
#include <stdlib.h>
#include <math.h>
#include <time.h>

// Define constants for maximum number of nodes and time steps.
#define Nmax 10001
#define tmax 1000001

// Declare a file pointer for data output.
FILE *data;

// Matrices and arrays for future network use and node properties.
int s[Nmax], votes[Nmax], sigma[Nmax], u[Nmax];
int i, j, N, v, run, nruns;

// Variables for calculations and results.
double r, p, nup, ndown, w, welfare;
double np, nm, totalu, scale; 
double votesprop1, votesprop2, votes1, votes2, totalvotes;
double wsum, nupsum, ndownsum, votesprop1sum, magsum, votesprop2sum;

// Buffer for file names.
char name[200];

// Long double for fractional values.
long double frac, multi;

// Static variables for random number generation.
static unsigned int ux, uy;
static float h_scale;

/*****************************************************************************/
/*****************************************************************************/

// Function to set initial values for parameters.
void ALLSET()
{
    p = 0.30;          // Set probability parameter.
    N = 1024;          // Set number of nodes.
    nruns = 5000;      // Set number of runs for simulation.
    frac = 0.00;       // Set initial fraction.
    multi = 1000;      // Set multiplier.
}

/*****************************************************************************/
/*****************************************************************************/

// Function to generate a random floating-point number using XOR-shift algorithm.
float xor64()
{
    h_scale = (float)(1.0 / pow(2.0, 32.0));  // Scaling factor.
    unsigned int b = (ux ^ (ux << 8));        // XOR-shift transformation.
    ux = uy;                                  // Update ux with uy.
    uy = (uy ^ (uy >> 22)) ^ (b ^ (b >> 9));  // Update uy with new value.
    return ((float)uy) * h_scale;             // Return random float.
}

/*****************************************************************************/
/*****************************************************************************/

// Function to initialize all spins to zero.
void SPINNING()
{
    for (i = 1; i <= N; i++) {
        s[i] = 0;  // Set spin to zero.
    }
}

/*****************************************************************************/
/*****************************************************************************/

// Function to distribute credit values among nodes.
void CREDITDISTRO()
{
    for (i = 1; i <= N; i++) {
        sigma[i] = 1;  // Initialize sigma values to 1.
    }
    
    int Nfrac = N * frac;  // Calculate the number of nodes to modify.
    int j = 0;
    while (j < Nfrac) {
        i = rand() % N + 1;  // Select a random node.
        
        if (sigma[i] == 1) {
            sigma[i] = multi;  // Set a new sigma value.
            s[i] = -s[i];      // Flip the spin.
            j++;
        }    
    }
}

/*****************************************************************************/
/*****************************************************************************/

// Function to initialize utility values for nodes.
void UTILITYDISTRO()
{
    totalu = 0.0;  // Reset total utility.
    
    for (i = 1; i <= N; i++) {
        u[i] = 1;        // Set utility to 1.
        totalu += u[i];  // Accumulate total utility.
    }
}

/*****************************************************************************/
/*****************************************************************************/

// Function to randomly assign initial spins to nodes.
void IDENTIFICATION()
{
    for (i = 1; i <= N; i++) {
        r = xor64();         // Generate a random number.
        s[i] = (r < p) ? 1 : -1;  // Assign spin based on probability.
    }
}

/*****************************************************************************/
/*****************************************************************************/

// Function to cast votes based on spins and sigma values.
void CASTVOTES()
{
    votesprop1 = votesprop2 = 0.0;  // Reset vote proportions.
    totalvotes = 0.0;  // Reset total votes.
    nup = ndown = 0.0;  // Reset counts for up and down spins.
    
    for (i = 1; i <= N; i++) {
        if (s[i] > 0) {  // If spin is positive.
            votes[i] = sqrt(sigma[i]);  // Assign vote based on sigma.
            votesprop1 += votes[i];     // Accumulate votes for positive spin.
            totalvotes += votes[i];     // Accumulate total votes.
            nup++;                      // Increment up spin count.
        }
        else {  // If spin is negative.
            votes[i] = sqrt(sigma[i]);  // Assign vote based on sigma.
            votesprop2 += votes[i];     // Accumulate votes for negative spin.
            totalvotes += votes[i];     // Accumulate total votes.
            ndown++;                    // Increment down spin count.
        }
    }
}

/*****************************************************************************/
/*****************************************************************************/

// Function to calculate various metrics based on votes and spins.
void CALC()
{
    welfare = 0.0;
    w = 0.0;
    
    for (i = 1; i <= N; i++) {
        welfare += s[i] * votes[i];  // Calculate welfare.
    }
    
    for (i = 1; i <= N; i++) {
        if (s[i] * welfare > 0) {
            w += u[i];  // Accumulate utility for positive welfare.
        }
    }
    
    w = w / totalu;  // Normalize utility.
    votesprop1 = votesprop1 / totalvotes;  // Normalize vote proportions.
    votesprop2 = votesprop2 / totalvotes;
    nup = nup / N;  // Normalize up and down counts.
    ndown = ndown / N;
}

/*****************************************************************************/
/*****************************************************************************/

// Function to store results in a data file.
void DATA()
{
    fprintf(data, "%Le\t", frac);          // Write fraction to file.
    fprintf(data, "%f\t", wsum);           // Write welfare sum.
    fprintf(data, "%f\t", votesprop1sum);  // Write vote proportion sum for positive spin.
    fprintf(data, "%f\t", votesprop2sum);  // Write vote proportion sum for negative spin.
    fprintf(data, "%f\t", nupsum);         // Write up spin proportion sum.
    fprintf(data, "%f\t", ndownsum);       // Write down spin proportion sum.
    fprintf(data, "%f\n", magsum);         // Write magnetization sum.
}

/*****************************************************************************/
/***************************** END OF FUNCTIONS ******************************/

// Main function to set up and run the simulation.
int main() {

    scale = 1.0 / pow(2.0, 32.0) + 1;  // Initialize scaling factor.
    scale = 1.0 / scale;               // Adjust scaling factor.
    srand(time(0));                    // Seed random number generator.
    
    for (v = 0; v < 100; ++v) ux = rand();  // Initialize ux with random values.
    for (v = 0; v < 100; ++v) uy = rand();  // Initialize uy with random values.

    ALLSET();  // Set initial parameters.
    
    // Create a file name based on parameters.
    sprintf(name, "N%d-p%f-multi%Le.txt", N, p, multi);
    
    // Open a file for writing data.
    data = fopen(name, "w");
    if (!data) {
        printf("\n\n Error!\n\n");  // Handle file open error.
    }
        
    // Write column headers to the file.
    fprintf(data, "frac\t");
    fprintf(data, "w\t");
    fprintf(data, "prop1\t");
    fprintf(data, "prop2\t");
    fprintf(data, "nup\t");
    fprintf(data, "ndown\t");
    fprintf(data, "mag\n");
    fclose(data);  // Close the file.
    
    // Loop over different fractions of nodes to modify.
    for (frac = 0.0; frac <= 0.10; frac += 0.001) {
        // Initialize sums for metrics.
        wsum = 0.0;
        votesprop1sum = 0.0;
        votesprop2sum = 0.0;
        nupsum = 0.0;
        ndownsum = 0.0;
        magsum = 0.0;
        
        // Loop over multiple runs to collect statistics.
        for (run = 1; run <= nruns; run++) {
            SPINNING();       // Initialize spins.
            IDENTIFICATION(); // Assign spins.
            CREDITDISTRO();   // Distribute credit.
            UTILITYDISTRO();  // Distribute utility.
            CASTVOTES();      // Cast votes.
            CALC();           // Calculate metrics.
            
            wsum += w;                   // Accumulate welfare.
            votesprop1sum += votesprop1; // Accumulate positive vote proportion.
            votesprop2sum += votesprop2; // Accumulate negative vote proportion.
            nupsum += nup;               // Accumulate up spin count.
            ndownsum += ndown;           // Accumulate down spin count.
            magsum += nup - ndown;       // Accumulate magnetization.
        }    
    
        // Normalize sums by the number of runs.
        wsum /= nruns;
        votesprop1sum /= nruns;
        votesprop2sum /= nruns;
        nupsum /= nruns;
        ndownsum /= nruns;
        magsum /= nruns;
    
        // Append results to the data file.
        data = fopen(name, "a");
        DATA();
        fclose(data);
    }
}
