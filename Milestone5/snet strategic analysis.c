//bringing the tools
#include <stdlib.h>
#include <stdio.h>
#include <time.h>
#include <math.h>
#include <string.h>

//system parameters

//number of individuals
#define N 150

#define fi (0.00)
#define ff (1.00)
#define df (0.05)

//number of proposals per pool
#define NproposalsperPools (33)

#define Npolls (6)

//number of proposals available to vote
#define Nproposals (Npolls*NproposalsperPools)

//number of experiments
#define Nxps 100000

//Number of experiments to write data in txt files
#define backUpRate (1000) 

//Using several threads to run the simulation
#define Nstages (21)

//proportional constant of the business model of inertia 
#define InertiaProp (3)

//probability of an indiviudal postint a rate in the platform
#define Pposting (0.4)

//parameter that controls how the number of people rating one proposal impacts the nonconformity inertia of the other users.
#define socialPressure (0.01)

//probability of an user skiping a proposal. If the user do not skip, it makes a grade from 1 to 10 to the proposal and vote on it.
#define Pskip (2.0/3)

#define AverageInertia (0.10)

//Users balance distribution parameters
#define y0b 0.09436
#define ab 1.75759
#define rb 1.37562
#define ub -0.5

//community RFP funding request distribution parameters 
#define y0crfp 7.69231e-5
#define x0crfp 110000.0
#define A1crfp 6.41026e-6
#define t1crfp 3640.95691
#define minFundingcrfp 108000.0
#define maxFundingcrfp 130000.0  

//Market initiative funding request distribution parameters 
#define y0mi 5.74855e-5
#define xcmi 6.285081e107
#define wmi 9.82269e35
#define Ami -8.8208e34

//Miscellaneous funding request distribution parameters 
#define y0mll 1.05893
#define xcmll 41038.4187
#define wmll 23606.70128
#define Amll 231036.8138

//New projects funding request distribution parameters 
#define A1np -6.1238e-7
#define A2np -7.7718e-6
#define x0np 18167.28621
#define pnp 6.56315

//RFP design funding request distribution parameters 
#define y0rfpd 4.16667e-5
#define x0rfpd 13503.49983
#define A1rfpd 4.51354e-70
#define t1rfpd 79.16707
#define minFundingrfpd 16000.0
#define maxFundingrfpd 26000.0  // Set a reasonable upper limit for the funding range

//funding money fraction of each pool of the total proposals funding request
#define communityRFPfunding 0.2051282051
#define Ideationfunding 0.3856041131
#define MarketInitiativefunding 0.1887091539
#define Miscellaneousfunding 0.1443001443
#define NewProjectsfunding 0.1635055592
#define RFPDesignfunding 0.3668378577

//coupled gaussian parameters
#define kappa (2.0) //related to comunity extremism level
#define muMin (-100.0) //related to the community average opinion on the proposal
#define muMax (100.0) //related to the community average opinion on the proposal
#define sigma (1.0)//related to community noise in interpreatating the proposals

//strategic voting parameter
#define Ki 1
#define Kf 3
#define dK 1

//global System variables
long double Inertia[N], rating[N][Nproposals], proposalRating[Nproposals] ;
long double voting_rating[N][Nproposals];
int NumberRatings[Nproposals],  IndividualVotes[Nproposals];
long double money[N], funding[Nproposals], proposalVotes[Nproposals], Impact[Nproposals];
long double totalSQRTmoney, totalMoney;
int MostVotedProposals[Nproposals], NfundedProposals;
int fundedProposals[Nproposals];
long double f, moneyMin, moneyMax;
int favoriteProposals[N][Nproposals], proposalsToVote[N][Nproposals];
int stage, stagesNeeded;
int agentType[N];
long double max_sentiment[N], min_sentment[N], MoneyPercent[Nproposals];
long double poolFunding[Npolls];

long double W;
long double WextFully, WextFullyStrategic, WextFullyNonstrategic;
long double WextFullySkip, WextFullySkipStrategic, WextFullySkipNonstrategic;
long double Wext[Kf], WextStrategic[Kf], WextNonStrategic[Kf];
long double WextSkip[Kf], WextSkipStrategic[Kf], WextSkipNonStrategic[Kf];
long double Weco[Kf], WecoStrategic[Kf], WecoNonStrategic[Kf];
long double WecoExtreme[Kf], WecoExtremeStrategic[Kf], WecoExtremeNonStrategic[Kf];

//arquive variables
char txt[200];
FILE *fp;
FILE* read; 
char character;
char write[300];

//random number
#define rn ((float)(rand()))/(float)(RAND_MAX)

struct STAGE
{
	float INITIAL;
	float FINAL;
};

//finding the initial points from the simulation of each thread
struct STAGE POINTS(float initial_point, float final_point, float increment, int number_stages)
{    
	struct STAGE POINT;
	
	int Npoints_total, Npoints_per_stage;
	
	Npoints_total = round((final_point - initial_point)/increment) + 1;
	
	Npoints_per_stage = round((double)Npoints_total/number_stages);
	
	if(Npoints_per_stage == 0)
		stagesNeeded = 1;
	else
		stagesNeeded = ceil((float)Npoints_total/Npoints_per_stage);
	
	if(stagesNeeded > Nstages)
		stagesNeeded = Nstages;
	
	printf("please, set the simulation stage as a integer between 1 and %d:", stagesNeeded);
	scanf("%d", &stage);
	
	//predicting initial and final points of each stage with lorenz corrections
	POINT.INITIAL = initial_point + (stage-1)*Npoints_per_stage*increment;
	POINT.FINAL = initial_point + (stage*Npoints_per_stage -1)*increment + 0.5*increment;
	if(stage == Nstages || stagesNeeded == 1)
		POINT.FINAL = final_point + 0.5*increment;
	return (POINT);
}

// Function to generate a Weibull-distributed random variable
double weibullRandom() {
	double U = rn;
	return ub + ab * pow(-log(1 - U), 1 / rb);
}

void Money_Distribution()
{	
	totalMoney = 0.0;
	totalSQRTmoney = 0.0;
	for(int i=0; i <N; i++)
	{
		//how much balance/tokens each agent has
		money[i] = pow(10, weibullRandom());
		
		totalMoney += money[i];
		totalSQRTmoney += sqrt(money[i]);
	}
}

long double ExponentialFunctioncrfp(long double x) {
	return y0crfp + A1crfp * exp(-(x - x0crfp) / t1crfp);
}

// Optimized function to generate a random number according to the exponential distribution
long double randomExponentialcrfp() {
	long double randomNumber = (long double)rand() / RAND_MAX;  // Uniform random number between 0 and 1
	long double cumulative = 0.0;
	long double expoRN = minFundingcrfp;
	long double dExpoRn = 1;
	long double stepSize = 0.1;  // Use the same step size as in ExponentialCumulativecrfp
	
	// Compute the cumulative directly in the loop
	while (cumulative < randomNumber && expoRN < maxFundingcrfp) {
		cumulative += 0.5 * (ExponentialFunctioncrfp(expoRN) + ExponentialFunctioncrfp(expoRN + stepSize)) * stepSize;
		expoRN += dExpoRn;
	}
	
	return expoRN - dExpoRn;
}

//requested proposal fundings
void CommunityRFPRequestFundingDistribution(int poolNumber)
{	
	long double totalProposalFunding = 0.0;

	int propStart = NproposalsperPools*(poolNumber);
	int propEnd = propStart + NproposalsperPools;
	
	for(int proposal = propStart; proposal < propEnd; proposal++)
	{
		funding[proposal] = randomExponentialcrfp();
		
		totalProposalFunding += funding[proposal];
	}
	
	poolFunding[poolNumber] = communityRFPfunding*totalProposalFunding;
}

//requested proposal fundings
void IdeationRequestFundingDistribution(int poolNumber)
{	
	long double totalProposalFunding = 0.0;
	
	int propStart = NproposalsperPools*(poolNumber);
	int propEnd = propStart + NproposalsperPools;
	
	for(int proposal = propStart; proposal < propEnd; proposal++)
	{
		funding[proposal] = 5000;
		
		totalProposalFunding += funding[proposal];
	}
	
	poolFunding[poolNumber] = Ideationfunding*totalProposalFunding;
}

// Function to compute the log-normal PDF
double logNormalPDF(double x) {
	if (x <= 0) return 0.0; // Log-normal is not defined for x <= 0
	return y0mi + (Ami / (sqrt(2 * M_PI) * wmi * x)) * exp(-pow(log(x / xcmi), 2) / (2 * wmi * wmi));
}

// Function to generate a log-normal random variable using numerical inverse transform sampling
double logNormalRandom(double stepSize, double maxRange) {
	double uniformRandom = (double)rand() / RAND_MAX;
	double x = stepSize;
	double integral = 0.0; // Accumulate the integral
	
	while (integral < uniformRandom && x < maxRange) {
		double pdfValue = logNormalPDF(x);
		integral += pdfValue * stepSize;  // Trapezoidal rule for integration
		x += stepSize;
		//printf("a %f \n", integral);
	}
	
	return x - stepSize; // Return the last x value within the desired CDF range
}

//requested proposal fundings
void MarketInitiativeFundingDistribution(int poolNumber)
{	
	long double totalProposalFunding = 0.0;
	
	int propStart = NproposalsperPools*(poolNumber);
	int propEnd = propStart + NproposalsperPools;
	
	double stepSize = 1;   // Step size for numerical integration
	double maxRange = 1e8;   // Max range for integration to avoid infinite loops

	
	for(int proposal = propStart; proposal < propEnd; proposal++)
	{
		funding[proposal] = logNormalRandom(stepSize, maxRange);

		
		totalProposalFunding += funding[proposal];
	}
	
	poolFunding[poolNumber] = MarketInitiativefunding*totalProposalFunding;
}

// Function to compute the Gaussian PDF
double gaussianPDF(double x) {
	double normalization = Amll / (wmll * sqrt(M_PI / 2));
	double exponent = -2 * pow((x - xcmll) / wmll, 2);
	return y0mll + normalization * exp(exponent);
}

// Function to generate a standard Gaussian random variable using the Box-Muller transform
double standardGaussianRandom() {
	double u1 = (double)rand() / RAND_MAX;
	double u2 = (double)rand() / RAND_MAX;
	double z0 = sqrt(-2.0 * log(u1)) * cos(2.0 * M_PI * u2);
	return z0;
}

// Function to generate a Gaussian-distributed random variable with given mean and standard deviation
double gaussianRandom(double mean, double stddev) {
	double randomValue;
	do {
		randomValue = mean + stddev * standardGaussianRandom();
	} while (randomValue < 0); // Re-generate if the value is negative
	return randomValue;
}

//requested proposal fundings
void MiscellaneousFundingDistribution(int poolNumber)
{	
	long double totalProposalFunding = 0.0;
	
	int propStart = NproposalsperPools*(poolNumber);
	int propEnd = propStart + NproposalsperPools;
	
	for(int proposal = propStart; proposal < propEnd; proposal++)
		{
			funding[proposal] = gaussianRandom(xcmll, wmll);			
			totalProposalFunding += funding[proposal];
		}
	
	poolFunding[poolNumber] = Miscellaneousfunding*totalProposalFunding;
}

// Function to generate a logistic random variable
double logisticRandom() {
	double U = (double)rand() / RAND_MAX; // Uniform random number between 0 and 1
	double logisticPart = (U - A2np) / (A1np - A2np); // Solve for logistic part [1 + (x/x0)^p]
	double x = x0np * pow(logisticPart - 1.0, 1.0 / pnp); // Isolate x from the logistic equation
	return x;
}

//requested proposal fundings
void NewProjectsFundingDistribution(int poolNumber)
{	
	long double totalProposalFunding = 0.0;
	
	int propStart = NproposalsperPools*(poolNumber);
	int propEnd = propStart + NproposalsperPools;
	
	for(int proposal = propStart; proposal < propEnd; proposal++)
		{
			funding[proposal] =logisticRandom();			
			totalProposalFunding += funding[proposal];
		}
	
	poolFunding[poolNumber] = NewProjectsfunding*totalProposalFunding;
}

// Function to compute the exponential function based on given parameters
long double ExponentialFunctionrfpd(long double x) {
	return y0rfpd + A1rfpd * exp(-(x - x0rfpd) / t1rfpd);
}

// Optimized function to generate a random number according to the exponential distribution
long double randomExponentialrfpd() {
	long double randomNumber = (long double)rand() / RAND_MAX;  // Uniform random number between 0 and 1
	long double cumulative = 0.0;
	long double expoRN = minFundingrfpd;
	long double dExpoRn = 1;
	long double stepSize = 0.1;  // Use the same step size as in ExponentialCumulativerfpd
	
	// Compute the cumulative directly in the loop
	while (cumulative < randomNumber && expoRN < maxFundingrfpd) {
		cumulative += 0.5 * (ExponentialFunctionrfpd(expoRN) + ExponentialFunctionrfpd(expoRN + stepSize)) * stepSize;
		expoRN += dExpoRn;
	}
	
	return expoRN - dExpoRn;
}

//requested proposal fundings
void RFPdesignFundingDistribution(int poolNumber)
{	
	long double totalProposalFunding = 0.0;
	
	int propStart = NproposalsperPools*(poolNumber);
	int propEnd = propStart + NproposalsperPools;
	
	for(int proposal = propStart; proposal < propEnd; proposal++)
		{
			funding[proposal] = 	randomExponentialrfpd();	
			totalProposalFunding += funding[proposal];
		}
	
	poolFunding[poolNumber] = RFPDesignfunding*totalProposalFunding;
}

void GeneratePools()
{
	for(int pollNumber = 0; pollNumber < Npolls; pollNumber++)
	{
		int RandomNumber = rand() % 6;
		
		if(RandomNumber == 0)
			CommunityRFPRequestFundingDistribution(pollNumber);
		
		else if (RandomNumber == 1)
			IdeationRequestFundingDistribution(pollNumber);
		
		else if (RandomNumber == 2)
			MarketInitiativeFundingDistribution(pollNumber);
		
		else if (RandomNumber == 3)
			MiscellaneousFundingDistribution(pollNumber);
		
		else if (RandomNumber == 4)
			NewProjectsFundingDistribution(pollNumber);
		
		else if (RandomNumber == 5)
			RFPdesignFundingDistribution(pollNumber);
	}
}

void InertiaDistribution()
{
	for(int i = 0; i < N; i++)
	{
		Inertia[i] = AverageInertia;
	}

	for(int i = 0; i < N; i++)
	{
		long double peopleWithLessMoney = 0; 
		
		for(int j = 0; j < N; j ++)
		{
			if(money[j] < money[i])
				peopleWithLessMoney++;
		}
		
		Inertia[i] = Inertia[i]*(1 + InertiaProp*peopleWithLessMoney/(N-1));
		
		if(Inertia[i] > 1)
			Inertia[i] = 1;
	}
}

//calculate the weight of a grade. More extreme grades cost more.
//maps grades {1, 2, ,3 ,4 5, 6, 7, 8, 9, 10} to weights {5. 4, 3, 2, 1, 1, 2, 3, 4, 5}.
long double LinearGradeWeight(long double grade)
{
	if(grade <= 5)
		return 6 -grade;
	else
		return grade - 5;
}

//calculate the weight of a grade. More extreme grades cost more.
//maps grades {1, 2, ,3 ,4 5, 6, 7, 8, 9, 10} to weights {25, 16, 9, 4, 1, 1, 4, 9, 16, 25}.
long double QuadraticGradeWeight(long double grade) 
{
	if(grade <= 5)
		return pow((6-grade), 2);
	
	else
		return pow((grade - 5), 2);
}

//calculate the weight of a grade. More extreme grades cost more.
//maps grades {-10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 1, 2, ,3 ,4 5, 6, 7, 8, 9, 10} to weights {100, 81, 64, 49, 36, 25, 16, 9, 4, 1, 1, 4, 9, 16, 25, 36, 49, 64, 81, 100}.
long double QuadraticGradeWeightWithNegatives(long double grade) 
{
	return pow(grade, 2);
}

long double LinearGradeWeightWithNegatives(long double grade) 
{
	return fabsl(grade);
}

long double kappa_log(long double x, long double kappa_distro) 
{
	if (kappa == 0) 
		return log(x);
	
	else 
		return (pow(x, kappa) - 1) / (kappa);
}

long double coupled_gaussian(long double kappa_distro, long double mu_distro, long double sigma_distro) 
{
	long double U1 = rn;
	long double U2 = rn;
	
	long double R = sqrt(kappa_log(pow(U1, -2), kappa));
	long double theta = 2 * M_PI * U2;
	
	long double Z = R * cos(theta);  
	return mu_distro + sigma * Z;
}

void ProposalDynamics()
{
	for(int proposal = 0; proposal < Nproposals; proposal++)
	{
		long double mu_proposal = (rn < 0.5)? muMax*rn : muMin*rn;
		
		//number of people who voted on the proposal
		IndividualVotes[proposal] = 0;
				
		NumberRatings[proposal] = 0;
		proposalRating[proposal] = 0.0;
		
		int i = 0;
		while(NumberRatings[proposal] == 0 && i < N)
		{
			if(rn< Pskip)
				rating[i][proposal] = NAN;
			
			else
			{
				IndividualVotes[proposal]++;
				
				rating[i][proposal] = coupled_gaussian(kappa, mu_proposal, sigma);
								
				if(rn < Pposting)
				{
					proposalRating[proposal] += rating[i][proposal];
					NumberRatings[proposal]++;
				}
			}
			
			i++;
		}
		
		//now, the other agents will rate the proposal
		//one invidiual at a time
		//but they are influenced bu the average rating past users gave
		//how much an agent is influenced by the average majority
		//is modelled by the social validation parameter
		while(i < N)
		{
			if(rn < Pskip)
				rating[i][proposal] = NAN;
			
			else
			{
				IndividualVotes[proposal]++;
				
				//agent independent opinion
				rating[i][proposal] =  coupled_gaussian(kappa, mu_proposal, sigma);
								
				//average past majority rating
				long double averageOpinion = proposalRating[proposal]/(NumberRatings[proposal]);
				
				//social validation on inertia
				long double socialValidation = 1 - Inertia[i]*pow(1-socialPressure, NumberRatings[proposal]);

				//social validation effect
				if(rn < socialValidation)
					rating[i][proposal] += socialValidation*(averageOpinion - rating[i][proposal]); 
				
				//nonconformism
				else
				{
					rating[i][proposal] -= (1 - socialValidation)/(averageOpinion -  rating[i][proposal]);
				}
					
				if(rn < Pposting)
				{
					proposalRating[proposal] += rating[i][proposal];
					NumberRatings[proposal]++;
				}
			}

			i++;
		}
		
		//writing the final average rating values
		proposalRating[proposal] = proposalRating[proposal]/NumberRatings[proposal];
	}
	
	//initially, all agents are honest
	for(int i = 0; i < N; i++)
	{
		agentType[i] = 0;
		for(int proposal = 0; proposal < Nproposals; proposal++)
		{
			voting_rating[i][proposal] = rating[i][proposal];
		}
	}

}

void AgentsDistributionExtreme(int K)
{		
	//initially, all agents are honest
	for(int i = 0; i < N; i++)
		{
			agentType[i] = 0;
			for(int proposal = 0; proposal < Nproposals; proposal++)
				{
					voting_rating[i][proposal] = rating[i][proposal];
				}
		}

	
	
	
	//now, we will select a fraction f of them to peform strategiv voting.
	int Nf = 0;
	int Ntarget = N*f;
	
	while(Nf < Ntarget)
	{
		int agent = rand()%N;
		
		if(agentType[agent] == 0)
		{
			agentType[agent] = 1;
			Nf++;
			
			int preferredProposal[Nproposals];
			
			for(int proposal = 0; proposal < Nproposals; proposal++)
				preferredProposal[proposal] = proposal;
			
			//now, we make a copy of the ratings vector. We don't want to mess the original vector.
			long double copyRatings[Nproposals];
			for(int proposal = 0; proposal < Nproposals; proposal++)
				copyRatings[proposal] = rating[agent][proposal];
				
			//now, we will order the copy votes vector and the index (the proposals) using bubble sort. The goal is that the first entry of the MostVotedProposals will say the proposal number with most votes, and so on.
			for(int i = 0; i < Nproposals - 1; i ++)
			{
				for(int j = 0; j < Nproposals - 1 - i; j++)
				{
					if(copyRatings[j] < copyRatings[j+1])
					{
						long double store = copyRatings[j];
						copyRatings[j] = copyRatings[j+1];
						copyRatings[j+1] = store;
						
						int storeIndex = preferredProposal[j];
						preferredProposal[j] = preferredProposal[j+1];
						preferredProposal[j+1] = storeIndex;
					}
				}
			}
			
			int j = 0;
			int strategiedProposals = 0;
			while(j < Nproposals && strategiedProposals < K)
			{
				int proposal = preferredProposal[j];
				
				if(!isnan(rating[agent][proposal]) && rating[agent][proposal] > 0)
				{
					voting_rating[agent][proposal] = max_sentiment[agent];
					strategiedProposals++;
				}
				
				j++;
			}
			
			for(int proposal = 0; proposal < Nproposals; proposal++)
			{
				if(voting_rating[agent][proposal]!=max_sentiment[agent])
					voting_rating[agent][proposal] = min_sentment[agent];
			}
		}
	}
}

void AgentsDistributionFullyExtreme()
{		
	//initially, all agents are honest
	for(int i = 0; i < N; i++)
		{
			agentType[i] = 0;
			for(int proposal = 0; proposal < Nproposals; proposal++)
				{
					voting_rating[i][proposal] = rating[i][proposal];
				}
		}
	
	//now, we will select a fraction f of them to peform strategiv voting.
	int Nf = 0;
	int Ntarget = N*f;
	
	while(Nf < Ntarget)
	{
		int agent = rand()%N;
		
		if(agentType[agent] == 0)
		{
			agentType[agent] = 1;
			Nf++;
			
			for(int proposal = 0; proposal < Nproposals; proposal++)
			{
				if(rating[agent][proposal] > 0)
					voting_rating[agent][proposal] = max_sentiment[agent];
				
				else
					voting_rating[agent][proposal] = min_sentment[agent];
			}
		}
	}
}

void AgentsDistributionFullyExtremeSkip()
{
	//initially, all agents are honest
	for(int i = 0; i < N; i++)
		{
			agentType[i] = 0;
			for(int proposal = 0; proposal < Nproposals; proposal++)
				{
					voting_rating[i][proposal] = rating[i][proposal];
				}
		}
	
	//initially, all agents are honest
	for(int i = 0; i < N; i++)
	{
		agentType[i] = 0;
		for(int proposal = 0; proposal < Nproposals; proposal++)
		{
			voting_rating[i][proposal] = rating[i][proposal];
		}
	}
		
	//now, we will select a fraction f of them to peform strategiv voting.
	int Nf = 0;
	int Ntarget = N*f;
	
	while(Nf < Ntarget)
	{
		int agent = rand()%N;
		
		if(agentType[agent] == 0)
		{
			agentType[agent] = 1;
			Nf++;
			
			for(int proposal = 0; proposal < Nproposals; proposal++)
			{
				if(rating[agent][proposal] > 0)
					voting_rating[agent][proposal] = max_sentiment[agent];
				
				else
					voting_rating[agent][proposal] = NAN;
			}
		}
	}
}

void AgentsDistributionExtremeSkip(int K)
{	
	//initially, all agents are honest
	for(int i = 0; i < N; i++)
		{
			agentType[i] = 0;
			for(int proposal = 0; proposal < Nproposals; proposal++)
				{
					voting_rating[i][proposal] = rating[i][proposal];
				}
		}
	
	//now, we will select a fraction f of them to peform strategiv voting.
	int Nf = 0;
	int Ntarget = N*f;
	
	while(Nf < Ntarget)
	{
		int agent = rand()%N;
		
		if(agentType[agent] == 0)
		{
			agentType[agent] = 1;
			Nf++;
			
			int preferredProposal[Nproposals];
			
			for(int proposal = 0; proposal < Nproposals; proposal++)
				preferredProposal[proposal] = proposal;
			
			//now, we make a copy of the ratings vector. We don't want to mess the original vector.
			long double copyRatings[Nproposals];
			for(int proposal = 0; proposal < Nproposals; proposal++)
				copyRatings[proposal] = rating[agent][proposal];
				
			//now, we will order the copy votes vector and the index (the proposals) using bubble sort. The goal is that the first entry of the MostVotedProposals will say the proposal number with most votes, and so on.
			for(int i = 0; i < Nproposals - 1; i ++)
			{
				for(int j = 0; j < Nproposals - 1 - i; j++)
				{
					if(copyRatings[j] < copyRatings[j+1])
					{
						long double store = copyRatings[j];
						copyRatings[j] = copyRatings[j+1];
						copyRatings[j+1] = store;
						
						int storeIndex = preferredProposal[j];
						preferredProposal[j] = preferredProposal[j+1];
						preferredProposal[j+1] = storeIndex;
					}
				}
			}
			
			int j = 0;
			int strategiedProposals = 0;
			while(j < Nproposals && strategiedProposals < K)
			{
				int proposal = preferredProposal[j];
				
				if(!isnan(rating[agent][proposal]) && rating[agent][proposal] > 0)
				{
					voting_rating[agent][proposal] = max_sentiment[agent];
					strategiedProposals++;
				}
				
				j++;
			}
			
			for(int proposal = 0; proposal < Nproposals; proposal++)
			{
				if(voting_rating[agent][proposal]!=max_sentiment[agent])
					voting_rating[agent][proposal] = NAN; //skip the proposal
			}
		}
	}
}

void AgentsDistributionEconomist(int K)
{	
	//initially, all agents are honest
	for(int i = 0; i < N; i++)
		{
			agentType[i] = 0;
			for(int proposal = 0; proposal < Nproposals; proposal++)
				{
					voting_rating[i][proposal] = rating[i][proposal];
				}
		}
	
	//now, we will select a fraction f of them to peform strategic voting.
	int Nf = 0;
	int Ntarget = N*f;
	
	while(Nf < Ntarget)
	{
		int agent = rand()%N;
		
		if(agentType[agent] == 0)
		{
			agentType[agent] = 1;
			Nf++;
			
			int preferredProposal[Nproposals];
			
			for(int proposal = 0; proposal < Nproposals; proposal++)
				preferredProposal[proposal] = proposal;
			
			//now, we make a copy of the ratings vector. We don't want to mess the original vector.
			long double copyRatings[Nproposals];
			for(int proposal = 0; proposal < Nproposals; proposal++)
				copyRatings[proposal] = rating[agent][proposal];
				
			//now, we will order the copy votes vector and the index (the proposals) using bubble sort. The goal is that the first entry of the MostVotedProposals will say the proposal number with most votes, and so on.
			for(int i = 0; i < Nproposals - 1; i ++)
			{
				for(int j = 0; j < Nproposals - 1 - i; j++)
				{
					if(copyRatings[j] < copyRatings[j+1])
					{
						long double store = copyRatings[j];
						copyRatings[j] = copyRatings[j+1];
						copyRatings[j+1] = store;
						
						int storeIndex = preferredProposal[j];
						preferredProposal[j] = preferredProposal[j+1];
						preferredProposal[j+1] = storeIndex;
					}
				}
			}
						
			int j = 0;
			int strategiedProposals = 0;
			int strategic[K];
			while(j < Nproposals && strategiedProposals < K)
			{
				int proposal = preferredProposal[j];
				
				if(!isnan(rating[agent][proposal]) && rating[agent][proposal] > 0)
				{
					strategic[strategiedProposals] = proposal;
					strategiedProposals++;
				}
				
				j++;
			}
						
			for(int proposal = 0; proposal < Nproposals; proposal++)
			{
				int found = 0;
				for(int j = 0; j < strategiedProposals; j++)
				{
					if(strategic[j] == proposal)
						found = 1;
				}
				
				if(found == 1)
					voting_rating[agent][proposal] = rating[agent][proposal];
				
				else
					voting_rating[agent][proposal] = NAN;
			}
		}
	}
}

void AgentsDistributionEconomistExtreme(int K)
{	
	
	//initially, all agents are honest
	for(int i = 0; i < N; i++)
		{
			agentType[i] = 0;
			for(int proposal = 0; proposal < Nproposals; proposal++)
				{
					voting_rating[i][proposal] = rating[i][proposal];
				}
		}
	
	
	//now, we will select a fraction f of them to peform strategic voting.
	int Nf = 0;
	int Ntarget = N*f;
	
	while(Nf < Ntarget)
	{
		int agent = rand()%N;
		
		if(agentType[agent] == 0)
		{
			agentType[agent] = 1;
			Nf++;
			
			int preferredProposal[Nproposals];
			
			for(int proposal = 0; proposal < Nproposals; proposal++)
				preferredProposal[proposal] = proposal;
			
			//now, we make a copy of the ratings vector. We don't want to mess the original vector.
			long double copyRatings[Nproposals];
			for(int proposal = 0; proposal < Nproposals; proposal++)
				copyRatings[proposal] = rating[agent][proposal];
				
			//now, we will order the copy votes vector and the index (the proposals) using bubble sort. The goal is that the first entry of the MostVotedProposals will say the proposal number with most votes, and so on.
			for(int i = 0; i < Nproposals - 1; i ++)
			{
				for(int j = 0; j < Nproposals - 1 - i; j++)
				{
					if(copyRatings[j] < copyRatings[j+1])
					{
						long double store = copyRatings[j];
						copyRatings[j] = copyRatings[j+1];
						copyRatings[j+1] = store;
						
						int storeIndex = preferredProposal[j];
						preferredProposal[j] = preferredProposal[j+1];
						preferredProposal[j+1] = storeIndex;
					}
				}
			}
						
			int j = 0;
			int strategiedProposals = 0;
			int strategic[K];
			while(j < Nproposals && strategiedProposals < K)
			{
				int proposal = preferredProposal[j];
				
				if(!isnan(rating[agent][proposal]) && rating[agent][proposal] > 0)
				{
					strategic[strategiedProposals] = proposal;
					strategiedProposals++;
				}
				
				j++;
			}
			
			long double totalOpinion = 0.0;
			for(int j = 0; j < strategiedProposals; j ++)
			{
				int proposal = strategic[j];
				
				totalOpinion += rating[agent][proposal];
			}
			
			for(int proposal = 0; proposal < Nproposals; proposal++)
			{
				int found = 0;
				for(int j = 0; j < strategiedProposals; j++)
				{
					if(strategic[j] == proposal)
						found = 1;
				}
				
				if(found == 1)
					voting_rating[agent][proposal] = rating[agent][proposal]/totalOpinion;
				
				else
					voting_rating[agent][proposal] = NAN;
			}
		}
	}
}

void FindMaximumSentments()
{
	for(int i = 0; i < N; i++)
	{
		max_sentiment[i] = -INFINITY;
		min_sentment[i] =  INFINITY;
		
		for(int proposal = 0; proposal < Nproposals; proposal++)
		{
			if(!isnan(rating[i][proposal]))
			{
				if(rating[i][proposal] > max_sentiment[i])
					max_sentiment[i] = rating[i][proposal];
				
				if(rating[i][proposal] < min_sentment[i])
					min_sentment[i] = rating[i][proposal];
			}
			
		}
	}
}

long double CalculateGrade1to10(int i, int proposal)
{
	return round(9.0*voting_rating[i][proposal] + max_sentiment[i] - 10*min_sentment[i])/(max_sentiment[i] - min_sentment[i]);
}

long double CalculateGradeMinus10to10(int i, int proposal)
{
	return round(20.0*voting_rating[i][proposal] -10.0*(min_sentment[i] + max_sentiment[i]))/(max_sentiment[i] - min_sentment[i]);
}

long double CalculateBinaryGrade(int i, int proposal)
{
	long double y = (2.0*voting_rating[i][proposal] - (max_sentiment[i] + min_sentment[i]))/(max_sentiment[i] - min_sentment[i]);
	
	if(y < 0)
		return -1;
	
	else if (y > 0)
		return 1;
	
	else
		return (rn < 0.5)? 1: -1;
}

void CastVotesSqrtTokens()
{
	for(int proposal = 0; proposal < Nproposals; proposal++)
	{
		proposalVotes[proposal] = 0.0;
		IndividualVotes[proposal] = 0.0;
	}
	
	//calculating the average grade of each proposal
	for(int i = 0; i < N; i ++)
	{
		for(int proposal = 0; proposal < Nproposals; proposal++)
		{
			//if i has not skiped the proposal
			if(!isnan(voting_rating[i][proposal]))
			{
				//grade between 1 and 10
				int grade = CalculateGrade1to10(i, proposal);
									
				proposalVotes[proposal] += grade*sqrt(money[i]);
				
				IndividualVotes[proposal]++;
			}
		}
	}
	
	for(int proposal = 0; proposal < Nproposals; proposal++)
		proposalVotes[proposal] = proposalVotes[proposal]/totalSQRTmoney;
}

void CastBinaryVotesSqrtTokens()
{
	for(int proposal = 0; proposal < Nproposals; proposal++)
	{
		proposalVotes[proposal] = 0.0;
		IndividualVotes[proposal] = 0.0;
	}
	
	//calculating the average grade of each proposal
	for(int i = 0; i < N; i ++)
	{
		for(int proposal = 0; proposal < Nproposals; proposal++)
		{
			//if i has not skiped the proposal
			if(!isnan(voting_rating[i][proposal]))
			{
				//grade between 1 and 10
				int grade = CalculateBinaryGrade(i, proposal);
									
				proposalVotes[proposal] += grade*sqrt(money[i]);		
				
				IndividualVotes[proposal]++;
				
			}
		}
	}
	
	for(int proposal = 0; proposal < Nproposals; proposal++)
		proposalVotes[proposal] = proposalVotes[proposal]/totalSQRTmoney;
}

void CastNegativeVotesSqrtTokens()
{
	for(int proposal = 0; proposal < Nproposals; proposal++)
	{
		proposalVotes[proposal] = 0.0;
		IndividualVotes[proposal] = 0.0;
	}
	
	//calculating the average grade of each proposal
	for(int i = 0; i < N; i ++)
	{
		for(int proposal = 0; proposal < Nproposals; proposal++)
		{
			//if i has not skiped the proposal
			if(!isnan(voting_rating[i][proposal]))
			{
				//grade between -10 and 10
				int grade = CalculateGradeMinus10to10(i, proposal);
								
				proposalVotes[proposal] += grade*sqrt(money[i]);	
				
				IndividualVotes[proposal]++;
			}
		}
	}
	
	for(int proposal = 0; proposal < Nproposals; proposal++)
		proposalVotes[proposal] = proposalVotes[proposal]/totalSQRTmoney;
}

void CastVotesOneCoinOneVote()
{
	for(int proposal = 0; proposal < Nproposals; proposal++)
	{
		proposalVotes[proposal] = 0.0;
		IndividualVotes[proposal] = 0.0;
	}
	
	//calculating the average grade of each proposal
	for(int i = 0; i < N; i ++)
	{		
		for(int proposal = 0; proposal < Nproposals; proposal++)
		{
			//if i has not skiped the proposal
			if(!isnan(voting_rating[i][proposal]))
			{
				//grade between 1 and 10
				int grade = CalculateGrade1to10(i, proposal);
										
				proposalVotes[proposal] += grade*(money[i]);	
				
				IndividualVotes[proposal]++;
			}
		}
	}
	
	for(int proposal = 0; proposal < Nproposals; proposal++)
		proposalVotes[proposal] = proposalVotes[proposal]/totalMoney;
}

void CastVotesOneWalletOneVote()
{
	for(int proposal = 0; proposal < Nproposals; proposal++)
	{
		proposalVotes[proposal] = 0.0;
		IndividualVotes[proposal] = 0.0;
	}
	
	//calculating the average grade of each proposal
	for(int i = 0; i < N; i ++)
	{		
		for(int proposal = 0; proposal < Nproposals; proposal++)
		{
			//if i has not skiped the proposal
			if(!isnan(voting_rating[i][proposal]))
			{
				//grade between 1 and 10
				int grade = CalculateGrade1to10(i, proposal);
				
				proposalVotes[proposal] += grade;	
				
				IndividualVotes[proposal]++;
			}
		}
	}
	
	for(int proposal = 0; proposal < Nproposals; proposal++)
		proposalVotes[proposal] = proposalVotes[proposal]/N;
}

void GetFavoriteProposals()
{
	//we will make a list with the number of the proposal, going from the most favorite proosal to the less favorite.
	
	//first, just create the list 
	for(int i = 0; i < N; i++)
	{
		for(int proposal = 0; proposal < Nproposals; proposal++)
		{
			favoriteProposals[i][proposal] = proposal;
		}
	}
	
	//now, we make a copy of the ratings vector. We don't want to mess the original vector.
	long double copyRatings[N][Nproposals];
	for(int i = 0; i < N; i++)
	{
		for(int proposal = 0; proposal < Nproposals; proposal++)
		{
			copyRatings[i][proposal] = rating[i][proposal];
		}
		
	}
	
	//now, we will order the copy ratings vector and the index (the proposals) using bubble sort. The goal is that the first entry of the favoriteProposals will say the proposal number with the higher rating, and so on.
	for(int i = 0; i < N; i ++)
	{
		for(int p1 = 0; p1 < Nproposals - 1; p1 ++)
		{
			for(int p2 = 0; p2 < Nproposals - 1 - p1; p2++)
			{
				if(copyRatings[i][p2] < copyRatings[i][p2+1])
				{
					long double store = copyRatings[i][p2];
					copyRatings[i][p2] = copyRatings[i][p2+1];
					copyRatings[i][p2+1] = store;
					
					int storeIndex = favoriteProposals[i][p2];
					favoriteProposals[i][p2] = favoriteProposals[i][p2+1];
					favoriteProposals[i][p2+1] = storeIndex;
				}
			}
		}
	}
}

void DecideWichProjetcsToVote()
{
	//initializing
	for(int i = 0; i < N; i ++)
	{
		for(int proposal = 0; proposal < Nproposals; proposal++)
		{
			proposalsToVote[i][proposal] = -1;
		}
	}
	
	//deciding proposals will actually vote.
	//going from the most favorite proposal to the less favorite.
	for(int i = 0; i < N; i++)
	{
		int proposalIndex = 0;
		int proposalIndexVote = 0;
		while(proposalIndex < Nproposals)
		{
			int proposal = favoriteProposals[i][proposalIndex];
			
			if(!isnan(voting_rating[i][proposal]))
			{
				proposalsToVote[i][proposalIndexVote] = favoriteProposals[i][proposalIndex];
				
				proposalIndexVote++;
			}
			
			proposalIndex++;
		}
	}
}

void CastVotesPluralityVoting()
{
	GetFavoriteProposals();
	DecideWichProjetcsToVote();
	
	long double proposalVoteWeight[Nproposals];
	
	for(int proposal = 0; proposal < Nproposals; proposal++)
	{
		proposalVotes[proposal] = 0.0;
		proposalVoteWeight[proposal] = 0.0;
		
		IndividualVotes[proposal] = 0.0;
	}
	
	for(int i = 0; i < N; i ++)
	{
		long double totalGradeWeight = 0;
		
		int proposalIndex = 0;
		while(proposalIndex < Nproposals && proposalsToVote[i][proposalIndex] != -1)
		{
			int proposal = proposalsToVote[i][proposalIndex];
			
			totalGradeWeight += LinearGradeWeight(CalculateGrade1to10(i, proposal));;		
			
			proposalIndex++;
		}
				
		if(totalGradeWeight)
		{
			int proposalIndex = 0;
			while(proposalIndex < Nproposals && proposalsToVote[i][proposalIndex] != -1)
			{
				int proposal = proposalsToVote[i][proposalIndex];
				
				long double grade = CalculateGrade1to10(i, proposal);
				
				long double weightGrade = LinearGradeWeight(grade);
				
				proposalVotes[proposal] += grade*sqrt(weightGrade*money[i]/totalGradeWeight);
				
				proposalVoteWeight[proposal] += sqrt(weightGrade*money[i]/totalGradeWeight);
				
				IndividualVotes[proposal]++;
				
				proposalIndex++;
			}
		}
	}
	
	for(int proposal = 0; proposal < Nproposals; proposal++)
		proposalVotes[proposal] = proposalVotes[proposal]/proposalVoteWeight[proposal];
}

void CastVotesUnboundedPluralityVoting()
{
	GetFavoriteProposals();
	DecideWichProjetcsToVote();
	
	long double proposalVoteWeight[Nproposals];
	
	for(int proposal = 0; proposal < Nproposals; proposal++)
	{
		proposalVotes[proposal] = 0.0;
		
		IndividualVotes[proposal] = 0.0;
		
		MoneyPercent[proposal] = 0.0;
	}
	
	for(int i = 0; i < N; i ++)
	{		
		long double totalOpinion = 0.0;
		for(int proposal = 0; proposal < Nproposals; proposal++)
		{
			if(voting_rating[i][proposal] > 0)
				totalOpinion += voting_rating[i][proposal];
		}
		
		if(!isnan(totalOpinion) && totalOpinion > 0)
		{
			int proposalIndex = 0;
			while(proposalIndex < Nproposals && proposalsToVote[i][proposalIndex] != -1)
			{
				int proposal = proposalsToVote[i][proposalIndex];
				
				if(voting_rating[i][proposal] > 0)
				{
					proposalVotes[proposal] += sqrt(voting_rating[i][proposal]*money[i]/totalOpinion);
					
					IndividualVotes[proposal]++;
					
					MoneyPercent[proposal] += voting_rating[i][proposal]/totalOpinion;
				}
				
				proposalIndex++;
			}
		}
	}
	
	for(int proposal = 0; proposal < Nproposals; proposal++)
		MoneyPercent[proposal] = MoneyPercent[proposal]/N;
}

void CastVotesUnboundedPluralityVotingWithoutSqrt()
{
	GetFavoriteProposals();
	DecideWichProjetcsToVote();
	
	long double proposalVoteWeight[Nproposals];
	
	for(int proposal = 0; proposal < Nproposals; proposal++)
	{
		proposalVotes[proposal] = 0.0;
		
		IndividualVotes[proposal] = 0.0;
		
		MoneyPercent[proposal] = 0.0;
	}
	
	for(int i = 0; i < N; i ++)
	{		
		long double totalOpinion = 0.0;
		for(int proposal = 0; proposal < Nproposals; proposal++)
		{
			if(voting_rating[i][proposal] > 0)
				totalOpinion += voting_rating[i][proposal];
		}
		
		if(!isnan(totalOpinion) && totalOpinion > 0)
		{
			int proposalIndex = 0;
			while(proposalIndex < Nproposals && proposalsToVote[i][proposalIndex] != -1)
			{
				int proposal = proposalsToVote[i][proposalIndex];
				
				if(voting_rating[i][proposal] > 0)
				{
					proposalVotes[proposal] += (voting_rating[i][proposal]*money[i]/totalOpinion);
					
					IndividualVotes[proposal]++;
					
					MoneyPercent[proposal] += voting_rating[i][proposal]/totalOpinion;
				}
				
				proposalIndex++;
			}
		}
	}
	
	for(int proposal = 0; proposal < Nproposals; proposal++)
		MoneyPercent[proposal] = MoneyPercent[proposal]/N;
}

double sign(long double x) 
{
	if (x > 0) 
		return 1;
	
	else if (x < 0) 
		return -1;
	
	else 
		return 0;
}

void CastVotesUnboundedPluralityVotingWithNegatives()
{
	GetFavoriteProposals();
	DecideWichProjetcsToVote();
	
	long double proposalVoteWeight[Nproposals];
	
	for(int proposal = 0; proposal < Nproposals; proposal++)
	{
		proposalVotes[proposal] = 0.0;
		IndividualVotes[proposal] = 0.0;
		
		MoneyPercent[proposal] = 0.0;
	}
	
	for(int i = 0; i < N; i ++)
	{		
		long double totalOpinion = 0.0;
		for(int proposal = 0; proposal < Nproposals; proposal++)
		{
			totalOpinion += fabsl(voting_rating[i][proposal]);
		}
		
		if(!isnan(totalOpinion) && totalOpinion > 0)
		{
			int proposalIndex = 0;
			while(proposalIndex < Nproposals && proposalsToVote[i][proposalIndex] != -1)
			{
				int proposal = proposalsToVote[i][proposalIndex];
				
				proposalVotes[proposal] += sign(voting_rating[i][proposal])*sqrt(fabsl(voting_rating[i][proposal])*money[i]/totalOpinion);
				
				IndividualVotes[proposal]++;
				
				proposalIndex++;
				
				if(sign(voting_rating[i][proposal]) > 0)
					MoneyPercent[proposal] += (voting_rating[i][proposal])/totalOpinion;
			}			
		}
	}
	
	for(int proposal = 0; proposal < Nproposals; proposal++)
		MoneyPercent[proposal] = MoneyPercent[proposal]/N;
}

void CastVotesPluralityVotingWithNegatives()
{
	GetFavoriteProposals();
	DecideWichProjetcsToVote();
	
	long double proposalVoteWeight[Nproposals];
	
	for(int proposal = 0; proposal < Nproposals; proposal++)
	{
		proposalVotes[proposal] = 0.0;
		proposalVoteWeight[proposal] = 0.0;
		
		IndividualVotes[proposal] = 0.0;
	}
	
	for(int i = 0; i < N; i ++)
	{
		long double totalGradeWeight = 0;
		
		int proposalIndex = 0;
		while(proposalIndex < Nproposals && proposalsToVote[i][proposalIndex] != -1)
		{
			int proposal = proposalsToVote[i][proposalIndex];
			
			totalGradeWeight += LinearGradeWeightWithNegatives(CalculateGradeMinus10to10(i, proposal));;		
			
			proposalIndex++;
		}
				
		if(totalGradeWeight)
		{
			int proposalIndex = 0;
			while(proposalIndex < Nproposals && proposalsToVote[i][proposalIndex] != -1)
			{
				int proposal = proposalsToVote[i][proposalIndex];
				
				long double grade = CalculateGradeMinus10to10(i, proposal);
				
				long double weightGrade = LinearGradeWeightWithNegatives(grade);
				
				proposalVotes[proposal] += grade*sqrt(weightGrade*money[i]/totalGradeWeight);
				
				proposalVoteWeight[proposal] += sqrt(weightGrade*money[i]/totalGradeWeight);
				
				IndividualVotes[proposal]++;
				
				proposalIndex++;
			}
		}
	}
	
	for(int proposal = 0; proposal < Nproposals; proposal++)
		proposalVotes[proposal] = proposalVotes[proposal]/proposalVoteWeight[proposal];

}

void CastQuadraticVotesPluralityVotingWithNegatives()
{
	GetFavoriteProposals();
	DecideWichProjetcsToVote();
	
	long double proposalVoteWeight[Nproposals];
	
	for(int proposal = 0; proposal < Nproposals; proposal++)
	{
		proposalVotes[proposal] = 0.0;
		proposalVoteWeight[proposal] = 0.0;
		
		IndividualVotes[proposal] = 0.0;
	}
	
	for(int i = 0; i < N; i ++)
	{
		long double totalGradeWeight = 0;
		
		int proposalIndex = 0;
		while(proposalIndex < Nproposals && proposalsToVote[i][proposalIndex] != -1)
		{
			int proposal = proposalsToVote[i][proposalIndex];
			
			totalGradeWeight += QuadraticGradeWeightWithNegatives(CalculateGradeMinus10to10(i, proposal));;		
			
			proposalIndex++;
		}
				
		if(totalGradeWeight)
		{
			int proposalIndex = 0;
			while(proposalIndex < Nproposals && proposalsToVote[i][proposalIndex] != -1)
			{
				int proposal = proposalsToVote[i][proposalIndex];
				
				long double grade = CalculateGradeMinus10to10(i, proposal);
				
				long double weightGrade = QuadraticGradeWeightWithNegatives(grade);
				
				proposalVotes[proposal] += grade*sqrt(weightGrade*money[i]/totalGradeWeight);
				
				proposalVoteWeight[proposal] += sqrt(weightGrade*money[i]/totalGradeWeight);
				
				IndividualVotes[proposal]++;
				
				proposalIndex++;
				
			}
		}
	}
	
	for(int proposal = 0; proposal < Nproposals; proposal++)
		proposalVotes[proposal] = proposalVotes[proposal]/proposalVoteWeight[proposal];

}

void CastQuadraticVotesPluralityVoting()
{
	GetFavoriteProposals();
	DecideWichProjetcsToVote();
	
	long double proposalVoteWeight[Nproposals];
	
	for(int proposal = 0; proposal < Nproposals; proposal++)
	{
		proposalVotes[proposal] = 0.0;
		proposalVoteWeight[proposal] = 0.0;
		
		IndividualVotes[proposal] = 0.0;
	}
	
	for(int i = 0; i < N; i ++)
	{
		long double totalGradeWeight = 0;
		
		int proposalIndex = 0;
		while(proposalIndex < Nproposals && proposalsToVote[i][proposalIndex] != -1)
		{
			int proposal = proposalsToVote[i][proposalIndex];
			
			totalGradeWeight += QuadraticGradeWeight(CalculateGrade1to10(i, proposal));;		
			
			proposalIndex++;
		}
				
		if(totalGradeWeight)
		{
			int proposalIndex = 0;
			while(proposalIndex < Nproposals && proposalsToVote[i][proposalIndex] != -1)
			{
				int proposal = proposalsToVote[i][proposalIndex];
				
				long double grade = CalculateGrade1to10(i, proposal);
				
				long double weightGrade = QuadraticGradeWeight(grade);
				
				proposalVotes[proposal] += grade*sqrt(weightGrade*money[i]/totalGradeWeight);
				
				proposalVoteWeight[proposal] += sqrt(weightGrade*money[i]/totalGradeWeight);
				
				IndividualVotes[proposal]++;
				
				proposalIndex++;
			}
		}
	}
	
	for(int proposal = 0; proposal < Nproposals; proposal++)
		proposalVotes[proposal] = proposalVotes[proposal]/proposalVoteWeight[proposal];

}

void GetMostVotedProposals()
{
	// Initialize the MostVotedProposals array with proposal indices
	for (int proposal = 0; proposal < Nproposals; proposal++)
	{
		MostVotedProposals[proposal] = proposal;
	}
	
	// Make a copy of the proposalVotes array to preserve the original data
	long double copyVotes[Nproposals];
	for (int proposal = 0; proposal < Nproposals; proposal++)
	{
		copyVotes[proposal] = proposalVotes[proposal];
	}
	
	// Bubble sort within each pool to order proposals by vote count
	for (int poll = 0; poll < Npolls; poll++)
	{
		int propStart = NproposalsperPools * poll;
		int propEnd = propStart + NproposalsperPools;
		
		for (int i = 0; i < NproposalsperPools - 1; i++)
		{
			for (int j = propStart; j < propEnd - 1 - i; j++)
			{
				if (copyVotes[j] < copyVotes[j + 1])
				{
					// Swap votes
					long double store = copyVotes[j];
					copyVotes[j] = copyVotes[j + 1];
					copyVotes[j + 1] = store;
					
					// Swap proposal indices
					int storeIndex = MostVotedProposals[j];
					MostVotedProposals[j] = MostVotedProposals[j + 1];
					MostVotedProposals[j + 1] = storeIndex;
				}
			}
		}
	}
}

void GetAwardedProposals()
{
	//first, we need to determine the eligible proposals. Eligible porposals must have received votes from at least 1% of the voters.	
	//the project also needs a minimum average grad of 6.5 and must fit the pools remaining budget after higher voter proposals are funded.
	
	NfundedProposals = 0;
	
	for (int poll = 0; poll < Npolls; poll++)
	{
		int propStart = NproposalsperPools*(poll);
		int propEnd = propStart + NproposalsperPools;
		
		long double MoneyAvalaibleToFund = poolFunding[poll];

		//from the most voted proposal to the less voted proposal
		for(int j = propStart; j < propEnd; j++)
		{
			int proposal = MostVotedProposals[j];
			
			//check if proposal is eligible
			if(proposalVotes[proposal] >= 6.5 && (long double)IndividualVotes[proposal] >= 0.01*N)
			{
				//if there is suficient funding money to fund the proposal
				if(funding[proposal] <= MoneyAvalaibleToFund)
				{
					fundedProposals[NfundedProposals] = proposal;
					NfundedProposals++;
					MoneyAvalaibleToFund = MoneyAvalaibleToFund - funding[proposal];
				}
			}
		}
	}
}

void GetNegativeAwardedProposals()
{
	//first, we need to determine the eligible proposals. Eligible porposals must have received votes from at least 1% of the voters.	
	//the project also needs a minimum average grad of 6.5 and must fit the pools remaining budget after higher voter proposals are funded.
			
	NfundedProposals = 0;
	
	for (int poll = 0; poll < Npolls; poll++)
		{
			int propStart = NproposalsperPools*(poll);
			int propEnd = propStart + NproposalsperPools;
			
			long double MoneyAvalaibleToFund = poolFunding[poll];

			
			//from the most voted proposal to the less voted proposal
			for(int j = propStart; j < propEnd; j++)
				{
					int proposal = MostVotedProposals[j];
					
					//check if proposal is eligible
					if(proposalVotes[proposal] >= 1.0 && (long double)IndividualVotes[proposal] >= 0.01*N)
						{
							//if there is suficient funding money to fund the proposal
							if(funding[proposal] <= MoneyAvalaibleToFund)
								{
									fundedProposals[NfundedProposals] = proposal;
									NfundedProposals++;
									MoneyAvalaibleToFund = MoneyAvalaibleToFund - funding[proposal];
								}
						}
				}
		}
}


void GetUnboudedAwardedProposals()
{
	//first, we need to determine the eligible proposals. Eligible porposals must have received votes from at least 1% of the voters.	
	//the project also needs a minimum average grad of 6.5 and must fit the pools remaining budget after higher voter proposals are funded.
	
	NfundedProposals = 0;
	
	for (int poll = 0; poll < Npolls; poll++)
		{
			int propStart = NproposalsperPools*(poll);
			int propEnd = propStart + NproposalsperPools;
			
			long double MoneyAvalaibleToFund = poolFunding[poll];
			
			//from the most voted proposal to the less voted proposal
			for(int j = propStart; j < propEnd; j++)
				{
					int proposal = MostVotedProposals[j];
					
					//check if proposal is eligible
					if(MoneyPercent[proposal] >= 0.05 && (long double)IndividualVotes[proposal] >= 0.01*N)
						{
							//if there is suficient funding money to fund the proposal
							if(funding[proposal] <= MoneyAvalaibleToFund)
								{
									fundedProposals[NfundedProposals] = proposal;
									NfundedProposals++;
									MoneyAvalaibleToFund = MoneyAvalaibleToFund - funding[proposal];
								}
						}
				}
		}
}
void GetBinaryAwardedProposals()
{
	//first, we need to determine the eligible proposals. Eligible porposals must have received votes from at least 1% of the voters.	
	//the project also needs a minimum average grad of 6.5 and must fit the pools remaining budget after higher voter proposals are funded.
	
	NfundedProposals = 0;
	
	for (int poll = 0; poll < Npolls; poll++)
		{
			int propStart = NproposalsperPools*(poll);
			int propEnd = propStart + NproposalsperPools;
			
			long double MoneyAvalaibleToFund = poolFunding[poll];

			
			//from the most voted proposal to the less voted proposal
			for(int j = propStart; j < propEnd; j++)
				{
					int proposal = MostVotedProposals[j];
					
					//check if proposal is eligible
					if(proposalVotes[proposal] >= 0.65 && (long double)IndividualVotes[proposal] >= 0.01*N)
						{
							//if there is suficient funding money to fund the proposal
							if(funding[proposal] <= MoneyAvalaibleToFund)
								{
									fundedProposals[NfundedProposals] = proposal;
									NfundedProposals++;
									MoneyAvalaibleToFund = MoneyAvalaibleToFund - funding[proposal];
								}
						}
				}
		}
}

int proposalIsFunded(int proposal)
{
	for(int j = 0; j < NfundedProposals; j++)
	{
		if(proposal == fundedProposals[j])
			return 1;
	}
	
	return 0;
}

void welfare()
{	
	W = 0.0;
	long double normalization_factor = 0.0;
	//long double totalNumberVoters = 0;
	
	for(int proposal = 0; proposal < Nproposals; proposal++)
	{
		//for each funded proposal, we calculate the welfare of this proposal on the population.
		for(int i = 0; i < N; i ++)
		{
			//we assume if i skiped the proposal, he/she is indiferent to the proposal, and has no welfare to that proposal.
			if(!isnan(rating[i][proposal]))
			{
				normalization_factor += fabsl(rating[i][proposal]);
				//totalNumberVoters ++;
						
				if(proposalIsFunded(proposal))
					W += rating[i][proposal];
				
				else
					W -= rating[i][proposal];
			}
		}
	}
	
	if(NfundedProposals)
		W = W/normalization_factor;
		
	else
		W = 0.0;	
}

void welfareStrategicAgents()
{	
	W = 0.0;
	long double normalization_factor = 0.0;
	//long double totalNumberVoters = 0;
	
	for(int proposal = 0; proposal < Nproposals; proposal++)
	{
		//for each funded proposal, we calculate the welfare of this proposal on the population.
		for(int i = 0; i < N; i ++)
		{
			//we assume if i skiped the proposal, he/she is indiferent to the proposal, and has no welfare to that proposal.
			if(agentType[i]==1 && !isnan(rating[i][proposal]))
			{
				normalization_factor += fabsl(rating[i][proposal]);
				//totalNumberVoters ++;
						
				if(proposalIsFunded(proposal))
					W += rating[i][proposal];
				
				else
					W -= rating[i][proposal];
			}
		}
	}
	
	if(NfundedProposals)
		W = W/normalization_factor;
		
	else
		W = 0.0;	
}

void welfareNonStrategicAgents()
{	
	W = 0.0;
	long double normalization_factor = 0.0;
	//long double totalNumberVoters = 0;
	
	for(int proposal = 0; proposal < Nproposals; proposal++)
	{
		//for each funded proposal, we calculate the welfare of this proposal on the population.
		for(int i = 0; i < N; i ++)
		{
			//we assume if i skiped the proposal, he/she is indiferent to the proposal, and has no welfare to that proposal.
			if(agentType[i]==0 && !isnan(rating[i][proposal]))
			{
				normalization_factor += fabsl(rating[i][proposal]);
				//totalNumberVoters ++;
						
				if(proposalIsFunded(proposal))
					W += rating[i][proposal];
				
				else
					W -= rating[i][proposal];
			}
		}
	}
	
	if(NfundedProposals)
		W = W/normalization_factor;
		
	else
		W = 0.0;	
}

int effectiveAmt(long double variable)
{
	int effectiveAmt = backUpRate;
	
	//find name of txt
	char txtname [200];
	sprintf(txtname, "%s", "Variable");
	char txtname2 [200];
	sprintf(txtname2, "(%.4Le)", variable);
	strcat(txtname, txtname2);
	char final [200] = ".txt";
	strcat(txtname, final);
	
	//open the file
	read = fopen(txtname, "r");
	
	//check if file exists
	if(read == NULL)
		printf("file can't be opened.\n");
	
	//extract characters from file until end of the file (EOF)
	for (character = getc(read); character != EOF; character = getc(read))
		//increment counter if we find new line
	if(character == '\n')
		effectiveAmt +=backUpRate;
	
	//close the file
	fclose(read);
	
	return effectiveAmt;
}

void SIMULATION(long double variablei, long double variablef, long double dvariable)
{
	//defining the stage points
	struct STAGE POINT; 
	
	//determining the stage of the simulation with the parameters
	POINT = POINTS(variablei, variablef, dvariable, Nstages);
	
	float Nbackups = (float)Nxps/backUpRate;
	for(int backup = 1; backup <= Nbackups; backup++)
	{
		f = POINT.INITIAL;
		for(int step = 0; step <= (POINT.FINAL-POINT.INITIAL)/dvariable; step++)
		{
			//arquive
			sprintf(txt, "Variable(%.4Le).txt", f);
			fp = fopen(txt, "a");
			
			//find effective sample
			int totalAmt = effectiveAmt(f);
							
			long double Wext[Kf], WextStrategic[Kf], WextNonStrategic[Kf];
			long double WextSkip[Kf], WextSkipStrategic[Kf], WextSkipNonStrategic[Kf];
			long double Weco[Kf], WecoStrategic[Kf], WecoNonStrategic[Kf];
			long double WecoExtreme[Kf], WecoExtremeStrategic[Kf], WecoExtremeNonStrategic[Kf];
			
			//initializing the means
			WextFully = 0.0; WextFullyStrategic = 0.0; WextFullyNonstrategic = 0.0;
			WextFullySkip = 0.0; WextFullySkipStrategic = 0.0; WextFullySkipNonstrategic = 0.0;
			for(int K = Ki; K <= Kf; K++)
				{
					Wext[K] = 0;
					WextStrategic[K] = 0;
					WextNonStrategic[K] = 0;
					
					WextSkip[K] = 0;
					WextSkipStrategic[K] = 0;
					WextSkipNonStrategic[K] = 0;
					
					Weco[K] = 0;
					WecoStrategic[K] = 0;
					WecoNonStrategic[K] = 0;
					
					WecoExtreme[K] = 0;
					WecoExtremeStrategic[K] = 0;
					WecoExtremeNonStrategic[K] = 0;
				}
			
			for(int xp = 0; xp < backUpRate; xp++)
			{
				Money_Distribution();
				GeneratePools();
				InertiaDistribution();
				ProposalDynamics();
				FindMaximumSentments();
				
				for(int K = Ki; K <= Kf; K++)
					{
						AgentsDistributionExtreme(K);
						CastVotesSqrtTokens();
						GetMostVotedProposals();
						GetAwardedProposals();
						welfare();
						Wext[K] += W;
						welfareStrategicAgents();
						WextStrategic[K] += W;
						welfareNonStrategicAgents();
						WextNonStrategic[K] += W;
						
						
						AgentsDistributionExtremeSkip(K);
						CastVotesSqrtTokens();
						GetMostVotedProposals();
						GetAwardedProposals();
						welfare();
						WextSkip[K] += W;
						welfareStrategicAgents();
						WextSkipStrategic[K] += W;
						welfareNonStrategicAgents();
						WextSkipNonStrategic[K] += W;
						
						AgentsDistributionEconomist(K);
						CastVotesSqrtTokens();
						GetMostVotedProposals();
						GetAwardedProposals();
						welfare();
						Weco[K] += W;
						welfareStrategicAgents();
						WecoStrategic[K] += W;
						welfareNonStrategicAgents();
						WecoNonStrategic[K] += W;
						
						AgentsDistributionEconomistExtreme(K);
						CastVotesSqrtTokens();
						GetMostVotedProposals();
						GetAwardedProposals();
						welfare();
						WecoExtreme[K] += W;
						welfareStrategicAgents();
						WecoExtremeStrategic[K] += W;
						welfareNonStrategicAgents();
						WecoExtremeNonStrategic[K] += W;
					}
				
				AgentsDistributionFullyExtreme();
				CastVotesSqrtTokens();
				GetMostVotedProposals();
				GetAwardedProposals();
				welfare();
				WextFully += W;
				welfareStrategicAgents();
				WextFullyStrategic += W;
				welfareNonStrategicAgents();
				WextFullyNonstrategic += W;
				
				AgentsDistributionFullyExtremeSkip();
				CastVotesSqrtTokens();
				GetMostVotedProposals();
				GetAwardedProposals();
				welfare();
				WextFullySkip += W;
				welfareStrategicAgents();
				WextFullySkipStrategic += W;
				welfareNonStrategicAgents();
				WextFullySkipNonstrategic += W;

			}
			
			WextFully = WextFully/backUpRate; 
			WextFullyStrategic = WextFullyStrategic/backUpRate;
			WextFullyNonstrategic = WextFullyNonstrategic/backUpRate;
			
			WextFullySkip = WextFullySkip/backUpRate;
			WextFullySkipStrategic = WextFullySkipStrategic/backUpRate;
			WextFullySkipNonstrategic = WextFullySkipNonstrategic/backUpRate;
			for(int K = Ki; K <= Kf; K++)
				{
					Wext[K] = Wext[K]/backUpRate;
					WextStrategic[K] = WextStrategic[K]/backUpRate;
					WextNonStrategic[K] = WextNonStrategic[K]/backUpRate;
					
					WextSkip[K] = WextSkip[K]/backUpRate;
					WextSkipStrategic[K] = WextSkipStrategic[K]/backUpRate;
					WextSkipNonStrategic[K] = WextSkipNonStrategic[K]/backUpRate;
					
					Weco[K] = Weco[K]/backUpRate;
					WecoStrategic[K] = WecoStrategic[K]/backUpRate;
					WecoNonStrategic[K] = WecoNonStrategic[K]/backUpRate;
					
					WecoExtreme[K] = WecoExtreme[K]/backUpRate;
					WecoExtremeStrategic[K] = WecoExtremeStrategic[K]/backUpRate;
					WecoExtremeNonStrategic[K] = WecoExtremeNonStrategic[K]/backUpRate;
				}
			
			//we write the results the average result of this samples
			fp = fopen(txt, "a");
			
			for(int K = Ki; K <= Kf; K++)
				fprintf (fp, "%Le\t", Wext[K]);
			for(int K = Ki; K <= Kf; K++)
				fprintf (fp, "%Le\t", WextSkip[K]);
			for(int K = Ki; K <= Kf; K++)
				fprintf (fp, "%Le\t", Weco[K]);
			for(int K = Ki; K <= Kf; K++)
				fprintf (fp, "%Le\t", WecoExtreme[K]);
			fprintf (fp, "%Le\t", WextFully);
			fprintf (fp, "%Le\t", WextFullySkip);
			
			
			for(int K = Ki; K <= Kf; K++)
				fprintf (fp, "%Le\t", WextStrategic[K]);
			for(int K = Ki; K <= Kf; K++)
				fprintf (fp, "%Le\t", WextSkipStrategic[K]);
			for(int K = Ki; K <= Kf; K++)
				fprintf (fp, "%Le\t", WecoStrategic[K]);
			for(int K = Ki; K <= Kf; K++)
				fprintf (fp, "%Le\t", WecoExtremeStrategic[K]);
			fprintf (fp, "%Le\t", WextFullyStrategic);
			fprintf (fp, "%Le\t", WextFullySkipStrategic);
			
			for(int K = Ki; K <= Kf; K++)
				fprintf (fp, "%Le\t", WextNonStrategic[K]);
			for(int K = Ki; K <= Kf; K++)
				fprintf (fp, "%Le\t", WextSkipNonStrategic[K]);
			for(int K = Ki; K <= Kf; K++)
				fprintf (fp, "%Le\t", WecoNonStrategic[K]);
			for(int K = Ki; K <= Kf; K++)
				fprintf (fp, "%Le\t", WecoExtremeNonStrategic[K]);
			fprintf (fp, "%Le\t", WextFullyNonstrategic);
			fprintf (fp, "%Le\t", WextFullySkipNonstrategic);
			
			fprintf (fp, "%d\t",  totalAmt);
			
			fprintf(fp, "\n");
			
			fclose(fp);
			
			//improving effective sample
			totalAmt+=backUpRate;
			
			f += dvariable;
		}
	}
}	

//function to sum the values at a given column of a txt file
long double sumColumnK(const char* filename, int Ncolumns, int targetColumn) 
{
	FILE* file = fopen(filename, "r");
	if (file == NULL)
	{
		printf("Error opening file: %s\n", filename);
		return 0.0;
	}
	
	double combine = 0.0;
	int xp = 0;
	int column = 1;
	double value;
	while (fscanf(file, "%lf", &value) == 1) 
	{
		if (column == targetColumn && !isnan(value)) 
		{
			combine += value;
			xp++;
		}
		
		column++;
		if (column > Ncolumns) 
		{
			column = 1;
		}
	}
	fclose(file);
	
	return combine = combine/xp;
}

//here we combined the data on the txts files to get the average results of all the samples.
void Combine(long double variable, long double variablei, long double variablef, long double dvariable)
{
	system("clear");
	printf("Combining txt files...\n");
	
	int Npoints = (int)((variablef - variablei)/dvariable) + 1;
	
	//writing arquive
	sprintf(write, "CombinedData.txt");
	
	fp = fopen(write, "w");
	
	fprintf (fp, "f\t");
	
	for(int K = Ki; K <= Kf; K++)
		fprintf (fp, "Wext%d\t", K);
	for(int K = Ki; K <= Kf; K++)
		fprintf (fp, "WextSkip%d\t", K);
	for(int K = Ki; K <= Kf; K++)
		fprintf (fp, "Wco%d\t", K);
	for(int K = Ki; K <= Kf; K++)
		fprintf (fp, "WecoExtreme%d\t", K);
	fprintf (fp, "Wextfully\t");
	fprintf (fp, "WextfullySkip\t");
	
	for(int K = Ki; K <= Kf; K++)
		fprintf (fp, "WextStrategic%d\t", K);
	for(int K = Ki; K <= Kf; K++)
		fprintf (fp, "WextSkipStrategic%d\t", K);
	for(int K = Ki; K <= Kf; K++)
		fprintf (fp, "WecoStrategic%d\t", K);
	for(int K = Ki; K <= Kf; K++)
		fprintf (fp, "WecoExtremeStrategic%d\t", K);
	fprintf (fp, "WextfullyStrategic\t");
	fprintf (fp, "WextFullySkipStrategic\t");
	
	for(int K = Ki; K <= Kf; K++)
		fprintf (fp, "WextNonStrategic%d\t", K);
	for(int K = Ki; K <= Kf; K++)
		fprintf (fp, "WextSkipNonStrategic%d\t", K);
	for(int K = Ki; K <= Kf; K++)
		fprintf (fp, "WecoNonStrategic%d\t", K);
	for(int K = Ki; K <= Kf; K++)
		fprintf (fp, "WecoExtremeNonStrategic%d\t", K);
	fprintf (fp, "WextfullyNonstrategic\t");
	fprintf (fp, "WextfullySkipNonstrategic\t");
	
	fprintf(fp, "\n");	
	fclose(fp);
	
	//opening the files to read
	variable = variablei;
	for(int i=0; i <= Npoints; i++)
		{
			//find name of txt
			char txtname [200];
			sprintf(txtname, "%s", "Variable");
			char txtname2 [200];
			sprintf(txtname2, "(%.4Le)", variable);
			strcat(txtname, txtname2);
			char final [200] = ".txt";
			strcat(txtname, final);
			
			//writing data
			fp = fopen(write, "a");
			fprintf(fp, "%Le \t", variable);
			fclose(fp);
			
			//combining data
			int numberColumns = 12*Kf + 7;
			int initialColumnCombine = 1, finalColumnCombine = 12*Kf + 6;
			for(int column = initialColumnCombine; column <= finalColumnCombine; column++)
				{
					long double combine = sumColumnK(txtname, numberColumns, column);
					
					if(!isnan(combine))
						{
							//writing result averaged data
							fp = fopen(write, "a");
							fprintf(fp, "%Le \t", combine);
							fclose(fp);
						}
					
					else
						{
							//writing result averaged data
							fp = fopen(write, "a");
							fprintf(fp, "0.0 \t");
							fclose(fp);
							
						}
				}
			fp = fopen(write, "a");
			fprintf(fp, "\n");
			fclose(fp);
			
			variable +=dvariable;
		}
	printf("...Done!");

}

void SimulationMenu(long double variable, long double variablei, long double variablef, long double dvariable)
{
	//system("clear");
	printf("Hello, welcome to the simulator! \n\nTo simulate, insert 1. \nTo combine txt simulation files, insert 2. \nTo exit, insert anything else. \n\nInsert here:");
	int insert;
	scanf("%d", &insert);
	
	if(insert == 1)
		SIMULATION(variablei, variablef, dvariable);
	else if(insert == 2)
		Combine(variable, variablei, variablef, dvariable);
}

int main(void)
{ 
	//using time as seed for the random number generator     
    srand(time(NULL));
    	
	//starting!!
	printf("-Program started!\n");
	
	//executing the program!
	SimulationMenu(f, fi, ff, df);
	//remember to manually insert the changing
	//variable in the simulation function!!!

	//finished!!
	printf("-Program finished:)\n");
	
    //goodbye                
    return 0;

	//praised be God!!!
}
	
	
	
	