//bringing the tools
#include <stdlib.h>
#include <stdio.h>
#include <time.h>
#include <math.h>
#include <string.h>

//system parameters

//number of individuals
#define N 50

//number of experiments
#define Nxps 10000

//Number of experiments to write data in txt files
#define backUpRate (500) 

//Using several threads to run the simulation
#define Nstages (24)

//social Inertia
#define AverageInertiai (0.000)
#define AverageInertiaf (1.000)
#define dAverageInertia (0.010)

//proportional constant of the business model of inertia 
#define InertiaProp (3)

//probability of an indiviudal postint a rate in the platform
#define Pposting (0.6)

//parameter that controls how the number of people rating one proposal impacts the nonconformity inertia of the other users.
#define socialPressure (0.01)

//number of proposals available to vote
#define Nproposals (10)

//probability of an user skiping a proposal. If the user do not skip, it makes a grade from 1 to 10 to the proposal and vote on it.
#define Pskip (0.05)

//in plurality voting with quadratic costs, the agents choose only a few proposals to vote on.
#define NmaxProposalsToVote (3)

//average Total Funding from rounds 1 to 4.
//(ignoring round 4 beta who had a smaller total funding money).
#define fundingMoney (1137500)

//balance distribution parameters
#define yoL (0.06)
#define xc (8.26)
#define w  (0.024)
#define AL  (0.38)

//funding request distribution parameters
#define yo (0.0000045)
#define A (0.000051)
#define xo (9000.0)
#define minFunding (1000)

//global System variables
long double Inertia[N], rating[N][Nproposals], proposalRating[Nproposals];
int NumberRatings[Nproposals],  IndividualVotes[Nproposals];
long double money[N], funding[Nproposals], proposalVotes[Nproposals], Impact[Nproposals];
long double totalSQRTmoney, totalMoney;
int MostVotedProposals[Nproposals], NfundedProposals;
int fundedProposals[Nproposals];
long double W, WsqrtSum, WoneCoinSum, WoneWalletSum, WpluralitySum, WLinearpluralitySum;
long double AverageInertia, moneyMin, moneyMax;
int favoriteProposals[N][Nproposals], proposalsToVote[N][Nproposals];
int stage, stagesNeeded;

//random numbers generator parameters
static unsigned int ux, uy;
static float h_scale;

//arquive variables
char txt[200];
FILE *fp;
FILE* read; 
char character;
char write[300];

//random number generator function
long double xor64()
{
	h_scale = (float) (1.0/pow(2.0, 32.0));
	unsigned int b = (ux^(ux<<8));
	ux = uy;
	uy = (uy^(uy>>22))^(b^(b>>9));
	return ((float) uy) * h_scale;
}

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

//lognormal distribution formula
long double logNormal(long double x)
{
	long double y = yoL;
	
	y += AL*exp(-pow(log(x/xc), 2)/(2*w*w))/(w*x*sqrt(2*M_PI));
	
	return y;
}

//generator of random numbers following a log normal distribution using Inverse Transform Sampling.
long double randomLogNormal()
{
	long double randomNumber = xor64();
	
	long double step = 0.01;
	long double logNormalRN = 2*step;
	
	long double sum = (logNormal(logNormalRN-step) + logNormal(logNormalRN));
	
	while(sum*step*0.5 < randomNumber)
	{
		logNormalRN += step;
		
		sum += (logNormal(logNormalRN-step) + logNormal(logNormalRN));
	}
	
	long double answer = logNormalRN - step;
		
	return answer;
}

void Money_Distribution()
{	
	totalSQRTmoney = 0.0;
	totalMoney = 0.0;
	for(int i=0; i <N; i++)
	{
		//how much balance/tokens each agent has
		money[i] = pow(10, randomLogNormal());
		
		totalSQRTmoney += sqrt(money[i]);
		totalMoney += money[i];
	}
}

//cumulative of the exponential function
long double ExponentialCumulative(long double x)
{
	return yo*x - A*xo*exp(-x/xo) + A*xo;
}

//generator of random numbers following a exponential distribution using Inverse Transform Sampling.
long double randomExponential()
{
	long double randomNumber = xor64();
	
	long double expoRN = 0;
	long double dExpoRn = 0.1;
	while(ExponentialCumulative(expoRN) < randomNumber)
		expoRN += dExpoRn;
	
	return minFunding + expoRN - dExpoRn;
}

//requested proposal fundings
void RequestFundingDistribution()
{
	for(int proposal = 0; proposal < Nproposals; proposal++)
		funding[proposal] = randomExponential();
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

//gives a random rating between 1 and 5 stars
long double RandomStar(long double randomNumber)
{
	return 4*randomNumber+1;
}

//convert star from 1 to 5 into preference into 1 to 10
long double StarToPreference(long double star)
{
	//linear relationship
	return round((9*star-5)/4);
}

//calculate the weight of a grade. More extreme grades cost more.
//maps grades {1, 2, ,3 ,4 5, 6, 7, 8, 9, 10} to weights {5. 4, 3, 2, 1, 1, 2, 3, 4, 5}.
long double gradeWeight(long double grade)
{
	if(grade <= 5)
		return 6 -grade;
	else
		return grade - 5;
}

//maps stars from 1 to 5 into a normalized version from 0 to 1
long double starTo01(long double star)
{
	return (star-1)/4;
}

void ProposalDynamics()
{
	for(int proposal = 0; proposal < Nproposals; proposal++)
	{
		//number of people who voted on the proposal
		IndividualVotes[proposal] = 0;
		
		//determining the impact of each proposal on the community on a scale from 1 to 5
		Impact[proposal] = RandomStar(xor64());
		
		NumberRatings[proposal] = 0;
		proposalRating[proposal] = 0.0;
		
		int i = 0;
		while(NumberRatings[proposal] == 0 && i < N)
		{
			if(xor64() < Pskip)
				rating[i][proposal] = 0;
			
			else
			{
				IndividualVotes[proposal]++;
				
				rating[i][proposal] = RandomStar(xor64());
				
				if(xor64() < Pposting)
				{
					proposalRating[proposal] += round(rating[i][proposal]);
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
			if(xor64() < Pskip)
				rating[i][proposal] = 0;
			
			else
			{
				IndividualVotes[proposal]++;
				
				//agent independent opinion
				rating[i][proposal] = RandomStar(xor64());
								
				//average past majority rating
				long double averageOpinion = proposalRating[proposal]/(NumberRatings[proposal]);
				
				//social validation on inertia
				long double socialValidation = 1 - Inertia[i]*pow(1-socialPressure, NumberRatings[proposal]);

				//social validation effect
				if(xor64() < socialValidation)
					rating[i][proposal] += socialValidation*(averageOpinion - rating[i][proposal]); 
				
				//nonconformism
				else
				{
					rating[i][proposal] -= (1 - socialValidation)/(averageOpinion -  rating[i][proposal]);
					
					if(rating[i][proposal] < 1)
						rating[i][proposal] = 1;
					
					else if (rating[i][proposal] > 5)
						rating[i][proposal] = 5;
				}
					
				if(xor64() < Pposting)
				{
					proposalRating[proposal] += round(rating[i][proposal]);
					NumberRatings[proposal]++;
				}
			}

			i++;
		}
		
		//writing the final average rating values
		proposalRating[proposal] = proposalRating[proposal]/NumberRatings[proposal];
	}
}

void CastVotesSqrtTokens()
{
	for(int proposal = 0; proposal < Nproposals; proposal++)
	{
		proposalVotes[proposal] = 0.0;
	}
	
	//calculating the average grade of each proposal
	for(int i = 0; i < N; i ++)
	{
		for(int proposal = 0; proposal < Nproposals; proposal++)
		{
			//if i has not skiped the proposal
			if(rating[i][proposal] !=0)
			{
				//grade between 1 and 10
				int grade = StarToPreference(rating[i][proposal]);
				
				proposalVotes[proposal] += grade*sqrt(money[i]);			
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
	}
	
	//calculating the average grade of each proposal
	for(int i = 0; i < N; i ++)
	{		
		for(int proposal = 0; proposal < Nproposals; proposal++)
		{
			//if i has not skiped the proposal
			if(rating[i][proposal] !=0)
			{
				//grade between 1 and 10
				int grade = StarToPreference(rating[i][proposal]);
				
				proposalVotes[proposal] += grade*money[i];			
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
	}
	
	//calculating the average grade of each proposal
	for(int i = 0; i < N; i ++)
	{		
		for(int proposal = 0; proposal < Nproposals; proposal++)
		{
			//if i has not skiped the proposal
			if(rating[i][proposal] !=0)
			{
				//grade between 1 and 10
				int grade = StarToPreference(rating[i][proposal]);
				
				proposalVotes[proposal] += grade;			
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
		while(proposalIndex < NmaxProposalsToVote && proposalIndex < Nproposals)
		{
			if(StarToPreference(rating[i][favoriteProposals[i][proposalIndex]]) >= 7)
				proposalsToVote[i][proposalIndex] = favoriteProposals[i][proposalIndex];
			
			proposalIndex++;
		}
	}
}

void CastVotesPluralityVoting()
{
	GetFavoriteProposals();
	DecideWichProjetcsToVote();
	
	for(int proposal = 0; proposal < Nproposals; proposal++)
	{
		proposalVotes[proposal] = 0.0;
	}
	
	for(int i = 0; i < N; i ++)
	{
		long double totalGradeWeight = 0;
		
		int proposalIndex = 0;
		while(proposalIndex < Nproposals && proposalsToVote[i][proposalIndex] != -1)
		{
			int proposal = proposalsToVote[i][proposalIndex];
			totalGradeWeight += gradeWeight(StarToPreference(rating[i][proposal]));
			proposalIndex++;
		}
				
		if(totalGradeWeight)
		{
			int proposalIndex = 0;
			while(proposalIndex < Nproposals && proposalsToVote[i][proposalIndex] != -1)
			{
				int proposal = proposalsToVote[i][proposalIndex];
				
				long double grade = StarToPreference(rating[i][proposal]);
				long double weightGrade = gradeWeight(grade);
				
				proposalVotes[proposal] += sqrt(weightGrade*money[i]/totalGradeWeight);
				
				proposalIndex++;
			}
		}
	}
}

void CastVotesLinearPluralityVoting()
{
	GetFavoriteProposals();
	DecideWichProjetcsToVote();
	
	for(int proposal = 0; proposal < Nproposals; proposal++)
	{
		proposalVotes[proposal] = 0.0;
	}
	
	for(int i = 0; i < N; i ++)
	{
		long double totalGradeWeight = 0;
		
		int proposalIndex = 0;
		while(proposalIndex < Nproposals && proposalsToVote[i][proposalIndex] != -1)
		{
			int proposal = proposalsToVote[i][proposalIndex];
			totalGradeWeight += gradeWeight(StarToPreference(rating[i][proposal]));
			proposalIndex++;
		}
		
		if(totalGradeWeight)
		{
			int proposalIndex = 0;
			while(proposalIndex < Nproposals && proposalsToVote[i][proposalIndex] != -1)
			{
				int proposal = proposalsToVote[i][proposalIndex];
				
				long double grade = StarToPreference(rating[i][proposal]);
				long double weightGrade = gradeWeight(grade);
				
				proposalVotes[proposal] += (weightGrade*money[i]/totalGradeWeight);
				
				proposalIndex++;
			}
		}
	}
}

void GetMostVotedProposals()
{
	//we will make a list with the number of the proposal, going from the most voted proosal to the less voted.
	//first, just create the list 
	for(int proposal = 0; proposal < Nproposals; proposal++)
	{
		MostVotedProposals[proposal] = proposal;
	}
	
	//now, we make a copy of the proposalvotes vector. We don't want to mess the original vector.
	long double copyVotes[Nproposals];
	for(int proposal = 0; proposal < Nproposals; proposal++)
	{
		copyVotes[proposal] = proposalVotes[proposal];
	}

	//now, we will order the copy votes vector and the index (the proposals) using bubble sort. The goal is that the first entry of the MostVotedProposals will say the proposal number with most votes, and so on.
	for(int i = 0; i < Nproposals - 1; i ++)
	{
		for(int j = 0; j < Nproposals - 1 - i; j++)
		{
			if(copyVotes[j] < copyVotes[j+1])
			{
				long double store = copyVotes[j];
				copyVotes[j] = copyVotes[j+1];
				copyVotes[j+1] = store;
				
				int storeIndex = MostVotedProposals[j];
				MostVotedProposals[j] = MostVotedProposals[j+1];
				MostVotedProposals[j+1] = storeIndex;
			}
		}
	}
}

void GetAwardedProposals()
{
	//first, we need to determine the eligible proposals. Eligible porposals must have received votes from at least 1% of the voters.	
	//the project also needs a minimum average grad of 6.5 and must fit the pools remaining budget after higher voter proposals are funded.
	long double MoneyAvailableToFund = fundingMoney;
	NfundedProposals = 0;
	
	//from the most voted proposal to the less voted proposal
	for(int j = 0; j < Nproposals; j++)
	{
		int proposal = MostVotedProposals[j];
		
		//check if proposal is eligible
		if(proposalVotes[proposal] >= 6.5 && IndividualVotes[proposal] >= 0.01*N)
		{
			//if there is suficient funding money to fund the proposal
			if(funding[proposal] <= MoneyAvailableToFund)
			{
				fundedProposals[NfundedProposals] = proposal;
				NfundedProposals++;
				MoneyAvailableToFund = MoneyAvailableToFund - funding[proposal];
			}
		}
	}
	
	//printf("ffff %d \n", NfundedProposals);
}

void GetPluralityAwardedProposals()
{
	//In plurality voring, each individual vote just on a few proposals. Therefore, we only require an average grade >= 6.5 and that the proposal must fit the pools remaining budget after higher voter proposals are funded.
	
	long double MoneyAvailableToFund = fundingMoney;
	NfundedProposals = 0;
	
	//from the most voted proposal to the less voted proposal
	for(int j = 0; j < Nproposals; j++)
	{
		int proposal = MostVotedProposals[j];
		
		//calculating average grade of the proposal
		long double grade = 0.0;
		int graders = 0;
		for(int i = 0; i < N; i ++)
		{
			if(rating[i][proposal])
			{
				grade += StarToPreference(rating[i][proposal]);
				graders++;
			}
		}
		grade = grade/graders;
		
		//check proposal is eligible
		if(grade >= 6.5)
		{
			//if there is suficient funding money to fund the proposal
			if(funding[proposal] <= MoneyAvailableToFund)
			{
				fundedProposals[NfundedProposals] = proposal;
				NfundedProposals++;
				MoneyAvailableToFund = MoneyAvailableToFund - funding[proposal];
			}
		}
	}
}

void welfare()
{
	long double totalGrade[N];
	for(int i = 0; i < N; i++)
	{
		totalGrade[i] = 0.0;
		for(int proposal = 0; proposal < Nproposals; proposal++)
		{
			//if not skipped the proposal
			if(rating[i][proposal])
				totalGrade[i] += StarToPreference(rating[i][proposal]);
		}
	}
	
	W = 1.0;
	long double totalNumberVotersOnProposals = 0.0;
	for(int j = 0; j < NfundedProposals; j++)
	{
		int proposal = fundedProposals[j];
		
		//for each funded proposal, we calculate the welfare of this proposal on the population.
		for(int i = 0; i < N; i ++)
		{
			//we assume if i skiped the proposal, he/she is indiferent to the proposal, and has no welfare to that proposal.
			if(rating[i][proposal])
			{
				W *= sqrt(StarToPreference(rating[i][proposal])*money[i]/(totalGrade[i]*totalMoney));  
				totalNumberVotersOnProposals++;
			}
		}
	}
	
	if(NfundedProposals > 0)
	{
		W = pow(W, 1.0/(totalNumberVotersOnProposals));
	}
	
	else
	{
		W = 0.0;
	}
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
		AverageInertia = POINT.INITIAL;
		for(int step = 0; step <= (POINT.FINAL-POINT.INITIAL)/dvariable; step++)
		{
			//arquive
			sprintf(txt, "Variable(%.4Le).txt", AverageInertia);
			fp = fopen(txt, "a");
			
			//find effective sample
			int totalAmt = effectiveAmt(AverageInertia);
				
			//initializing the means
			WsqrtSum = 0.0;
			WoneCoinSum = 0.0;
			WoneWalletSum = 0.0;
			WpluralitySum = 0.0;
			WLinearpluralitySum = 0.0;
			
			for(int xp = 0; xp < backUpRate; xp++)
			{
				Money_Distribution();
				RequestFundingDistribution();
				InertiaDistribution();
				ProposalDynamics();
				
				CastVotesSqrtTokens();
				GetMostVotedProposals();
				GetAwardedProposals();
				welfare();
				WsqrtSum += W;
				
				CastVotesOneCoinOneVote();
				GetMostVotedProposals();
				GetAwardedProposals();
				welfare();
				WoneCoinSum += W;
				
				CastVotesOneWalletOneVote();
				GetMostVotedProposals();
				GetAwardedProposals();
				welfare();
				WoneWalletSum += W;
				
				CastVotesPluralityVoting();
				GetMostVotedProposals();
				GetPluralityAwardedProposals();
				welfare();
				WpluralitySum += W;
				
				CastVotesLinearPluralityVoting();
				GetMostVotedProposals();
				GetPluralityAwardedProposals();
				welfare();
				WLinearpluralitySum += W;

			}
			
			WsqrtSum = WsqrtSum/backUpRate;
			WoneCoinSum = WoneCoinSum/backUpRate;
			WoneWalletSum = WoneWalletSum/backUpRate;
			WpluralitySum = WpluralitySum/backUpRate;
			WLinearpluralitySum = WLinearpluralitySum/backUpRate;
			
			//we write the results the average result of this samples
			fp = fopen(txt, "a");
			
			fprintf (fp, "%Le\t", WsqrtSum);
			fprintf (fp, "%Le\t", WoneCoinSum);
			fprintf (fp, "%Le\t", WoneWalletSum);
			fprintf (fp, "%Le\t", WpluralitySum);
			fprintf (fp, "%Le\t", WLinearpluralitySum);
			fprintf (fp, "%d\t",  totalAmt);
			
			fprintf(fp, "\n");
			
			fclose(fp);
			
			//improving effective sample
			totalAmt+=backUpRate;
			
			AverageInertia += dvariable;
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
		if (column == targetColumn) 
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
	
	fprintf (fp, "I\t");
	fprintf (fp, "Wsqrt\t");
	fprintf (fp, "WoneCoin\t");
	fprintf (fp, "WoneWallet\t");
	fprintf (fp, "Wplurality\t");
	fprintf (fp, "WLinearPlurality\t");
	fprintf(fp, "\n");
	
	fclose(fp);
	
	//opening the files to read
	variable = variablei;
	for(int i=1; i <= Npoints; i++)
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
		int numberColumns = 6;
		int initialColumnCombine = 1, finalColumnCombine = 5;
		for(int column = initialColumnCombine; column <= finalColumnCombine; column++)
		{
			long double combine = sumColumnK(txtname, numberColumns, column);
			
			//writing result averaged data
			fp = fopen(write, "a");
			fprintf(fp, "%Le \t", combine);
			fclose(fp);
		}
		fp = fopen(write, "a");
		fprintf(fp, "\n");
		fclose(fp);
		
		variable +=dvariable;
	}
	printf("...Done!");
}

void SimulationMenu(float variable, float variablei, float variablef, float dvariable)
{
	system("clear");
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
	
	//preparing random numbers generation
	long double scale = 1.0/pow(2.0, 32.0) + 1;
	scale = 1.0/scale;
	srand(time(0));
	for (int v = 0; v < 100; ++v) ux = rand();
	for (int v = 0; v < 100; ++v) uy = rand();

	//executing the program!
	SimulationMenu(AverageInertia, AverageInertiai, AverageInertiaf, dAverageInertia);
	//remember to manually insert the changing
	//variable in the simulation function!!!

	//finished!!
	printf("-Program finished:)\n");
	
    //goodbye                
    return 0;

	//praised be God!!!
}
	
	
	
	