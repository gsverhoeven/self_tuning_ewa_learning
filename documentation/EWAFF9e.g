/* 

Program:		EWALite
Author:		Chong Juin Kuan
Date:			January 10, 2002
Version:		9

Description:	Fat-free EWA


20) added one more column to inpar9c.dat so that data sets from Nagel and Sovik can be incorporated

January 10, 2002
19) Adopted from the thinking step model TFLFFa8.g where the thinking model and 3 data sets are removed 
Note that in EWAFFa8e.g and previous version but not later, first period in QRE uses initial attraction values 
as in the case for other models. In this version, both options are available.
Note also that in EWAFFa8f.g, the Fatfree model has a similarity-adjusted phi specification.
McNemar Test in EWAFFa7g.g is taken out

October 01, 2001
18) Alternative way to for initial attraction

February 3, 2001
16) Table 3 Whole game prediction 
17) Table 4 for Economic Value

January 21, 2001
15) New Output for 3 Tables and 1 Plot

January 12, 2001
13) Traveler's Dilemma games added
14) Support for pot games = 2

January 04, 2001
12) Pot (Pond) games added

December 28, 2000
10) pBC put in with pEWA having one additional parameter to be estimated
11) cross-sequence validation

December 09, 2000

8) Reestimate model pooling all games into one data set.
9) Modify to allow for different lambda for different games (December 14, 2000)

Sept 23, 2000
1) Phi is (moving average(t with time window = support of the equilibrium strateies) - total(t))
2) delta = (phi[k,t]/spp[Gi])
3) kappa uses empirical freq 	pr0 = sumc(choice[.,1:t]')./(t);
4) initial attraction is first period empirical freq + spp[Gi]/ns;

Oct 16, 2000
5) in place of 2) above delta = sqrt(average time being smart) smart being defined as better response

November 11, 2000

6) initialize n(0) = support
7) reestimate adaptive EWA with burn-in initial attraction similar to fatfree and use 6)

Note on adaptive EWA: For cdg and mag, only one set of initial attraction is used for all groups.
Whereas in fatfree each group has each own burn-in initial attraction. Therefore, an adaptive EWA
that uses the same burn-in as fatfree is not a special case of adaptive EWA that uses 
one set of A0 estimates for all groups. In addition, the difference in initial attractions
for adaptive EWA was constrained within a range. In fatfree, it is not; again using burn-in 
would not result in a special case.

Games
-----

1. Continental Divide
2. Median Action 
3. Mixed Strategies (4 Games)
4. Amaldoss's Asymmetric Patent Race (October 24, 2000)
5. p-Beauty constest (2 Games)
6. Pot (Pond) games (7 games)
7. Traveler's dilemma (5 games excluding R=10 because 1 subject unmatched)

*/

new; library maxlik; maxset; format /rd 4,4; outwidth 256;
_max_CovPar = 0; _max_algorithm = 2; 

_max_MaxIters = 5;		/* Input: Number of Iterations */ 
ngame = 28;				/* Input: Total Number of Game Sessions studied */
evsim = 1000;			/* economic value simulation */

u_lam = 20;			/* upper bound for lambda */
max_iter = 20;		/* max iterations for fixed point search */
min_diff = 0.0001;	/* min convergenece for fixed point search */

/* Time Weighted Initial Values */
iphi = 0.5; idelt = 0.5; ikappa = 0.5; initial = 1;

/* Initialization: searching for best initial values */
iv = 0; 	/* 9 number of combination to try */

llam = zeros(3,1); llam[1] = 1.00; llam[2] = 8.00; llam[3] = 16.00;
ltau = zeros(3,1); ltau[1] = 0.25; ltau[2] = 0.75; ltau[3] = 1.5;

gname = zeros(ngame,1); 

/* Pure strategy equilibrium */
gname[1] = "cdg";	gname[2] = "mag"; gname[3] = "pBCex"; gname[4] = "pBCix";	
gname[5] = "td5"; gname[6] = "td20"; gname[7] = "td25"; gname[8] = "td50"; 
gname[9] = "td80";

/* Mixed strategies equilibrium */
gname[10] = "mix1"; gname[11] = "mix2"; gname[12] = "mix3"; gname[13] = "mix4"; 
gname[14] = "pstrg"; gname[15] = "pweak"; gname[16] = "potm3"; gname[17] = "potm6"; 
gname[18] = "potm9"; gname[19] = "potc3"; gname[20] = "potc6"; gname[21] = "potc18a"; 	
gname[22] = "potc18b"; 	

gname[23] = "Uc50a"; gname[24] = "Uc50b"; 
gname[25] = "Svk1"; gname[26] = "Svk2"; gname[27] = "Svk3"; gname[28] = "Svk4";

SFile = "c:/gauss/input/inpar9c.dat"; load indata[ngame,11]=^SFile;

t0	= indata[.,1];	/* Calibration period */
tv0	= indata[.,2];	/* Validation period */
n0	= indata[.,3];	/* Calibration subjects */
nv0	= indata[.,4];	/* Validation subjects */
ns0	= indata[.,5];	/* Number of strategies */
ons0	= indata[.,6];	/* Number of scenarios */
tns0	= indata[.,7];	/* Number of strategies */
ngrp0	= indata[.,8];	/* Number of groups */
nsj0	= indata[.,9];	/* Number of subjects in a group */
mvavg	= indata[.,10];	/* Mv Avg periods for fatfree phi */
spp	= indata[.,11];	/* supports for fatfree parameters */

t = t0[1];	tv = tv0[1]; n = n0[1]; nv = nv0[1]; 
ns = ns0[1]; ons = ons0[1]; ngrp = ngrp0[1]; nsj = nsj0[1]; tns = tns0[1];

/* declare global variables */
choice0 ={}; payoff0 ={}; oppid = {}; others = {}; wpbc = {}; Gi = {}; 
pay = {}; dslope = {}; nwin = {}; twidth = {}; winner = {};
pr_ffr = {}; pr_ewa = {}; ffpred = {}; ewapred = {}; empred = {}; 
phi ={}; uphi = {}; kappa = {}; delta = {}; lambda = {}; nt = {}; att0 = {};
Ivldn = {}; delt = {}; othmax = {}; CFILE = {}; rndev = {};
trpr_ffr = {}; trpr_ewa = {}; trpr_em = {}; EFile = {};
DFILE = {}; BFILE = {}; PFILE = {}; evcall = 0;  idMPAR ={};	
frslt = {}; terslt = {}; erslt = {}; rslt = {}; tdslp = {}; MPAR = {};
pr_ffl = {}; pr_tfl = {}; msd = {}; dmsd = {}; ns1 = {}; ons1 = {}; tns1 = {};
max_ns = {}; max_ons = {}; begpay = {}; nsavb = {}; signal = {}; tatt0 = {}; max_tns = {};

MSDFile = "c:/gauss/input/msdb5.out"; output file=^MSDFile reset; 

RFile = "c:/gauss/input/pool.out"; output file=^RFile reset; 
cls; GFile = "c:/gauss/input/var.out"; output file=^GFile reset; output off; 

bgame = 1; rndseed 789987; call readdata;

idMPAR = zeros(3,ngame);

model = 0; do while model <= 6; 
	
/* initializing the opponents' choice probability for patent race */
othmax = (1/ns0[14]).*ones(n0[14]+nv0[14],t0[14]*ns0[14]); 
MPAR = "q" $+ ftos(1,"%*.*lf",1,0) $+ ftos(0,"%*.*lf",1,0) $+ ftos(15,"%*.*lf",1,0) $+ ftos(14,"%*.*lf",1,0); save ^MPAR = othmax;
MPAR = "q" $+ ftos(model,"%*.*lf",1,0) $+ ftos(0,"%*.*lf",1,0) $+ ftos(15,"%*.*lf",1,0) $+ ftos(14,"%*.*lf",1,0); save ^MPAR = othmax;
MPAR = "q" $+ ftos(model,"%*.*lf",1,0) $+ ftos(1,"%*.*lf",1,0) $+ ftos(15,"%*.*lf",1,0) $+ ftos(14,"%*.*lf",1,0); save ^MPAR = othmax;
MPAR = "q" $+ ftos(model,"%*.*lf",1,0) $+ ftos(2,"%*.*lf",1,0) $+ ftos(15,"%*.*lf",1,0) $+ ftos(14,"%*.*lf",1,0); save ^MPAR = othmax;

othmax = (1/ns0[15]).*ones(n0[15]+nv0[15],t0[15]*ns0[15]); 
MPAR = "q" $+ ftos(1,"%*.*lf",1,0) $+ ftos(0,"%*.*lf",1,0) $+ ftos(15,"%*.*lf",1,0) $+ ftos(15,"%*.*lf",1,0); save ^MPAR = othmax;
MPAR = "q" $+ ftos(model,"%*.*lf",1,0) $+ ftos(0,"%*.*lf",1,0) $+ ftos(15,"%*.*lf",1,0) $+ ftos(15,"%*.*lf",1,0); save ^MPAR = othmax;
MPAR = "q" $+ ftos(model,"%*.*lf",1,0) $+ ftos(1,"%*.*lf",1,0) $+ ftos(15,"%*.*lf",1,0) $+ ftos(15,"%*.*lf",1,0); save ^MPAR = othmax;
MPAR = "q" $+ ftos(model,"%*.*lf",1,0) $+ ftos(2,"%*.*lf",1,0) $+ ftos(15,"%*.*lf",1,0) $+ ftos(15,"%*.*lf",1,0); save ^MPAR = othmax;

if model == 0; x2 = zeros(1,1); else; x2 = zeros(5,1); endif; /* Number of parameters: lambda, phi, delta, kappa, N(0) */

j = 31; do while j <= 32;

		if j > 22;
			othmax = (1/ns0[14]).*ones(n0[14]+nv0[14],t0[14]*ns0[14]); 
			MPAR = "q" $+ ftos(model,"%*.*lf",1,0) $+ ftos(1,"%*.*lf",1,0) $+ ftos(j,"%*.*lf",1,0) $+ ftos(14,"%*.*lf",1,0); save ^MPAR = othmax;
			othmax = (1/ns0[15]).*ones(n0[15]+nv0[15],t0[15]*ns0[15]); 
			MPAR = "q" $+ ftos(model,"%*.*lf",1,0) $+ ftos(1,"%*.*lf",1,0) $+ ftos(j,"%*.*lf",1,0) $+ ftos(15,"%*.*lf",1,0); save ^MPAR = othmax;
		endif;

	if model == 0; bp = 1; np = 2; 
	elseif model == 6; bp = 1; np = 2; 		/* EWAFFA8c.g and before, QRE has bp = 5 */
	else; bp = 5; np = 6; endif; /* Number of parameters: lambda, phi, delta, kappa, N(0) */

	bgame = j; /* first game session to be included in an estimation ngame define the last */

	/* pool = 0 if no pooling across games, = 1 if pooling and = 2 if pooling all other games except the one */
	if j == 1; 		TPAR = "1cdg"; ngame = j; pool = 0;
	elseif j == 2; 	TPAR = "1mag"; ngame = j; pool = 0;
	elseif j == 3; 	TPAR = "1pBC"; j = 4;	ngame = j; pool = 0;
	elseif j == 5; 	TPAR = "1TrD"; j = 9;	ngame = j; pool = 0;
	elseif j == 10; 	TPAR = "1mix"; j = 13;	ngame = j; pool = 0;
	elseif j == 14; 	TPAR = "1pat"; j = 15;	ngame = j; pool = 0;
	elseif j == 16; 	TPAR = "1pot"; j = 22;	ngame = j; pool = 0;
	elseif j == 23; 	bgame = 1; ngame = 22; np = np + 6; TPAR = "pool"; pool = 1;
	elseif j == 24; 	bgame = 1; ngame = 22; b1game = 1; 	n1game = 1;  TPAR = "ncdg"; pool = 2;
	elseif j == 25; 	bgame = 1; ngame = 22; b1game = 2; 	n1game = 2;  TPAR = "nmag"; pool = 2;
	elseif j == 26; 	bgame = 1; ngame = 22; b1game = 3; 	n1game = 4; TPAR = "npBC"; pool = 2;
	elseif j == 27; 	bgame = 1; ngame = 22; b1game = 5; 	n1game = 9; TPAR = "nTrD"; pool = 2;
	elseif j == 28;	bgame = 1; ngame = 22; b1game = 10; n1game = 13; TPAR = "nmix"; pool = 2; 
	elseif j == 29; 	bgame = 1; ngame = 22; b1game = 14; n1game = 15; TPAR = "npat"; pool = 2;
	elseif j == 30; 	bgame = 1; ngame = 22; b1game = 16; n1game = 22; TPAR = "npot"; pool = 2;
	elseif j == 31; 	TPAR = "1Nag"; bgame = 23; ngame = 24; pool = 0;
	elseif j == 32; 	TPAR = "1Svk"; bgame = 25; ngame = 28; pool = 0;

	endif;
	
	/* specify the calibration sample */
	nobs = n0[bgame:ngame]'*t0[bgame:ngame]; 
	if pool == 2; nobs = (n0[bgame:ngame] + nv0[bgame:ngame])'*(t0[bgame:ngame]+tv0[bgame:ngame]) - (n0[b1game:n1game]+nv0[b1game:n1game])'*(t0[b1game:n1game]+tv0[b1game:n1game]); endif;
	d = ones(nobs,1);
	saved(d,"data",0);		/* save d as a dummay data set of "pool" */

	x0 = 0.6.*rndu(np,1); x0[np] = 2;

	if j /= 26; x0[bp] = 0.11/1.7; endif; /* dslope for pBC */

	_max_Active = ones(np,1);		/* 1 indicates free parameter; 0 indicates fixed parameter */
	output off; vldn = 0;

	if model == 0; UPAR = "ff" $+ TPAR; 
	elseif model == 1; _max_Active[2:3] = zeros(2,1); x0[2] = -1e+70; x0[3] = 1e+70; UPAR = "bb" $+ TPAR;		
	elseif model == 2; _max_Active[2:3] = zeros(2,1); x0[2] = 1e+70; x0[3] = 1e+70; UPAR = "cr0" $+ TPAR;
	elseif model == 3; _max_Active[2:3] = zeros(2,1); x0[2] = 1e+70; x0[3] = -1e+70; UPAR = "cr1" $+ TPAR;
	elseif model == 4; UPAR = "ewa" $+ TPAR; 
	elseif model == 5; _max_Active[1:3] = zeros(3,1); x0[1:3] = zeros(3,1);	UPAR = "rl" $+ TPAR;	
	elseif model == 6; _max_Active[1:bp] = zeros(bp,1); x0[1:bp] = zeros(bp,1);	UPAR = "qr" $+ TPAR;	
	endif;

	/* dslope for pBC */
	_max_Active[bp] = 0;
	if (j == 4) or (j > 26) or ((j>22)and(j<26));
		_max_Active[bp] = 1;
	endif;
	if model >= 5; _max_Active[bp] = 0; endif;

/*
if model == 6; loadm x1 = ^UPAR; x0[bp] = x1[5]; x0[bp] = x1[5]; x0[bp+1:np] = x1[6:(6+np-bp-1)];
else; loadm x0 = ^UPAR; endif;
*/

	if iv == 0; loadm x0 = ^UPAR; endif;

/*
	if model == 0 or model == 5; if pool == 1; x0 = x2; endif; endif;		
	if j == 26; x0[bp] = tdslp; endif;
*/

	/* This is to generate the opponent choice probabilities for Patent Game */
	if j == 15;
		
		bgame = 14; ngame = 14; call tllk(x0,"data");
		MPAR = "q" $+ ftos(model,"%*.*lf",1,0) $+ ftos(1,"%*.*lf",1,0) $+ ftos(j,"%*.*lf",1,0) $+ ftos(14,"%*.*lf",1,0); save ^MPAR = othmax;  

		bgame = 15; ngame = 15; call tllk(x0,"data"); 
		MPAR = "q" $+ ftos(model,"%*.*lf",1,0) $+ ftos(1,"%*.*lf",1,0) $+ ftos(j,"%*.*lf",1,0) $+ ftos(15,"%*.*lf",1,0); save ^MPAR = othmax;

		bgame = 14; ngame = 14; call tllk(x0,"data");
		MPAR = "q" $+ ftos(model,"%*.*lf",1,0) $+ ftos(1,"%*.*lf",1,0) $+ ftos(j,"%*.*lf",1,0) $+ ftos(14,"%*.*lf",1,0); save ^MPAR = othmax;  

		bgame = 14; ngame =15;
	endif;

	output file=^RFile on;
	print "____________________________________"; print;
	if model == 0; print " Estimation Result for Fatfree EWA ";
	elseif model == 1; print " Estimation Result for Belief-based ";
	elseif model == 2; print " Estimation Result for Reinforcement (kappa = 0)";
	elseif model == 3; print " Estimation Result for Reinforcement (kappa = 1)";
	elseif model == 4; print " Estimation Result for Adaptive EWA ";
	elseif model == 5; print " Estimation Result for REL ";
	elseif model == 6; print " Estimation Result for QRE ";
	endif;
	print "____________________________________"; print;

	maxf = sumc(tllk(x0,"data"))/nobs; 
	maxx = x0; print maxf;; print maxx'; 
	output file=^RFile on; print " Searching for best initial value .... "; print; output off;
	rndseed (12344321);          @ no chatter @
	ii = 1; do while ii <= iv;

		_max_MaxIters = 20;	/* Input: Number of Iterations */ 
		x0 = 0.6.*rndu(np,1); x0[np] = 2.*x0[np];
	
	if model == 0; UPAR = "ff" $+ TPAR; 
	elseif model == 1; _max_Active[2:3] = zeros(2,1); x0[2] = -1e+70; x0[3] = 1e+70; UPAR = "bb" $+ TPAR;		
	elseif model == 2; _max_Active[2:3] = zeros(2,1); x0[2] = 1e+70; x0[3] = 1e+70; UPAR = "cr0" $+ TPAR;
	elseif model == 3; _max_Active[2:3] = zeros(2,1); x0[2] = 1e+70; x0[3] = -1e+70; UPAR = "cr1" $+ TPAR;
	elseif model == 4; UPAR = "ewa" $+ TPAR; 
	elseif model == 5; _max_Active[1:3] = zeros(3,1); x0[1:3] = zeros(3,1);	UPAR = "rl" $+ TPAR;	
	elseif model == 6; _max_Active[1:bp] = zeros(bp,1); x0[1:bp] = zeros(bp,1);	UPAR = "qr" $+ TPAR;	
	endif;

		{x1,f,grad,cov,ret}= maxlik("data",0,&tllk,x0); 
		if f > maxf; maxf = f; maxx = x1; save ^UPAR = maxx; endif;		
		output file=^RFile on; print ii;; print maxf;; print f;; print x0'; output off;

		ii = ii+1;
	endo;		
	x0 = maxx;

/*
	_max_MaxIters = 50;	/* Input: Number of Iterations */ 
*/

	output file=^RFile on;
	{x1,f,grad,cov,ret}= maxlik("data",0,&tllk,x0); 
	save ^UPAR = x1;

	if pool < 1; 
			x2 = x2|x1[bp+1];
			if j == 4; x2[bp] = x1[bp]; endif;
	endif; 

	/* pBC slope from individual sessions */
	if j == 4; tdslp = x1[bp]; endif;

	lam = x1[bp+1:np]; 
	if model == 6; lam = (u_lam/(1+exp(x1[bp+1:np]))); endif;

	call MaxPrt(selif(x1,_max_Active),f,selif(grad,_max_Active),cov,ret);

	format /rd 6,4; 
	print; print " Log-likelihood = " f*nobs;
	print; print " Lambda = " lam';

	if model > 0 and model < 6; 
		print " Phi 	= " x1[1];
		print " Delta 	= " 1/(1+exp(x1[2]));
		print " Kappa 	= " 1/(1+exp(x1[3]));
		if model <= 4; 
			print " n0 	= " (1/(1+exp(x1[4])))*(1/(1 - x1[1]*(1 - 1/(1+exp(x1[3])))));
		else;	
			print " n0 	= " x1[4];
		endif;	
		print " slope for pBC = " x1[5];
	endif;

	/* include the hold-out sample for validation */
	nobs = (n0[bgame:ngame] + nv0[bgame:ngame])'*(t0[bgame:ngame]+tv0[bgame:ngame]); 
	d = ones(nobs,1); saved(d,"data",0);	/* save d as a dummay data set of "pool" */

	vldn = 1; call tllk(x1,"data"); 	/* validation */

	/* standard errors */
	GFile = "c:/gauss/input/var.out"; output file=^GFile on;
	print j;; print sqrt(diag(cov))'; output off;

	j = j+1;
endo;

if model > 0; terslt = terslt|erslt; erslt = {}; endif;

model = model + 1;

endo;

format /rd 8,4; GFile = "c:/gauss/input/all.out";
output file=^GFile reset; print (frslt|terslt)';
output off; stop;

/* Total Log-likehood: Summing LL across games for simultaneous estimations */

Proc tllk(x,data);

local ylog, ncount, xt, ev, npar;

ylog = zeros(nobs,1); ncount = 0;
npar = bp; xt = zeros(bp+1,1);  xt[1:bp] = x[1:bp]; 

/* going through all games */
Gi = bgame; do while Gi <= ngame; 

	/* Pooling across games */
	if pool == 2;		
		if vldn == 1; if Gi<=b1game; Gi = b1game; elseif Gi > n1game; goto LASTV; endif;
		else; if ((b1game<=Gi)AND(Gi<=n1game)); Gi = n1game+1; if Gi>ngame; goto LASTV; endif; endif; endif;
	endif;

	CFile = "ns" $+ ftos(Gi,"%*.*lf",1,0); load ns1 = ^CFILE; max_ns = maxc(ns1);
	CFile = "ons" $+ ftos(Gi,"%*.*lf",1,0); load ons1 = ^CFILE; max_ons = maxc(ons1);
	if j == 14 or j ==15; max_ons = max_ns; endif;   
	CFile = "begpay" $+ ftos(Gi,"%*.*lf",1,0);  load begpay = ^CFILE;

	CFile = "tns" $+ ftos(Gi,"%*.*lf",1,0); load tns1 = ^CFILE; max_tns = maxc(tns1);
	CFile = "nsavb" $+ ftos(Gi,"%*.*lf",1,0); load nsavb = ^CFILE;
	CFile = "signal" $+ ftos(Gi,"%*.*lf",1,0); load signal = ^CFILE;

	/* load the relevant parameter for a particular game or session */
	t = t0[Gi]; tv = tv0[Gi]; n = n0[Gi]; nv = nv0[Gi]; 
	ns = ns1[1]; ons = ons1[1]; ngrp = ngrp0[Gi]; nsj = nsj0[Gi];
	othmax = zeros(n+nv,t*max_ons); if ((Gi >= 14) and (Gi <= 15)); othmax = (1/ns).*ones(n+nv,t*ns); endif;

	/* initialize parameter matrices */

	delt = zeros(n+nv,t+tv); phi = zeros(n+nv,t+tv); uphi = zeros(n+nv,t+tv); kappa = zeros(n+nv,t+tv);
	delta = zeros(n+nv,t+tv); lambda = zeros(n+nv,t+tv);
	nt = 1.*ones(n+nv,t+tv); pr_ffr = zeros(n+nv,t+tv); 

	ffpred = zeros(max_ns,t+tv);	/* average predicted probability fatfree */
	empred = zeros(max_ns,t+tv);	/* Empirical Frequency */

	if vldn == 1;

		if pool < 1; 
			DFile = "c:/gauss/input/1" $+ gname[Gi] $+ ".dgn"; 
			BFile = "c:/gauss/input/1" $+ gname[Gi] $+ ".prb";
			PFile = "c:/gauss/input/1" $+ gname[Gi] $+ ".par";
			EFile = "c:/gauss/input/1" $+ gname[Gi] $+ ".ecv";
		elseif pool == 1; 
			DFile = "c:/gauss/input/p" $+ gname[Gi] $+ ".dgn"; 
			BFile = "c:/gauss/input/p" $+ gname[Gi] $+ ".prb";
			PFile = "c:/gauss/input/p" $+ gname[Gi] $+ ".par";
			EFile = "c:/gauss/input/p" $+ gname[Gi] $+ ".ecv";
		elseif pool == 2; 
			DFile = "c:/gauss/input/n" $+ gname[Gi] $+ ".dgn"; 
			BFile = "c:/gauss/input/n" $+ gname[Gi] $+ ".prb";
			PFile = "c:/gauss/input/n" $+ gname[Gi] $+ ".par";
			EFile = "c:/gauss/input/n" $+ gname[Gi] $+ ".ecv";
		endif;
		if model == 0; 
			output file=^BFile on; print;
			output file=^PFile on; print;
			output file=^DFile on; print;
		endif;

		output file=^DFile on; print;
		print "___________________________________ "; print;
		print DFile;
		print "___________________________________ ";

		Ivldn = ones(n+nv,t+tv); 	/* validate on whole game */
		if pool <= 1 or pool >= 3; Ivldn[1:n,1:t] = zeros(n,t); endif; Ivldn = vec(Ivldn');

		t = t0[Gi] + tv0[Gi]; n = n0[Gi] + nv0[Gi]; nv = 0; nsj = n/ngrp; rslt = {};
		trpr_ffr = zeros(max_ns,max_ns); trpr_em = zeros(max_ns,max_ns);  

		othmax = zeros(n,t*max_ons); if ((Gi >= 14) and (Gi <= 15)); othmax = (1/ns).*ones(n,t*ns); endif;
	
	endif;


	/* estimate on whole game */
	if pool > 1; t = t0[Gi] +tv0[Gi]; n = n0[Gi] +nv0[Gi]; nv = 0; nsj = n/ngrp; endif;

	/* load the right data */
	CFile = "payoff" $+ ftos(Gi,"%*.*lf",1,0); load payoff0 = ^CFILE; 
	CFile = "choice" $+ ftos(Gi,"%*.*lf",1,0); load choice0 = ^CFILE; choice0 = choice0[.,1:t];
	CFile = "others" $+ ftos(Gi,"%*.*lf",1,0); load others = ^CFILE;

	if Gi <= 4; 
		CFile = "rndev" $+ ftos(Gi,"%*.*lf",1,0);  loadm rndev = ^CFILE; 
	endif;
	if ((Gi == 3)OR(Gi == 4)); 
		CFile = "nwin" $+ ftos(Gi,"%*.*lf",1,0); load nwin = ^CFILE;
		CFile = "twid" $+ ftos(Gi,"%*.*lf",1,0); load twidth = ^CFILE;
		CFile = "winr" $+ ftos(Gi,"%*.*lf",1,0); load winner = ^CFILE;
		CFile = "wpbc" $+ ftos(Gi,"%*.*lf",1,0); load wpbc = ^CFILE; 

		/* no dslope x[npar] except for EWA Lite, EWA and its special cases */
		if (model <= 4);
			payoff0 = pay - x[npar].*abs(seqa(0,1,ns)'.*ones(ns,ns) - seqa(0,1,ns).*ones(ns,ns));
			payoff0 = payoff0.*(payoff0.>0);
		endif;
	elseif ((Gi >= 23)AND(Gi <= 28)); 
		CFile = "oppid" $+ ftos(Gi,"%*.*lf",1,0); load oppid = ^CFILE;
	endif;

	/* Warning: initial attractions generated only meant for subjects sharing same strategy set within same group */
	att0 = zeros(max_ns,ngrp); tatt0 = zeros(max_tns,ngrp); call initv; 

	if pool == 1;	/* if pool all games */
		if Gi <= 2; 				xt[npar+1] = x[npar+Gi]; 
		elseif ((3 <= Gi)AND(Gi <= 4));	xt[npar+1] = x[npar+3]; 
		elseif ((5 <= Gi)AND(Gi <= 9));	xt[npar+1] = x[npar+4]; 
		elseif ((10 <= Gi)AND(Gi <= 13));	xt[npar+1] = x[npar+5]; 
		elseif ((14 <= Gi)AND(Gi <= 15));	xt[npar+1] = x[npar+6]; 
		elseif ((16 <= Gi)AND(Gi <= 22));	xt[npar+1] = x[npar+7]; endif;
	else; xt = x; endif;

	/* select the right likelihood procedure */
	if model  == 0; call premax; 			ylog[ncount+1:ncount+n*t] = ffllk(xt);
	elseif (model > 0) and (model <= 4);	ylog[ncount+1:ncount+n*t] = ewallk(xt); 
	elseif model == 5;				ylog[ncount+1:ncount+n*t] = relllk(xt);
	elseif model == 6; 				ylog[ncount+1:ncount+n*t] = qrellk(xt); 
	endif;

	/* When pooling give each game equal weight */
	if pool == 1 or pool == 2; ylog[ncount+1:ncount+n*t] = ylog[ncount+1:ncount+n*t]./(n*t); endif; 

	ncount = ncount + n*t;

	/* parameter print out */
	if vldn == 1; call parout(xt); endif;

	Gi = Gi + 1;
endo;

LASTV:

retp(ylog);
endp;

/* End: Total Log-likelihood */


Proc(0) = parout(xt);

local s1phi, s1delta, s1kappa, s2phi, s2delta, s2kappa, s3phi, s3delta, s3kappa, yy, ev;

s2phi ={}; s2kappa = {}; s2delta = {};
s3phi ={}; s3kappa = {}; s3delta = {};

	format /rd 6,4;
	output file=^BFile on;

	if model == 0; 
		print; print " Average Transition Probability (Empirical)";
		if 3<= Gi and Gi<=4; 
			trpr_em = trpr_em./(n*(t-1));		
			trpr_em = trpr_em[1,.]|(reshape(sumc(reshape(trpr_em[2:ns,.]',10*ns,10)'),ns,10)');
			trpr_em = trpr_em';
			trpr_em = trpr_em[1,.]|(reshape(sumc(reshape(trpr_em[2:ns,.]',10*11,10)'),11,10)');
			trpr_em = trpr_em'; print trpr_em;
		elseif 5<= Gi and Gi<=9; 
			trpr_em = trpr_em./(n*(t-1));		
			trpr_em = trpr_em[1,.]|(reshape(sumc(reshape(trpr_em[2:ns,.]',12*ns,10)'),ns,12)');
			trpr_em = trpr_em';
			trpr_em = trpr_em[1,.]|(reshape(sumc(reshape(trpr_em[2:ns,.]',12*13,10)'),13,12)');
			trpr_em = trpr_em'; print trpr_em;
		else; print (seqa(1,1,rows(trpr_em)))~(trpr_em./(n*(t-1))); endif;
	endif;

	print; print " Average Transition Probability";
	if 3<= Gi and Gi<=4; 
		trpr_ffr = trpr_ffr./(n*(t-1));		
		trpr_ffr = trpr_ffr[1,.]|(reshape(sumc(reshape(trpr_ffr[2:ns,.]',10*ns,10)'),ns,10)');
		trpr_ffr = trpr_ffr';
		trpr_ffr = trpr_ffr[1,.]|(reshape(sumc(reshape(trpr_ffr[2:ns,.]',10*11,10)'),11,10)');
		trpr_ffr = trpr_ffr'; print trpr_ffr;
	elseif 5<= Gi and Gi<=9; 
		trpr_ffr = trpr_ffr./(n*(t-1));		
		trpr_ffr = trpr_ffr[1,.]|(reshape(sumc(reshape(trpr_ffr[2:ns,.]',12*ns,10)'),ns,12)');
		trpr_ffr = trpr_ffr';
		trpr_ffr = trpr_ffr[1,.]|(reshape(sumc(reshape(trpr_ffr[2:ns,.]',12*13,10)'),13,12)');
		trpr_ffr = trpr_ffr'; print trpr_ffr;
	else; print (seqa(1,1,rows(trpr_ffr)))~(trpr_ffr./(n*(t-1))); endif;

	output file=^PFile on;
	if model == 0;

		print; print " Distribution of Phi ";
		print (seqa(1,1,n))~phi;
		print; print " Distribution of Kappa ";
		print (seqa(1,1,n))~kappa;
		print; print " Distribution of Delta ";
		print (seqa(1,1,n))~delta;
		print; print " Lambda: " meanc(meanc(lambda));

		s2phi = s2phi|meanc(phi); s3phi = s3phi|meanc(phi');
		s2kappa = s2kappa|meanc(kappa); s3kappa = s3kappa|meanc(kappa');
		s2delta = s2delta|meanc(delta); s3delta = s3delta|meanc(delta');

		s1phi = phi; s1kappa = kappa; s1delta = delta;
		yy = 1; do while yy <= t;
			s1phi[.,yy] =sortc(s1phi[.,yy],1);
			s1kappa[.,yy] =sortc(s1kappa[.,yy],1);
			s1delta[.,yy] =sortc(s1delta[.,yy],1);
			yy = yy+1;
		endo;

		print; print " 25% and 75% percentile value Across Subjects ";

		print; print " Phi ";
		print (seqa(1,1,t)~(s1phi[round(n*0.25),.]'))';
		print (seqa(1,1,t)~(s1phi[round(n*0.75),.]'))';

		print; print " Kappa ";
		print (seqa(1,1,t)~(s1kappa[round(n*0.25),.]'))';
		print (seqa(1,1,t)~(s1kappa[round(n*0.75),.]'))';

		print; print " Delta ";
		print (seqa(1,1,t)~(s1delta[round(n*0.25),.]'))';
		print (seqa(1,1,t)~(s1delta[round(n*0.75),.]'))';

		s1phi = phi; s1kappa = kappa; s1delta = delta;
		yy = 1; do while yy <= n;
			s1phi[yy,.] =sortc(s1phi[yy,.]',1)';
			s1kappa[yy,.] =sortc(s1kappa[yy,.]',1)';
			s1delta[yy,.] =sortc(s1delta[yy,.]',1)';
			yy = yy+1;
		endo;

		print; print " 25% and 75% percentile value Across Time ";

		print; print " Phi ";
		print (seqa(1,1,n)~(s1phi[.,round(t*0.25)]))';
		print (seqa(1,1,n)~(s1phi[.,round(t*0.75)]))';

		print; print " Kappa ";
		print (seqa(1,1,n)~(s1kappa[.,round(t*0.25),.]))';
		print (seqa(1,1,n)~(s1kappa[.,round(t*0.75),.]))';

		print; print " Delta ";
		print (seqa(1,1,n)~(s1delta[.,round(t*0.25),.]))';
		print (seqa(1,1,n)~(s1delta[.,round(t*0.75),.]))';

	endif;

	if model == 0; 
		print; print " Average Values Across Time and Subjects ";
	
		print; print " Phi ";
		print (seqa(1,1,t)~meanc(phi))';
		print (seqa(1,1,n)~meanc(phi'))';
	
		print; print " Kappa ";
		print (seqa(1,1,t)~meanc(Kappa))';
		print (seqa(1,1,n)~meanc(Kappa'))';

		print; print " Delta ";
		print (seqa(1,1,t)~meanc(Delta))';
		print (seqa(1,1,n)~meanc(Delta'))';
	endif;

	if j <= 30; evcall = 1; ev = econv(xt); evcall = 0;
	else; ev = zeros(14,1); endif;

	if model == 0;
		rslt = (meanc(vec(lambda))|vcx(vec(lambda))|rslt);
		rslt = (meanc(vec(delta))|vcx(vec(delta))|rslt);
		rslt = (meanc(vec(kappa))|vcx(vec(kappa))|rslt);
		rslt = (meanc(vec(phi))|vcx(vec(phi))|rslt);

		frslt = frslt~(0|n|ev|(n*t)|(t0[Gi]*n0[Gi])|xt|rslt);
	else;
		erslt = erslt~(ev[2]|ev[4:5]|ev[7:14]|xt|rslt);
	endif;

	output off;

endp;

/* End: Parameter Output */




/* Calculate Economic Value */

Proc econv(xt);

local k, kk, i, ii, temp1, pthmax, ttother, mttother, bhit, temp2, temp3, payoff;
local bpay, mbpay, apay, b0pay, mb0pay, a0pay, bimprv, mbimprv, pr_opp, beimprv, mbeimprv;
local cothmax, rothmax, tothmax, epayoff, m_pay, m_gap, mecorr, tmeval, evm, evn;

m_pay = zeros(n,t);	/* actual payoff */
m_gap = zeros(n,t);	/* the "distance" between actual choice and model response */
pthmax = simprob(Gi,1,othmax);
tothmax = zeros(n,t);

/*	
SpeciaL case for pBC
*/
if ((Gi >= 3) and (Gi <= 4));

	ns = ns1[1]; 
	epayoff = zeros(ns,n);		/* strategies by subject for period i */
	i = 1; do while i <= t;
		k = 1; do while k <= int(((n-1)/nsj)+1);
			/* random draw subject's choice say nsj by evsim */
			rothmax = zeros(nsj,evsim);
			ii = 1; do while ii <= evsim;
				cothmax = othmax[((k-1)*nsj+1):(k*nsj),((i-1)*ns+1):(i*ns)];
				cothmax = cumsumc(cothmax');		/* cumulative probability dist */
				cothmax = (cothmax - rndev[(((k-1)*evsim+ii-1)*nsj+1):(((k-1)*evsim+ii)*nsj),i]');	
				rothmax[.,ii] = minindc(abs(cothmax) + (cothmax.<0));	/* find the smallest positive difference */
				ii = ii +1;
			endo;

			temp1 = ones(nsj,nsj) - eye(nsj);
			temp1 = temp1*(rothmax-1);		/* summation matrix: nsj by evsim, - 1 for adjusting for strategy 0 */
			temp1 = round((wpbc[((k-1)*nsj+1):(k*nsj)]./(nsj-wpbc[((k-1)*nsj+1):(k*nsj)])).*temp1)+1; 		/* target number */

			ii = 1; do while ii <= ns;
				temp2 = (temp1.==ii);  
				temp3 = (sumc(rothmax.==ii)'-(rothmax.==ii)+temp2);
				temp3 = temp3 + (temp3.==0);
				epayoff[ii,((k-1)*nsj+1):(k*nsj)] = sumc((temp2.*(pay./temp3))')';
				ii = ii+1; 
			endo;

			k = k+1;
		endo;

		tothmax[.,i] = maxindc(epayoff);	/* bionic players' best response */				
		i = i+1;
	endo;

endif;

/* first period economic value excluded because used for burn-in: common for all models */

bpay = 0; mbpay = 0; apay = 0; bimprv = 0; mbimprv = 0; beimprv = 0; mbeimprv = 0; bhit = {};

k = 1; do while k <= n;

	ns = ns1[k]; ons = ons1[k];

	/* opponent(s)' choice probabilities */
	pr_opp = reshape(pthmax[k,1:t*ons],t,ons);		/* opponent's choice probabilities */

	b0pay = bpay; mb0pay = mbpay; a0pay = apay;

	i = 2; do while i <= t;

		if (Gi <= 2); 
	
			/* best response to actual observed opponents' strategies */

			ttother = (choice0[(nsj*int((k-1)/nsj)+1):(nsj*int((k-1)/nsj+1)),i]).*ones(nsj,ns);
			ttother[(k-nsj*int((k-1)/nsj)),.] = seqa(1,1,ns)';

			/* replace the ii strategy with its payoff to find perfect best strategy */
			ttother = median(ttother);
			ii = 1; do while ii <= ns;
				ttother[ii] = payoff0[ii,ttother[ii]];
				ii = ii +1;
			endo;
			mttother = maxindc(ttother);

			/* calculate payoff */
			ttother = (choice0[(nsj*int((k-1)/nsj)+1):(nsj*int((k-1)/nsj+1)),i]);
			ttother[(k-nsj*int((k-1)/nsj)),.] = mttother;		/* perfect foresight */
			mbpay = mbpay+payoff0[mttother,median(ttother)];
			tothmax[k,i] = maxindc(payoff0*pr_opp[i,.]');
			ttother[(k-nsj*int((k-1)/nsj)),.] = maxindc(payoff0*pr_opp[i,.]');	/* bionic player */
			bpay = bpay + payoff0[tothmax[k,i],median(ttother)];
			apay = apay + payoff0[choice0[k,i],others[k,i]];	/* actual payoff */

			m_gap[k,i] = (maxindc(payoff0*pr_opp[i,.]')- choice0[k,i]);
			m_pay[k,i] = payoff0[choice0[k,i],others[k,i]];

		elseif ((Gi >= 3) and (Gi <= 4));
			
			/* actual winning */
			ttother = (choice0[(nsj*int((k-1)/nsj)+1):(nsj*int((k-1)/nsj+1)),i]-1);	/* adjusting for strategy 0 */
			temp1 = (abs(ttother - wpbc[k].*meanc(ttother)));
			temp1 = (temp1.==minc(temp1)');		/* winner(s) */	
			apay = apay + temp1[(k-nsj*int((k-1)/nsj))].*(pay/sumc(temp1));

			m_pay[k,i] = temp1[(k-nsj*int((k-1)/nsj))].*(pay/sumc(temp1));

			/* best response to actual observed opponents' strategies */

			ttother[(k-nsj*int((k-1)/nsj))] = 0;
 			mttother = sumc(ttother)/(nsj - 1);
			ttother[(k-nsj*int((k-1)/nsj))] = (mttother*wpbc[k]*(nsj - 1))/(nsj - wpbc[k]);	/* best response */

			temp1 = (abs(ttother - wpbc[k].*meanc(ttother)));
			temp1 = (temp1.==minc(temp1)');		/* winner(s) */	
			mbpay = mbpay+temp1[(k-nsj*int((k-1)/nsj))].*(pay/sumc(temp1));

			ttother[(k-nsj*int((k-1)/nsj))] = tothmax[k,i]-1;		/* bionic player's best response, -1 for adjusting for strategy 0 */
			temp1 = (abs(ttother - wpbc[k].*meanc(ttother)));
			temp1 = (temp1.==minc(temp1)');		/* winner(s) */	
			bpay = bpay+temp1[(k-nsj*int((k-1)/nsj))].*(pay/sumc(temp1));

			m_gap[k,i] = (tothmax[k,i] - choice0[k,i]);

		elseif ((Gi >= 16) and (Gi <= 22));

			/* for pot games, count number of choice into small pot */
			mbpay = mbpay+maxc(payoff0[.,others[k,i]]);
			bpay = bpay+ payoff0[maxindc(payoff0*pr_opp[i,.]'),others[k,i]];
			apay = apay + payoff0[choice0[k,i],others[k,i]];

			m_gap[k,i] = 1 - ((maxindc(payoff0*pr_opp[i,.]')- choice0[k,i]).==0);
			m_pay[k,i] = payoff0[choice0[k,i],others[k,i]];

		elseif ((Gi >= 10) and (Gi <= 13));

			mbpay = mbpay+maxc(payoff0[.,others[k,i]]);
			apay = apay + payoff0[choice0[k,i],others[k,i]];
					
			/* payoff matrix for column players (k>10) is adjoint to row player's */
			if k > 10; 
				bpay = bpay+ payoff0[maxindc(payoff0[.,ons+1:2*ons]*pr_opp[i,.]'),others[k,i]];
				m_gap[k,i] = (maxindc(payoff0[.,ons+1:2*ons]*pr_opp[i,.]')- choice0[k,i]);
			else; 
				bpay = bpay+ payoff0[maxindc(payoff0[.,1:ons]*pr_opp[i,.]'),others[k,i]]; 
				m_gap[k,i] = (maxindc(payoff0[.,1:ons]*pr_opp[i,.]')- choice0[k,i]);
			endif;
			m_pay[k,i] = payoff0[choice0[k,i],others[k,i]];

		else;

			payoff = selif(payoff0[.,begpay[k,i]+1:begpay[k,i]+ons],nsavb[.,signal[k,i]]);	/* find the right payoff matrix  */

			mbpay = mbpay+maxc(selif(payoff0[.,others[k,i]],nsavb[.,signal[k,i]]));
			bpay = bpay+ payoff0[maxindc(payoff*pr_opp[i,.]'),others[k,i]]; 
			apay = apay + payoff0[choice0[k,i],others[k,i]];

			m_gap[k,i] = (maxindc(payoff*pr_opp[i,.]')- choice0[k,i]);
			m_pay[k,i] = payoff0[choice0[k,i],others[k,i]];

		endif;

		i = i+1;
	endo;

	bimprv = bimprv + ((bpay - b0pay).>(apay - a0pay));
	mbimprv = mbimprv + ((mbpay - mb0pay).>(apay - a0pay));

	beimprv = beimprv + ((bpay - b0pay).>=(apay - a0pay));
	mbeimprv = mbeimprv + ((mbpay - mb0pay).>=(apay - a0pay));

	bhit = bhit|((bpay - b0pay).>=(apay - a0pay));

	k = k+1;
endo;

CFile = "b" $+ ftos(model,"%*.*lf",1,0) $+ ftos(j,"%*.*lf",1,0) $+ "h" $+ ftos(Gi,"%*.*lf",1,0); save ^CFILE = bhit; 
output off;

output file=^EFile on; print;
print "Model (0 for ELite, 1 for BB, 2 for CR(Kappa = 0), 3 for CR(Kappa = 1), 4 for EWA, 5 for REL and 6 for QRE): " model;
print "Distance"; abs(m_gap[.,2:t]); print "Payoff"; (m_pay[.,2:t]); print;
output off;

tmeval = vec(m_gap[.,2:t].==0);
mecorr = corrx(abs(vec(m_gap[.,2:t]))~vec(m_pay[.,2:t]));

if ((Gi >= 3) and (Gi <= 4)); output file=^MSDFile on; print; counts(vec(nwin[.,2:t]),seqa(0,1,nsj+1))~counts((tmeval.*vec(nwin[.,2:t])),seqa(0,1,nsj+1)); output off; endif;

evm = selif(vec(m_pay[.,2:t]),tmeval);
evn = selif(vec(m_pay[.,2:t]),(1-tmeval));
 
retp(mbimprv|bimprv|apay|mbpay|bpay|mbeimprv|beimprv|mecorr[1,2]|meanc(evm)|stdc(evm)|sumc(tmeval)|meanc(evn)|stdc(evn)|sumc(1-tmeval));
endp;

/* End: Calculate Economic Value */





/* Choice Probability Distribution for Subject k: Economic Value as well as Thinking model */

Proc(0) = evprob(pr,k);

local temp1, temp2, temp3, i;

	ns = ns1[k]; ons = ons1[k];

	if ((Gi >= 10) and (Gi <= 13));

		/* subject k's opponent's predicted probailities */
		othmax[(k>10).*(k-10)+(k<=10).*(k+10),.] = vec(exp(pr))';	/* 1 is paired with 11 etc.. */		

	elseif ((Gi >= 5) and (Gi <= 9));

		/* subject k's opponents' predicted probailities */
		/* Opponent ID can not be identified, hence equal probable */
		othmax[(int((k-1)/nsj)*nsj+1):(int((k-1)/nsj+1)*nsj),.] = othmax[(int((k-1)/nsj)*nsj+1):(int((k-1)/nsj+1)*nsj),.] + (1/(nsj-1)).*vec(exp(pr))';		
		othmax[k,.] = othmax[k,.] - (1/(nsj-1)).*vec(exp(pr))';

	elseif ((Gi >= 16) and (Gi <= 22));

		/* for pot games, count number of other's choices into small pot */

		/* prob[small pot = i,k] = prob[small pot = i,k-1]*prob[k large pot] */
		temp1 = othmax[(int((k-1)/nsj)*nsj+1):(int((k-1)/nsj+1)*nsj),.].*vec(exp(pr[2,.]).*ones(ons,t))';	
		temp1 = temp1 + (sumc(othmax[(int((k-1)/nsj)*nsj+1):(int((k-1)/nsj+1)*nsj),.]').==0).*vec(exp(pr[2,.]).*(ones(1,t)|zeros(ons-1,t)))';

		/* prob[small pot = i,k] = prob[small pot = i-1,k-1]*prob[k small pot] */			
		temp2 = zeros(nsj,1)~(othmax[(int((k-1)/nsj)*nsj+1):(int((k-1)/nsj+1)*nsj),.].*vec(exp(pr[1,.]).*(ones(ons-1,t)|zeros(1,t)))');
		temp2 = temp2[.,1:(cols(temp2)-1)];
		temp2 = temp2 + (sumc(othmax[(int((k-1)/nsj)*nsj+1):(int((k-1)/nsj+1)*nsj),.]').==0).*vec(exp(pr[1,.]).*(zeros(1,t)|ones(1,t)|zeros(ons-2,t)))';

		temp3 = othmax[k,.];	/* do not update subject's k count */
		othmax[(int((k-1)/nsj)*nsj+1):(int((k-1)/nsj+1)*nsj),.] = temp1+temp2;
		othmax[k,.] = temp3;

	elseif (Gi<=4) or ((Gi >= 14) and (Gi <= 15));	

		/* need to change below */
		othmax[k,.] = vec(exp(pr))';	/* record the choice probabilities of subject k */

	elseif ((Gi >= 23) and (Gi <= 28));

		i = 1; do while i <= t;
			othmax[oppid[k,i],((i-1)*ons+1):(i*ons)] = exp(pr[.,i])';	/* record the choice probabilities of subject k */
			i = i+1; 
		endo;

	endif;

retp;
endp;

/* End: Choice Probability Distribution for subject k */


/* Choice Probability Distribution for  CDG MAG and pBC */

Proc simprob(Gi,id,mothmax);

local i, ii, k, temp1, tothmax, cothmax, rothmax, rrothmax;

if id; tothmax = mothmax; 
else;  
	tothmax = zeros(n,t*max_ons);
	k = 1; do while k <= (n);  
		if j == 14 or j ==15; tothmax[k,1:t*ns1[k]] = (1/ns1[k]).*ones(1,t*ns1[k]); 
		else; tothmax[k,1:t*ons1[k]] = (1/ons1[k]).*ones(1,t*ons1[k]); endif;
		 k = k+1; 
	endo;
endif;

if (Gi <= 4);
	rrothmax = zeros(n+nv,t*max_ons);

	i = 1; do while i <= t;
		k = 1; do while k <= int(((n-1)/nsj)+1);

			/* random draw subject's choice say nsj by evsim */
			rothmax = zeros(nsj,evsim);
			ii = 1; do while ii <= evsim;
				cothmax = tothmax[((k-1)*nsj+1):(k*nsj),((i-1)*ns+1):(i*ns)];
				cothmax = cumsumc(cothmax');		/* cumulative probability dist */
				cothmax = (cothmax - rndev[(((k-1)*evsim+ii-1)*nsj+1):(((k-1)*evsim+ii)*nsj),i]');	
				rothmax[.,ii] = minindc(abs(cothmax) + (cothmax.<0));	/* find the smallest positive difference */
				ii = ii +1;
			endo;
			if ((Gi >= 3) and (Gi <= 4));

				temp1 = ones(nsj,nsj) - eye(nsj);
				temp1 = temp1*(rothmax-1);		/* summation matrix: nsj by evsim */
				temp1 = round((wpbc[((k-1)*nsj+1):(k*nsj)]./(nsj-wpbc[((k-1)*nsj+1):(k*nsj)])).*temp1)+1; 		/* target number */
				ii = 1; do while ii <= nsj; rrothmax[((k-1)*nsj+ii),((i-1)*ons+1):(i*ons)] = (counts(temp1[ii,.]',seqa(1,1,ons))./evsim)'; ii = ii+1; endo;

			elseif ((Gi >= 1) and (Gi <= 2));
				rrothmax[((k-1)*nsj+1):(k*nsj),((i-1)*ons+1):(i*ons)] = (counts(median(rothmax),seqa(1,1,ons))./evsim)'.*ones(nsj,ons);
			endif;

			k = k+1;
		endo;

		i = i+1;
	endo;
	tothmax = rrothmax;

/* session 14 is opponent for session 15 (patent weak): save own prob first then load opponent's */
elseif Gi == 14; 
	MPAR = "q" $+ ftos(model,"%*.*lf",1,0) $+ ftos(id,"%*.*lf",1,0) $+ ftos(j,"%*.*lf",1,0) $+ ftos(15,"%*.*lf",1,0); 
	load tothmax = ^MPAR; 
elseif Gi == 15; 
	MPAR = "q" $+ ftos(model,"%*.*lf",1,0) $+ ftos(id,"%*.*lf",1,0) $+ ftos(j,"%*.*lf",1,0) $+ ftos(14,"%*.*lf",1,0); 
	load tothmax = ^MPAR; 
endif;


retp(tothmax);
endp;

/* End: Choice Probability Distribution for  CDG MAG and pBC */



/* Result Printout */

Proc(0) = prtVldn(ylog,yhit,ymax,ytemp);

	local nhit;

	output file=^DFile on;

	format /rd 4,4; 

	print; print "Calibration and Validation Results";
	print; print "Log-likelihood (Total)"; print sumc(delif(ylog,Ivldn))~sumc(selif(ylog,Ivldn));
	print; print "Number of Hits (Total)"; print sumc(delif(((ymax-ytemp).==0)./yhit,Ivldn))~sumc(selif(((ymax-ytemp).==0)./yhit,Ivldn));
	print; print "Average Hit Probability of Chosen Strategy"; print meanc(exp(delif(ylog,Ivldn)))~meanc(exp(selif(ylog,Ivldn)));
	print; print "Average Probability of Hit: " meanc(selif(exp(ytemp),((ytemp-ymax).==0)));

	rslt = rslt|(sumc(delif(ylog,Ivldn))~sumc(selif(ylog,Ivldn)))';		
	rslt = rslt|(sumc(delif(((ymax-ytemp).==0)./yhit,Ivldn))~sumc(selif(((ymax-ytemp).==0)./yhit,Ivldn)))';
	rslt = rslt|(meanc(exp(delif(ylog,Ivldn)))~meanc(exp(selif(ylog,Ivldn))))';

	if model == 0 and pool == 0;
		format /rd 4,0; 
		print; print "Chosen Strategy"; print seqa(1,1,n)~choice0;
	endif;

	format /rd 4,4; 
	print; print "Probability of Chosen Strategy"; print seqa(1,1,n)~exp(reshape(ylog,n,t));
	print; print "Chosen Strategy is a Hit"; print seqa(1,1,n)~(reshape(((ytemp-ymax).==0),n,t));

	output file=^BFile on;
	
	pr_ffr = exp(reshape(ylog,n,t));

	/* Save statistics for McNemar Test */
	nhit = ((ymax-ylog).==0)./yhit;
	CFile = "m" $+ ftos(model,"%*.*lf",1,0) $+ ftos(j,"%*.*lf",1,0) $+ "h" $+ ftos(Gi,"%*.*lf",1,0); save ^CFILE = nhit; 

	format /rd 8,4;
	print;

	if model == 0;
		CFile = ftos(j,"%*.*lf",1,0) $+ "emp" $+ ftos(Gi,"%*.*lf",1,0); load empred = ^CFILE; 
		print; print " Average Strategy across time -- Empirical ";
		if ((Gi >= 3) and (Gi <= 4));
			print (seqa(1,1,t)~(sumc(seqa(0,1,ns).*(empred./n))))';
		else;
			print (seqa(1,1,t)~(sumc(seqa(1,1,ns).*(empred./n))))';
		endif;	
		print;
		print " Empirical Frequency ";
		if 3<= Gi and Gi<=4; 
			print (seqa(1,1,11))~((empred[1,.]|(reshape(sumc(reshape(empred[2:ns,.]',10*t,10)'),t,10)'))./n);
		elseif 5<= Gi and Gi<=9; 
			print (seqa(1,1,13))~((empred[1,.]|(reshape(sumc(reshape(empred[2:ns,.]',12*t,10)'),t,12)'))./n);
		elseif 14<=Gi and Gi<=15;
			print (seqa(1,1,ns))~((reshape(sumc(reshape(empred,(ns*t/4),4)'),ns,(t/4)))./(4*n));
		else; print (seqa(1,1,ns))~(empred./n); endif;
	endif;

	if model == 0; print; print " Average Predicted Probability -- Fatfree ";
	elseif model == 1; print; print " Average Predicted Probability -- Belief Based ";
	elseif model == 2; print; print " Average Predicted Probability -- Reinforcement (Kappa = 0)";
	elseif model == 3; print; print " Average Predicted Probability -- Reinforcement (Kappa = 1)";
	elseif model == 4; print; print " Average Predicted Probability -- adaptive EWA ";
	elseif model == 5; print; print " Average Predicted Probability -- REL ";
	elseif model == 6; print; print " Average Predicted Probability -- QRE ";
	endif;

	if 3<= Gi and Gi<=4; 
		print (seqa(1,1,11))~((ffpred[1,.]|(reshape(sumc(reshape(ffpred[2:ns,.]',10*t,10)'),t,10)'))./n);
	elseif 5<= Gi and Gi<=9; 
		print (seqa(1,1,13))~((ffpred[1,.]|(reshape(sumc(reshape(ffpred[2:ns,.]',12*t,10)'),t,12)'))./n);
	elseif 14<=Gi and Gi<=15;
		print (seqa(1,1,ns))~((reshape(sumc(reshape(ffpred,(ns*t/4),4)'),ns,(t/4)))./(4*n));
	else; print (seqa(1,1,ns))~(ffpred./n); endif;

	print;
	print " Average Choice Probability across time and subject ";
	print (seqa(1,1,t)~meanc(exp(reshape(ylog,n,t))))';
	print (seqa(1,1,n)~meanc(exp(reshape(ylog,n,t))'))';

	output off; 

retp;
endp;

/* End: Result printout */



/* Accumulate Statistics for Reporting */
proc(3) = valstat(ylog,pr,choice,k);

local ytemp, ymax, yhit, i;

		empred = empred + choice;
		CFile = ftos(j,"%*.*lf",1,0) $+ "emp" $+ ftos(Gi,"%*.*lf",1,0); save ^CFILE = empred;
		ffpred = ffpred + exp(pr);
		CFile = ftos(j,"%*.*lf",1,0) $+ "ffp" $+ ftos(Gi,"%*.*lf",1,0); save ^CFILE = ffpred; 

		ytemp = sumc((pr.*choice));
		ymax = maxc(pr);
		yhit = sumc((pr -maxc(pr)').==0);	/* # of hit strategies */

		/* transition probabilities */
		i = 2; do while i <= t;
			trpr_ffr[choice0[k,i-1],.] = trpr_ffr[choice0[k,i-1],.] + exp(pr[.,i])'; 
			trpr_em[choice0[k,i-1],choice0[k,i]] = trpr_em[choice0[k,i-1],choice0[k,i]] + 1; 
		i = i+1; endo;

	retp(ytemp,ymax,yhit);

endp;
/* End: Accumulate Statistics for Reporting */



/* Log-likelihood Function for EWA Lite (Fatfree) */

Proc ffllk(x);

local lam, att, choice, payoff, pr, pr0, k, i, delt1;
local ylog, ymax, ytemp, yhit;
local tymax, tytemp, tyhit, pthmax, pr_opp;
local tatt;

ytemp = zeros(n*t,1); ylog = zeros(n*t,1);
ymax = zeros(n*t,1); yhit = zeros(n*t,1);
pr_ffl = zeros(n,t*max_ns);

lam =  x[bp+1];	/* Lambda */

/* calculate likelihood for each subject k */
k = 1;
do while k <= n;

	tns = tns1[k]; ns = ns1[k]; ons = ons1[k];

	tatt = zeros(tns,t);	/* attraction matrix: strategies by game round */
	att = zeros(ns,t);	/* attraction matrix: strategies by game round */	
	choice = zeros(ns,t);	/* choice matrix: strategies by game round */
	delt1 = ones(ns,t);	/* Delta matrix: strategies by game round */
	
	/* First round attraction: initial attraction */
	tatt[.,1] = (1./lam).*tatt0[.,int((k-1)/nsj+1)]; 
	att[.,1] = selif(tatt[.,1],nsavb[.,signal[k,1]]); 

	/* Second round and subsequent attractions */
	i = 2;
	do while i <= t;

		choice[choice0[k,i-1],i-1] = 1;	/* choice0 is ID of strategy chosen */
		payoff = genpay(k,i-1);		/* payoff matrix is for period i-1 choice */

		/* Note that for ease of programming att and nt have been shifted forward by 1 */
		/* In other words att[.,i] should be interpreted as att[.,i-1] in the paper */

		pr0 = sumc(choice[.,1:i-1]')./(i-1);

		kappa[k,i-1] = 1 - 2.*sumc(rev(sortc(pr0,1)).*((seqa(1,1,ns)-1)./(ns-1)));
		lambda[k,i-1] = lam; 

		delta[k,i-1] = uphi[k,i-1]/spp[Gi]; 		/* Delta for print-out purpose */
		delt1[.,i-1] = (uphi[k,i-1]/spp[Gi]).*(payoff .< payoff[choice0[k,i-1]]) + (uphi[k,i-1]/spp[Gi]).*(payoff .>= payoff[choice0[k,i-1]]); 

		/* if initial value is specified */
		if (initial == 1);
			kappa[k,i-1] = (1/(i-1)).*ikappa + (1 - 1/(i-1)).*kappa[k,i-1];
			delta[k,i-1] = (1/(i-1)).*idelt + (1 - 1/(i-1)).*delta[k,i-1];
			delt1[.,i-1] = (1/(i-1)).*idelt + (1 - 1/(i-1)).*delt1[.,i-1];
			phi[k,i-1] = (1/(i-1)).*iphi + (1 - 1/(i-1)).*uphi[k,i-1];
		endif;

		nt[k,i] = phi[k,i-1].*(1 - kappa[k,i-1]).*nt[k,i-1] + 1;

		delt1[choice0[k,i-1],i-1] = 1;
	
		if ((Gi >= 3) and (Gi <= 4));
			att[.,i] = (phi[k,i-1].*nt[k,i-1].*selif(tatt[.,i-1],nsavb[.,signal[k,i-1]]) + (delt1[.,i-1] + (1 - delt1[.,i-1]).*choice[.,i-1].*winner[k,i-1]).*payoff)./nt[k,i];		/* note that in pBC only winner(s) receive payoff */
		else;
			att[.,i] = (phi[k,i-1].*nt[k,i-1].*selif(tatt[.,i-1],nsavb[.,signal[k,i-1]]) + (delt1[.,i-1] + (1 - delt1[.,i-1]).*choice[.,i-1]).*payoff)./nt[k,i];
		endif;
		tatt[.,i] = (1-nsavb[.,signal[k,i-1]]).*tatt[.,i-1] + nsavb[.,signal[k,i-1]].*(ones(tns/ns,1).*.att[.,i]);
		att[.,i] = selif(tatt[.,i],nsavb[.,signal[k,i]]);

		i = i+1;
	endo;

	delta[k,t] = uphi[k,t]/spp[Gi]; 
	choice[choice0[k,t],t] = 1; payoff = genpay(k,t-1);
	delt1[.,t] = (uphi[k,t]/spp[Gi]).*(payoff .< payoff[choice0[k,t]]) + (uphi[k,t]/spp[Gi]).*(payoff .>= payoff[choice0[k,t]]); 

	pr0 = sumc(choice[.,1:t]')./(t);
	kappa[k,t] = 1 - 2.*sumc(rev(sortc(pr0,1)).*((seqa(1,1,ns)-1)./(ns-1)));
	lambda[k,t] = lam; 

	if (initial == 1);
		kappa[k,t] = (1/t).*ikappa + (1 - 1/t).*kappa[k,t];
		delta[k,t] = (1/t).*idelt + (1 - 1/t).*delta[k,t];
		delt1[.,t] = (1/t).*idelt + (1 - 1/t).*delt1[.,t];
		phi[k,t] = (1/t).*iphi + (1 - 1/t).*uphi[k,t];
	endif;

	if ((Gi >= 3) and (Gi <= 4)); 
		choice[101,2:t] = zeros(1,t-1);		/* was set to 0 in original program for pBC*/
	endif;

	delt1[choice0[k,t],t] = 1;

	/* shift lambda forward by 1 so that it corresponds to att */
	if t > 1; lambda[k,2:t] = lambda[k,1:t-1]; endif; lambda[k,1] = lam; 

	att = att - median(att[.,.])';
	pr = (lambda[k,1:t].*att) - ln(sumc(exp(lambda[k,1:t].*att))'+1e-70);

	ylog[(k-1)*t+1:k*t] = sumc((pr.*choice));

	/* economic value calculation */
	call evprob(pr,k);			/* opponent(s)'s choice probability */
	pr_ffl[k,1:t*ns] = vec(exp(pr))';		/* own choice probability */ 

	/* Validation purpose: accumulates statistics */
	if vldn == 1; 
		{tytemp,tymax,tyhit} = valstat(ylog,pr,choice,k);
		ytemp[(k-1)*t+1:k*t] = tytemp; ymax[(k-1)*t+1:k*t] = tymax; yhit[(k-1)*t+1:k*t] = tyhit;
	endif;	

	k = k+1;	
endo;

/* if validation but no economic value calculation, call print-out procedure */
if vldn == 1 and evcall == 0; call prtVldn(ylog,yhit,ymax,ytemp); endif;	

retp(ylog);
endp;

/* End: LL function calculation for EWA Lite (Fatfree) */



/* EWA Lite: generating phi */

Proc(0) = premax;

local choice, payoff, k, i, tphi, tothers, Bothers, ib;


/* to calculate phi, need to use the original data on <others> */
/* the modified <others> is pointer to the payoff matrix */

if ((Gi >= 10)AND(Gi <= 13)) or ((Gi >= 23)AND(Gi <= 28));
	Bothers = others; 
	CFile = "Aother" $+ ftos(Gi-9,"%*.*lf",1,0); load others = ^CFILE; 
endif; 

k = 1;
do while k <= n;
	ns = ns1[k]; ons = ons1[k];
	choice = zeros(ns,t);	
	tothers = zeros(ons,t);	
	i = 1;
	do while i <= t;
		choice[choice0[k,i],i] = 1;
		payoff = payoff0[1:ns,others[k,i]];
		tothers[others[k,i],i] = 1; 
		
		ib = i - mvavg[Gi] + 1;
		if (ib <= 0); ib = 1; endif;

		tphi = sumc(tothers[.,ib:i]')./(i-ib+1) - sumc(tothers[.,1:i]')./(i);
		uphi[k,i] = (1 - (sumc((tphi)^2)./2));

		i = i+1;
	endo;
	k = k+1;	
endo;

/* switch back the pointers to payoff matrix */
if ((Gi >= 10)AND(Gi <= 13)) or ((Gi >= 23)AND(Gi <= 28));
	others = Bothers; 
endif; 


retp;
endp;

/* End: generating phi */


/* Adaptive EWA Log-likelihood Function */

Proc ewallk(x);

local att, choice, payoff, pr, k, i, lam;
local ylog, ymax, ytemp, yhit, tymax, tytemp, tyhit;
local tatt;

ytemp = zeros(n*t,1); ylog = zeros(n*t,1);
ymax = zeros(n*t,1); yhit = zeros(n*t,1);

/* Parameters */
lam =  x[6];					/* lambda */
phi = x[1].*ones(n,t);				/* phi */
delt = (1/(1+exp(x[2]))).*ones(n,t);	/* delta */
kappa = (1/(1+exp(x[3]))).*ones(n,t);	/* kappa */
nt = (1./(1-phi[1,1]*(1 - kappa[1,1]))).*(1/(1+exp(x[4]))).*ones(n,t); /* Upper bound for N0 in EWA */

k = 1;
do while k <= n;

	tns = tns1[k]; ns = ns1[k]; ons = ons1[k];

	tatt = zeros(tns,t);	/* attraction matrix: strategies by game round */
	att = zeros(ns,t);	/* attraction matrix: strategies by game round */	
	choice = zeros(ns,t);	/* choice matrix: strategies by game round */

	tatt[.,1] = (1./lam).*tatt0[.,int((k-1)/nsj+1)]; 
	att[.,1] = selif(tatt[.,1],nsavb[.,signal[k,1]]); 

	i = 2;
	do while i <= t;

		nt[k,i] = phi[k,i-1].*(1 - kappa[k,i-1]).*nt[k,i-1] + 1;

		choice[choice0[k,i-1],i-1] = 1;	/* choice0 is ID of strategy chosen */
		payoff = genpay(k,i-1);		/* payoff matrix is for period i-1 choice */

		/* Note that for ease of programming att and nt have been shifted forward by 1 */
		/* In other words att[.,i] should be interpreted as att[.,i-1] in the paper */

		if ((Gi >= 3) and (Gi <= 4));
			att[.,i] = (phi[k,i-1].*nt[k,i-1].*selif(tatt[.,i-1],nsavb[.,signal[k,i-1]]) + (delt[k,i-1] + (1 - delt[k,i-1]).*choice[.,i-1].*winner[k,i-1]).*payoff)./nt[k,i];		/* note that in pBC only winner(s) receive payoff */
		else;
			att[.,i] = (phi[k,i-1].*nt[k,i-1].*selif(tatt[.,i-1],nsavb[.,signal[k,i-1]]) + (delt[k,i-1] + (1 - delt[k,i-1]).*choice[.,i-1]).*payoff)./nt[k,i];
		endif;
		tatt[.,i] = (1-nsavb[.,signal[k,i-1]]).*tatt[.,i-1] + nsavb[.,signal[k,i-1]].*(ones(tns/ns,1).*.att[.,i]);
		att[.,i] = selif(tatt[.,i],nsavb[.,signal[k,i]]);
		i = i+1;
	endo;

	choice[choice0[k,t],t] = 1; 

	if ((Gi >= 3) and (Gi <= 4)); 
		choice[101,2:t] = zeros(1,t-1);		/* was set to 0 in original program for pBC*/
	endif;

	att = att - median(att[.,.])';
	pr = ln(exp(lam.*att)+1e-70) - ln(sumc(exp(lam.*att))'+1e-70);

	ylog[(k-1)*t+1:k*t] = sumc((pr.*choice));

	/* economic value calculation */
	call evprob(pr,k);			/* opponent(s)'s choice probability */

	/* Validation purpose: accumulates statistics */
	if vldn == 1; 
		{tytemp,tymax,tyhit} = valstat(ylog,pr,choice,k);
		ytemp[(k-1)*t+1:k*t] = tytemp; ymax[(k-1)*t+1:k*t] = tymax; yhit[(k-1)*t+1:k*t] = tyhit;
	endif;	

	k = k+1;	
endo;

/* if validation but no economic value calculation, call print-out procedure */
if vldn == 1 and evcall == 0; call prtVldn(ylog,yhit,ymax,ytemp); endif;	

retp(ylog);

endp;

/* End; Adaptive EWA Log-likelihood Function pEWA */





/* REL Log-likelihood Function */

Proc relllk(x);

local att, choice, payoff, pr, k, i, lam;
local ylog, ymax, ytemp, yhit, tymax, tytemp, tyhit;
local pr_others, ct, pa, pv, n0;
local tatt;

ytemp = zeros(n*t,1); ylog = zeros(n*t,1);
ymax = zeros(n*t,1); yhit = zeros(n*t,1);


/* Parameters */
n0 = x[4];		/* N0 */
lam = x[6];		/* Lambda */

/* using first period others as input to PA */
pr_others = 0;
if ((Gi >= 10) and (Gi <= 13)) or ((Gi >= 23) and (Gi <= 28)); pr_others = counts((others[.,1] - int((others[.,1]-1)/ns)*ns), seqa(1,1,ons));
else; pr_others = counts(others[.,1], seqa(1,1,ons)); endif;
pr_others = pr_others + 1/ons; pr_others = pr_others./(sumc(pr_others)); pr_others = pr_others.*ones(ons,ns);


k = 1;
do while k <= n;

	tns = tns1[k]; ns = ns1[k]; ons = ons1[k];

	tatt = zeros(tns,t);	/* attraction matrix: strategies by game round */
	att = zeros(ns,t);	/* attraction matrix: strategies by game round */	
	choice = zeros(ns,t);	/* choice matrix: strategies by game round */

	ct = n0.*zeros(ns,t);
	pv = zeros(1,t);	
	pa = zeros(1,t);	

	if ((Gi >= 10) and (Gi <= 13)) or ((Gi >= 23) and (Gi <= 28));
		pa[1] = (1/ns).*sumc(sumc(payoff0[.,(int((others[k,1]-1)/ns)*ns+1):(int((others[k,1]-1)/ns+1)*ns)
]'.*pr_others));	/* assume equiprobable outcomes */
		pv[1] = (1/ns).*sumc(sumc(abs(payoff0[.,(int((others[k,1]-1)/ns)*ns+1):(int((others[k,1]-1)/ns+1)*ns)
]' - pa[1]).*pr_others));
	else;	
		pa[1] = (1/ns).*sumc(sumc(payoff0'.*pr_others));	/* assume equiprobable outcomes */
		pv[1] = (1/ns).*sumc(sumc(abs(payoff0' - pa[1]).*pr_others));
	endif;

	lambda[k,1] = lam./pv[1];
	tatt[.,1] = (pv[1]./lam).*tatt0[.,int((k-1)/nsj+1)];
	att[.,1] = selif(tatt[.,1],nsavb[.,signal[k,1]]); 

	i = 2;
	do while i <= t;

		choice[choice0[k,i-1],i-1] = 1;	/* choice0 is ID of strategy chosen */
		payoff = genpay(k,i-1);		/* payoff matrix is for period i-1 choice */

		/* Note that for ease of programming att and nt have been shifted forward by 1 */
		/* In other words att[.,i] should be interpreted as att[.,i-1] in the paper */

		if ((Gi >= 3) and (Gi <= 4));
			pa[i] = (pa[i-1]*(i-1+ns*n0) + sumc((choice[.,i-1].*winner[k,i-1]).*payoff))/(i+ns*n0);
			pv[i] = (pv[i-1]*(i-1+ns*n0) + abs(sumc((choice[.,i-1].*winner[k,i-1]).*payoff) - pa[i-1]))/(i+ns*n0);

			ct[.,i-1] = ct[.,i-1] + choice[.,i-1];
			att[.,i] = ((ct[.,i-1]+n0-1).*selif(tatt[.,i-1],nsavb[.,signal[k,i-1]]) + (choice[.,i-1].*winner[k,i-1]).*payoff)./(ct[.,i-1]+n0);
		else;
			pa[i] = (pa[i-1]*(i-1+ns*n0) + sumc(choice[.,i-1].*payoff))/(i+ns*n0);
			pv[i] = (pv[i-1]*(i-1+ns*n0) + abs(sumc(choice[.,i-1].*payoff) - pa[i-1]))/(i+ns*n0);

			/* as per the PV paper working paper */
			ct[.,i-1] = ct[.,i-1] + choice[.,i-1];
			att[.,i] = ((ct[.,i-1]+n0-1).*selif(tatt[.,i-1],nsavb[.,signal[k,i-1]]) + (choice[.,i-1]).*payoff)./(ct[.,i-1]+n0);
		endif;
		tatt[.,i] = (1-nsavb[.,signal[k,i-1]]).*tatt[.,i-1] + nsavb[.,signal[k,i-1]].*(ones(tns/ns,1).*.att[.,i]);
		att[.,i] = selif(tatt[.,i],nsavb[.,signal[k,i]]);

		ct[.,i] = ct[.,i-1];
		lambda[k,i] = lam./pv[i]; 

		i = i+1;

	endo;

	choice[choice0[k,t],t] = 1; 

	if ((Gi >= 3) and (Gi <= 4)); 
		choice[101,2:t] = zeros(1,t-1);		/* was set to 0 in original program for pBC*/
	endif;

	att = att - median(att[.,.])';
	pr = ln(exp(lambda[k,1:t].*att)+1e-70) - ln(sumc(exp(lambda[k,1:t].*att))'+1e-70);

	ylog[(k-1)*t+1:k*t] = sumc((pr.*choice));

	/* economic value calculation */
	call evprob(pr,k);			/* opponent(s)'s choice probability */

	/* Validation purpose: accumulates statistics */
	if vldn == 1; 
		{tytemp,tymax,tyhit} = valstat(ylog,pr,choice,k);
		ytemp[(k-1)*t+1:k*t] = tytemp; ymax[(k-1)*t+1:k*t] = tymax; yhit[(k-1)*t+1:k*t] = tyhit;
	endif;	

	k = k+1;	
endo;

/* if validation but no economic value calculation, call print-out procedure */
if vldn == 1 and evcall == 0; call prtVldn(ylog,yhit,ymax,ytemp); endif;	

retp(ylog);
endp;

/* End: REL Log-likelihood Function */


/* QRE Log-likelihood Function */

Proc qrellk(x);

local lam, att, choice, payoff, pr, pr_opp, k, i;
local ylog, ymax, ytemp, yhit, tymax, tytemp, tyhit;
local fp_diff, fp_iter, pr_old, pr_tfl, tthmax;
local tatt;

ytemp = zeros(n*t,1); ylog = zeros(n*t,1);
ymax = zeros(n*t,1); yhit = zeros(n*t,1);
pr_tfl = zeros(n+nv,t*max_ns);

/* Parameters */
lam =  u_lam/(1+exp(x[bp+1]));	/* lambda */

if vldn == 0; n= n0[Gi] + nv0[Gi]; endif; 
othmax = zeros(n,t*max_ons); if ((Gi >= 14) and (Gi <= 15)); othmax = zeros(n,t*max_ns); endif;

/* solve for fixed points for the choice probabilities of step 1 thinker */
fp_diff = 1; fp_iter = 1; do while ((fp_diff>=min_diff)AND(fp_iter<=max_iter));
 
	tthmax = simprob(Gi,(1.*(fp_iter.>1)),othmax);	/* simulate opponents' probabilities */
	othmax = othmax.*0; fp_diff = 0;
	pr_old = pr_tfl; 

	k = 1; do while k <= n;

		tns = tns1[k]; ns = ns1[k]; ons = ons1[k];

		/* opponent(s)' choice probabilities */
		pr_opp = reshape(tthmax[k,1:t*ons],t,ons)';		

		tatt = zeros(tns,t);	/* attraction matrix: strategies by game round */
		att = zeros(ns,t);	/* attraction matrix: strategies by game round */	
		choice = zeros(ns,t);	/* choice matrix: strategies by game round */
		pr = (1/ns).*ones(ns,t);	/* choice probability: strategies by game round */
	
		/* attractions */
		i = 1; choice[choice0[k,i],i] = 1;
		payoff = payoff0[.,begpay[k,i]+1:begpay[k,i]+ons];	/* find the right payoff matrix  */

		lambda[k,i] = lam; 
		att[.,i] = payoff*pr_opp[.,i];

		tatt[.,1] = (1./lam).*tatt0[.,int((k-1)/nsj+1)]; 
		att[.,1] = selif(tatt[.,1],nsavb[.,signal[k,1]]); 

		i = 2; do while i <= t;
			choice[choice0[k,i],i] = 1;
			payoff = payoff0[.,begpay[k,i]+1:begpay[k,i]+ons];	/* find the right payoff matrix  */
			lambda[k,i] = lam; 
			att[.,i] = payoff*pr_opp[.,i];

			tatt[.,i] = (1-nsavb[.,signal[k,i]]).*tatt[.,i-1] + nsavb[.,signal[k,i]].*(ones(tns/ns,1).*.att[.,i]);
			att[.,i] = selif(tatt[.,i],nsavb[.,signal[k,i]]);

			i = i+1;
		endo;

		choice[choice0[k,t],t] = 1; 
		att = att - median(att[.,.])';	/* logit form is invariant to constant, shift att so that exp(lam*att) stays within reasonable range */
		pr = (lambda[k,1:t].*att) - ln(sumc(exp(lambda[k,1:t].*att))'+1e-70);

		/* economic value calculation */
		call evprob(pr,k);			/* opponent(s)'s choice probability */
		pr_tfl[k,1:t*ns] = vec(exp(pr))';		/* own choice probability */ 

		k = k+1;	
	endo;

	fp_diff = maxc(vec(abs(pr_tfl - pr_old)));
	fp_iter = fp_iter + 1;
endo;

if vldn == 0; n= n0[Gi]; endif;

tthmax = simprob(Gi,1,othmax);	/* level think-1 */
othmax = othmax.*0; 

k = 1; do while k <= n;

	tns = tns1[k]; ns = ns1[k]; ons = ons1[k];

	/* opponent(s)' choice probabilities */
	pr_opp = reshape(tthmax[k,1:t*ons],t,ons)';		/* level think-1 */

	tatt = zeros(tns,t);	/* attraction matrix: strategies by game round */
	att = zeros(ns,t);	/* attraction matrix: strategies by game round */	
	choice = zeros(ns,t);	/* choice matrix: strategies by game round */
	pr = (1/ns).*ones(ns,t);	/* choice probability: strategies by game round */

	/* attractions */

	i = 1; choice[choice0[k,i],i] = 1;
	payoff = payoff0[.,begpay[k,i]+1:begpay[k,i]+ons];	/* find the right payoff matrix  */
	lambda[k,i] = lam; 
	att[.,i] = payoff*pr_opp[.,i];

		tatt[.,1] = (1./lam).*tatt0[.,int((k-1)/nsj+1)]; 
		att[.,1] = selif(tatt[.,1],nsavb[.,signal[k,1]]); 

	i = 2; do while i <= t;
		choice[choice0[k,i],i] = 1;
		payoff = payoff0[.,begpay[k,i]+1:begpay[k,i]+ons];	/* find the right payoff matrix  */
		lambda[k,i] = lam; 
		att[.,i] = payoff*pr_opp[.,i];

		tatt[.,i] = (1-nsavb[.,signal[k,i]]).*tatt[.,i-1] + nsavb[.,signal[k,i]].*(ones(tns/ns,1).*.att[.,i]);
		att[.,i] = selif(tatt[.,i],nsavb[.,signal[k,i]]);

		i = i+1;
	endo;

	choice[choice0[k,t],t] = 1; 
	att = att - median(att[.,.])';	/* logit form is invariant to constant, shift att so that exp(lam*att) stays within reasonable range */
	pr = (lambda[k,1:t].*att) - ln(sumc(exp(lambda[k,1:t].*att))'+1e-70);

	/* economic value calculation */
	call evprob(pr,k);			/* opponent(s)'s choice probability */
	pr_tfl[k,1:t*ns] = vec(exp(pr))';		/* own choice probability */ 

	if ((Gi >= 3) and (Gi <= 4)); 
		choice[101,2:t] = zeros(1,t-1);		/* was set to 0 in original program for pBC*/
	endif;

	/* each period i stores the same number, to be divided by t */
	ylog[(k-1)*t+1:k*t] = (sumc(pr.*choice));

	/* Validation purpose: accumulates statistics */
	if vldn == 1;

		/* predicted probability */
		pr = ln(reshape(pr_tfl[k,1:t*ns],t,ns)' +1e-70);
		{tytemp,tymax,tyhit} = valstat(ylog,pr,choice,k);	
		ytemp[(k-1)*t+1:k*t] = tytemp; ymax[(k-1)*t+1:k*t] = tymax; yhit[(k-1)*t+1:k*t] = tyhit;
	endif;

	k = k+1;	
endo;

/* if validation but no economic value calculation, call print-out procedure */
if vldn == 1 and evcall == 0; call prtVldn(ylog,yhit,ymax,ytemp); endif;	

retp(ylog);
endp;
/* End: LL function for QRE */





/* Your model likelihood function specification here */

Proc xxxllk(x);

local att, choice, payoff, pr, k, i, lam;
local ylog, ymax, ytemp, yhit, tymax, tytemp, tyhit;
local tatt;

ytemp = zeros(n*t,1); ylog = zeros(n*t,1);
ymax = zeros(n*t,1); yhit = zeros(n*t,1);


/* Your Parameters here: x */


k = 1;
do while k <= n;

	tns = tns1[k]; ns = ns1[k]; ons = ons1[k];

	tatt = zeros(tns,t);	/* attraction matrix: strategies by game round */
	att = zeros(ns,t);	/* attraction matrix: strategies by game round */	
	choice = zeros(ns,t);	/* choice matrix: strategies by game round */




	ylog[(k-1)*t+1:k*t] = sumc((pr.*choice));

	/* economic value calculation */
	call evprob(pr,k);			/* opponent(s)'s choice probability */

	/* Validation purpose: accumulates statistics */
	if vldn == 1; 
		{tytemp,tymax,tyhit} = valstat(ylog,pr,choice,k);
		ytemp[(k-1)*t+1:k*t] = tytemp; ymax[(k-1)*t+1:k*t] = tymax; yhit[(k-1)*t+1:k*t] = tyhit;
	endif;	

	k = k+1;	
endo;

/* if validation but no economic value calculation, call print-out procedure */
if vldn == 1 and evcall == 0; call prtVldn(ylog,yhit,ymax,ytemp); endif;	

retp(ylog);

endp;

/* End: Your model likelihood function specification here */



/* Calculate Initial Value */
Proc(0) = initv;

local m, mm;
m = 1; do while m <= ngrp;

	ns = ns1[(m-1)*nsj+1];	

/*
	att0[.,m] = counts(choice0[((m-1)*nsj+1):(m*nsj),1], seqa(1,1,ns));
	att0[.,m] = att0[.,m] + spp[Gi]/ns;
	att0[.,m] = att0[.,m]./(sumc(att0[.,m]));
	att0[.,m] = ln(att0[.,m]./att0[minindc(att0[.,m]),m]);

	att0[.,m] = ln(att0[.,m]./minc(att0[.,m]));
*/

	tns = tns1[(m-1)*nsj+1];
	mm = 1; do while mm <= cols(nsavb);
		tatt0[((mm-1)*ns+1):(mm*ns),m] = counts(selif(choice0[((m-1)*nsj+1):(m*nsj),1],(signal[((m-1)*nsj+1):(m*nsj),1].==mm)), seqa(1,1,ns));
		tatt0[((mm-1)*ns+1):(mm*ns),m] = tatt0[((mm-1)*ns+1):(mm*ns),m] + spp[Gi]/ns;
		tatt0[((mm-1)*ns+1):(mm*ns),m] = tatt0[((mm-1)*ns+1):(mm*ns),m]./(sumc(tatt0[((mm-1)*ns+1):(mm*ns),m]));


		tatt0[((mm-1)*ns+1):(mm*ns),m] = ln(tatt0[((mm-1)*ns+1):(mm*ns),m]./minc(tatt0[((mm-1)*ns+1):(mm*ns),m]));

		mm = mm+1;
	endo;
	m = m+1;
endo;
endp;


/* Generating the relevant payoff matrix for subject k in round i */

proc genpay(k,i);

local payoff, bd;

payoff = payoff0[1:ns,others[k,i]];

/* pBC Games */
if ((Gi >= 3) and (Gi <= 4));
	if (winner[k,i]);
		bd = (seqa(1,1,ns).>=abs(others[k,i] - twidth[k,i])).*(seqa(1,1,ns).<=abs(others[k,i] + twidth[k,i]));
		if (nwin[k,i] == 1);
			payoff = (1-bd).*payoff + pay.*bd;	/* forgone payoff beyond */
			payoff[choice0[k,i]] = pay;	/* actual payoff */
		else;
			payoff = pay.*bd;
			payoff[abs(others[k,i] - twidth[k,i])] = pay/nwin[k,i];	/* boundary payoff */
			payoff[abs(others[k,i] + twidth[k,i])] = pay/nwin[k,i];	/* boundary payoff */
			payoff[choice0[k,i]] = pay/nwin[k,i];	/* actual payoff */
		endif;
	endif;
endif;	

retp(payoff);
endp;

/* End: Generating the relevant payoff matrix for subject k in round i */


/* Read in data sets */

proc(0) = readdata;

local i, j, rr, Gi, others0, prize, strength, reward, edw, oppid0, oppid1, oppid2;
local winnumber0, winnumber, nwin0, rp, temp1, rro, datbeg, datend;

others0 = {};

Gi = bgame; do while Gi <= ngame; 

	t = t0[Gi];	tv = tv0[Gi]; n = n0[Gi]; nv = nv0[Gi]; tns1 = tns0[Gi].*ones(n+nv,1);
	ns1 = ns0[Gi].*ones(n+nv,1); ons1 = ons0[Gi].*ones(n+nv,1); 
	tns = tns1[1]; ns = ns1[1]; ons = ons1[1]; ngrp = ngrp0[Gi]; nsj = nsj0[Gi];
	begpay = zeros(n+nv,t+tv);		/* begining column of the payoff matrix */

	nsavb = ones(tns,1); signal = ones(n+nv,t+tv);

	if Gi == 1;

		SFile = "c:/gauss/input/cdg.dat"; load indata[70,15]=^SFile;

		choice0 = indata[.,1:15];

		/* Payoff Matrix from Continental Divide (strategy by median)*/

		payoff0 = zeros(ns,ns);
		payoff0[.,1] = 45|48|48|43|35|23|7|-13|-37|-65|-97|-133|-173|-217;
		payoff0[.,2] = 49|53|54|51|44|33|18|-1|-24|-51|-82|-117|-156|-198;
		payoff0[.,3] = 52|58|60|58|52|42|28|11|-11|-37|-66|-100|-137|-179;
		payoff0[.,4] = 55|62|66|65|60|52|40|23|3|-21|-49|-82|-118|-158;
		payoff0[.,5] = 56|65|70|71|69|62|51|37|18|-4|-31|-61|-96|-134;
		payoff0[.,6] = 55|66|74|77|77|72|64|51|35|15|-9|-37|-69|-105;
		payoff0[.,7] = 46|61|72|80|83|82|78|69|57|40|20|-5|-33|-65;
		payoff0[.,8] = -59|-27|1|26|46|62|75|83|88|89|85|78|67|52;
		payoff0[.,9] = -88|-52|-20|8|32|53|69|81|89|94|94|91|83|72;
		payoff0[.,10]= -105|-67|-32|-2|25|47|66|80|91|98|100|99|94|85;
		payoff0[.,11]= -117|-77|-41|-9|19|43|64|80|92|101|105|106|103|95;
		payoff0[.,12]= -127|-86|-48|-14|15|41|63|80|94|104|110|112|110|104;
		payoff0[.,13]= -135|-92|-53|-19|12|39|62|81|96|107|114|118|117|112;
		payoff0[.,14]= -142|-98|-58|-22|10|38|62|82|98|110|119|123|123|120;

		/* conversion to 1 USD */
		payoff0 = 0.01.*payoff0;	

		/* Median at each game group */

		others0 = {
		7	6	6	6	5	5	4	4	4	4	4	4	4	3	4,
		7	7	6	5	5	4	4	4	4	4	4	3	3	3	3,
		11	12	13	13	12	13	13	12	12	13	13	13	13	13	12,
		9	10	11	12	12	12	12	12	12	12	12	12	12	12	12,
		9	8	11	12	12	12	12	12	12	12	12	12	12	12	12,
		7	6	6	7	6	6	6	5	6	6	5	6	6	5	6,
		7	7	6	6	6	5	5	4	6	6	5	5	5	5	4,
		8	9	11	11	11	12	12	13	13	12	12	13	12	13	13,
		8	9	8	9	10	11	12	12	12	12	12	12	12	12	12,
		7	5	4	4	4	4	3	4	3	4	4	5	5	5	4};

		others0 = others0.*.ones(7,1);
		rndev = rndu((n+nv)*evsim,t+tv);
		CFile = "rndev" $+ ftos(Gi,"%*.*lf",1,0); save ^CFILE = rndev; 

	elseif (Gi == 2);

		SFile = "c:/gauss/input/mag.dat";

		/* 54x12: 1=group i.d., 2=subject i.d., 3-12=choice at period 1-10*/
		load indata[54,12]=^SFile; choice0 = indata[.,3:12];

		/* Payoff Matrix from Median Action (strategy by median)*/

		payoff0 = zeros(ns,ns);
		payoff0[.,1]=  0.70| 0.65| 0.50| 0.25| -0.10| -0.55| -1.10;
		payoff0[.,2]=  0.75| 0.80| 0.75| 0.60|  0.35|  0.00| -0.45;
		payoff0[.,3]=  0.70| 0.85| 0.90| 0.85|  0.70|  0.45|  0.10;
		payoff0[.,4]=  0.55| 0.80| 0.95| 1.00|  0.95|  0.80|  0.55;
		payoff0[.,5]=  0.30| 0.65| 0.90| 1.05|  1.10|  1.05|  0.90;
		payoff0[.,6]= -0.05| 0.40| 0.75| 1.00|  1.15|  1.20|  1.15;
		payoff0[.,7]= -0.50| 0.05| 0.50| 0.85|  1.10|  1.25|  1.30;
		payoff0 = payoff0;	/* Already in 1 USD scale */

		/* Median at each game group */

		others0 = (4|5|5|4|4|5);
		others0 = others0.*ones(6,10);
		others0=others0.*.ones(9,1);

		rndev = rndu((n+nv)*evsim,t+tv);
		CFile = "rndev" $+ ftos(Gi,"%*.*lf",1,0); save ^CFILE = rndev; 

	elseif ((Gi == 3)OR(Gi == 4));

		if Gi == 3; SFile = "c:/gauss/input/7expdat.dat";
		elseif (Gi == 4); SFile = "c:/gauss/input/7iexpdat.dat"; endif;
		load indata[98,11]=^SFile;

		pay = 3.5/1.7;			/* payoff for winner: S$ rescaled to 1 USD */

		/* Payoff Matrix for pBC (strategy by target)*/

		payoff0 = zeros(ns,ns);
		payoff0 = pay - 100.*abs(seqa(0,1,ns)'.*ones(ns,ns) - seqa(0,1,ns).*ones(ns,ns));
		payoff0 = 	payoff0.*(payoff0.>0);

		@Winning Number at each game group@

		winnumber0 = zeros(ngrp,t+tv);

		nwin0 = zeros(ngrp,t+tv);
		winner = zeros(n+nv,t+tv);
		choice0 = indata[.,2:11];

		wpbc = indata[.,1]; /* for economic value calculation */

		i = 1; do while i <= ngrp; 
			/* winning number */
			winnumber0[i,.] = meanc(wpbc[(i-1)*nsj+1:i*nsj].*choice0[(i-1)*nsj+1:i*nsj,.])';	
			temp1 = (abs(choice0[(i-1)*nsj+1:i*nsj,.] - winnumber0[i,.]));

			/* if there are two closest numbers, both are winners */	
			temp1 = (temp1.==minc(temp1)');		/* winner(s) */	
			winner[(i-1)*nsj+1:i*nsj,.] = temp1;

			nwin0[i,.] = sumc(winner[(i-1)*nsj+1:i*nsj,.])';		/* number of winners */
			i = i+1;
		endo;

		nwin = nwin0.*.ones(nsj,1);
		winnumber = winnumber0.*.ones(nsj,1);

		/* others is target number */
		others0 = zeros(n+nv,t+tv);
		i = 1; do while i <= (n+nv); 
			temp1 = ones(nsj,1); temp1[i-int((i-1)/nsj)*nsj] = 0;
			others0[i,.] = sumc(temp1.*choice0[int((i-1)/nsj)*nsj+1:int((i-1)/nsj+1)*nsj,.])';
			others0[i,.] = round(wpbc[int((i-1)/nsj)*nsj+1]./(nsj-wpbc[int((i-1)/nsj)*nsj+1]).*others0[i,.]);
			i = i+1;
		endo;

		twidth = round(abs(choice0 - others0));	/* target width for winner */

		choice0 = choice0 + 1; others0 = others0 + 1;	/* shift strategy ID from 0-100 to 1-101 */

		CFile = "wpbc" $+ ftos(Gi,"%*.*lf",1,0);  save ^CFILE = wpbc;
		CFile = "nwin" $+ ftos(Gi,"%*.*lf",1,0);  save ^CFILE = nwin;
		CFile = "twid" $+ ftos(Gi,"%*.*lf",1,0);  save ^CFILE = twidth;
		CFile = "winr" $+ ftos(Gi,"%*.*lf",1,0);  save ^CFILE = winner;
		rndev = rndu((n+nv)*evsim,t+tv);
		CFile = "rndev" $+ ftos(Gi,"%*.*lf",1,0); save ^CFILE = rndev; 

	elseif ((Gi >= 5)AND(Gi <= 9));	/* traveler's dilemma */	

		if (Gi == 5); SFile = "c:/gauss/input/td5.dat"; 
		elseif (Gi == 6); SFile = "c:/gauss/input/td20.dat"; 
		elseif (Gi == 7); SFile = "c:/gauss/input/td25.dat"; 
		elseif (Gi == 8); SFile = "c:/gauss/input/td50.dat"; 
		elseif (Gi == 9); SFile = "c:/gauss/input/td80.dat"; endif;

		rr = (t+tv); load indata[rr,nsj]= ^SFile; indata = indata';
		choice0 = round(indata); choice0 = choice0 - 79;	/* strategy 80 is 1 */

		if (Gi == 5); SFile = "c:/gauss/input/tdo5.dat"; RP = 5; 
		elseif (Gi == 6); SFile = "c:/gauss/input/tdo20.dat"; RP = 20;
		elseif (Gi == 7); SFile = "c:/gauss/input/tdo25.dat"; RP = 25; 
		elseif (Gi == 8); SFile = "c:/gauss/input/tdo50.dat";  RP = 50;
		elseif (Gi == 9); SFile = "c:/gauss/input/tdo80.dat"; RP = 80; endif;  

		/* discretize the strategies */
		load others0[rr,nsj]= ^SFile; others0 = round(others0)'; others0 = others0 - 79;

		payoff0 = zeros(ns,ons);
		payoff0 = lowmat(seqa(1,1,ons)'.*ones(ns,ons) + 79 - RP) + upmat(seqa(1,1,ns).*ones(ns,ons) + 79 + RP);
		payoff0 = diagrv(payoff0,diag(payoff0)./2);
		payoff0 = payoff0./100;		/* rescale from cents to 1 USD */

	elseif ((Gi >= 10)AND(Gi <= 13));

		SFile = "c:/gauss/input/grp" $+ ftos(Gi-9,"%*.*lf",1,0) $+ ".dat"; 
		load indata[800,28]= ^SFile;

		if Gi==10; prize = 5; elseif Gi==11; prize = 5;
		elseif Gi==12; prize = 10; elseif Gi==13; prize = 10; endif;

		choice0 = reshape(indata[.,3],n+nv,t+tv);
		others0 = reshape(indata[.,4],n+nv,t+tv);

		/* needed for fatfree calculation */
		CFile = "Aother" $+ ftos(Gi-9,"%*.*lf",1,0); save ^CFILE = others0; 

		payoff0 = zeros(ns,ns*2);	/* payoffs for row and column players are adjoint */

		if (ns==4);
			/* payoff for 4x4 game */
			/* row player */
			payoff0[1,1 4]=prize*ones(1,2); payoff0[2,3 4]=prize*ones(1,2); payoff0[3,2]=prize;
			payoff0[3,3]=prize/3; payoff0[3,4]=prize/3; payoff0[4,3]=prize*2/3; payoff0[4,4]=prize;
			/* col player: 5 => 1 ....  8 => 4 */
			payoff0[1,6 7 8]=prize*ones(1,3); payoff0[2,5 6 8]=prize*ones(1,3); payoff0[3,5]=prize;
			payoff0[3,7]=prize*2/3; payoff0[3,8]=prize*1/3; payoff0[4,7]=prize*2/3;
			others0[11:20,.] = others0[11:20,.] + 4;	/* adjust col players' pointer to the adjoint payoff */
			begpay[11:20,.] = 4.*ones(10,t+tv);
		elseif (ns==6);
			/* row player */
			payoff0[1,1]=prize; payoff0[3 4 5,2]=prize*ones(3,1); payoff0[2 4 6,3]=prize*ones(3,1);
			payoff0[2 5,4]=prize*ones(2,1); payoff0[2 3 6,5]=prize*ones(3,1);
			payoff0[1 2 5 6,6]=prize*ones(4,1);
			/* col player: 7 => 1 ....  12 => 6 */
			payoff0[1,8:12]=prize*ones(1,5); payoff0[2,7 8 12]=prize*ones(1,3);
			payoff0[3,7 9 11]=prize*ones(1,3); payoff0[4,7 9 10 12]=prize*ones(1,4);
			payoff0[5,7 10 11]=prize*ones(1,3); payoff0[6,9 10]=prize*ones(1,2);
			others0[11:20,.] = others0[11:20,.] + 6;	/* adjust col players' pointer to the adjoint payoff */
			begpay[11:20,.] = 6.*ones(10,t+tv);
		endif;

		payoff0 = payoff0./35;		/* conversion of 35 rupees in 1996-97 rate to a dollar */


	elseif ((Gi == 14)OR(Gi == 15));

		SFile = "c:/gauss/input/patent.dat";

		/* 
		rows = 160*36 = 5760, columns = 10 
		1=trial i.d., 2=group i.d., 3=slice i.d. (each 80 trials), 4=block i.d. (each 10 trials), 
		5=strength of player (0 weak with endowment = 4, 1 strong with endowment = 5), 
		6 = subject i.d., 7 = choice, 8= payoff, 9=other's choice, 10 = other's payoff
		*/

		load indata[5760,10]=^SFile; choice0 = zeros(36,80); others0 = zeros(36,80);
		strength = 0; if (Gi == 14); strength = 1; endif;
		i = 1; do while i <= 5760;
			if strength == indata[i,5];
				/* first strategy is 0 investment, to facilitate indexing, we rename as 1 */
				choice0[((indata[i,2]-1)*18 + indata[i,6]),(fmod(indata[i,1]-1,80)+1)] = indata[i,7]+1; 
				others0[((indata[i,2]-1)*18 + indata[i,6]),(fmod(indata[i,1]-1,80)+1)] = indata[i,9]+1;
			endif;
			i = i+1;
		endo;

		/* Payoff Matrix for Patent Race (strategy by others)*/
		/* Number of strategies: 6 for strong player, 5 for weak */		

		reward = 10;
		if (Gi == 14); 
			edw = 5; 
			payoff0 = ones(ns,ons); payoff0 = seqa(edw,-1,ns).*payoff0; 
			payoff0 = payoff0 + reward.*(seqa(0,1,ns).*ones(ns,ons) .> seqa(0,1,ons)'.*ones(ns,ons));
		else; 
			edw = 4;	
			payoff0 = ones(ns,ons); payoff0 = seqa(edw,-1,ns).*payoff0; 
			payoff0 = payoff0 + reward.*(seqa(0,1,ns).*ones(ns,ons) .> seqa(0,1,ons)'.*ones(ns,ons));
		endif;			
		payoff0 = payoff0./80;		/* payoff conversion to 1 USD */


	elseif ((Gi >= 16)AND(Gi <= 18));	/* manual pot games */	

		SFile = "c:/gauss/input/potm" $+ ftos(3*(Gi-15),"%*.*lf",1,0) $+ ".dat"; 

		rr = (t+tv)*nsj*ngrp; load indata[rr,3]= ^SFile;

		choice0 = reshape(indata[.,3],n+nv,t+tv);
		payoff0 = zeros(ns,ons);
		payoff0[1,.] = (nsj/3)./seqa(1,1,nsj)';
		payoff0[2,.] = (2*nsj/3)./rev(seqa(1,1,nsj))';
		/* No conversion needed, already in 1 USD scale */	

		/* Others refers to # of other choices to small pot 
		(index advanced by 1 since Gauss can't take 0 as index) */

		others0 = zeros(n+nv,t+tv);
		i = 1; do while i <= ngrp;
			j = 1; do while j <= (t+tv);
			/* 1 is small pot and 2 is large pot */
			others0[(i-1)*nsj+1:i*nsj,j] = counts(choice0[(i-1)*nsj+1:i*nsj,j],1).*ones(nsj,1) - (choice0[(i-1)*nsj+1:i*nsj,j].==1) + 1;
			j = j+1; endo;
		i = i + 1; endo;	

	elseif ((Gi >= 19)AND(Gi <= 22));	/* computer pot games */	

		if (Gi == 19); SFile = "c:/gauss/input/potc3.dat"; 
		elseif (Gi == 20); SFile = "c:/gauss/input/potc6.dat"; 
		elseif (Gi == 21); SFile = "c:/gauss/input/potc18a.dat"; 
		elseif (Gi == 22); SFile = "c:/gauss/input/potc18b.dat"; endif;

		rr = (t+tv)*nsj*ngrp; load indata[rr,10]= ^SFile;

		/* Note that the payoff for computer games is 3 times as big as those in manual */
		payoff0 = zeros(ns,ons);
		payoff0[1,.] = (nsj)./seqa(1,1,nsj)';
		payoff0[2,.] = (2*nsj)./rev(seqa(1,1,nsj))';
	
		choice0 = reshape(indata[.,6],t+tv,nsj)';
		others0 = reshape(indata[.,7],t+tv,nsj)'- (choice0.==1) + 1;

	elseif ((Gi >= 23)AND(Gi <= 24));	/* Nagel */

		if (Gi == 23); SFile = "c:/gauss/input/Uc50a.dat"; else; SFile = "c:/gauss/input/Uc50b.dat"; endif;

		load indata[800,10] = ^SFile;

		nsavb = zeros(tns,5); nsavb[1:2,1] = ones(2,1); nsavb[3:4,2] = ones(2,1); 
		nsavb[5:6,3] = ones(2,1); nsavb[7:8,4] = ones(2,1); nsavb[9:10,5] = ones(2,1);
		signal = reshape(indata[.,7],n+nv,t+tv);

		payoff0 = zeros(ns,5*ons);
		payoff0[1,.] = 90~90~80~80~70~70~60~60~50~50;
		payoff0[2,.] = ones(1,5).*.(0~80);

		choice0 = reshape(indata[.,5],n+nv,t+tv);
		others0 = reshape(indata[.,6],n+nv,t+tv);

		/* needed for fatfree calculation */
		CFile = "Aother" $+ ftos(Gi-9,"%*.*lf",1,0); save ^CFILE = others0; 

		begpay = reshape(indata[.,8],n+nv,t+tv);
		begpay = 2.*(begpay.==80) + 4.*(begpay.==70) + 6.*(begpay.==60) + 8.*(begpay.==50);

		others0 = begpay + others0;
		payoff0 = payoff0./330;		/* rescale from payoff to spanish peseta to 1 USD */

		oppid0 = zeros(n+nv,t+tv);
		oppid1 = reshape(indata[.,3],n+nv,t+tv);

		i = 1; do while i <= 8;
			oppid2 = zeros(n+nv,t+tv);
			oppid2[1:8,.] = oppid1[1:8,.] - oppid1[i,.]; oppid2[i,.] = oppid2[i,.] + 1;
			oppid0[i,.] = seqa(1,1,8)'*(oppid2[1:8,.].==0);
			oppid2[9:16,.] = oppid1[9:16,.] - oppid1[8+i,.]; oppid2[8+i,.] = oppid2[8+i,.] + 1;
			oppid0[8+i,.] = seqa(9,1,8)'*(oppid2[9:16,.].==0);
			i = i +1;
		endo;	

		CFile = "oppid" $+ ftos(Gi,"%*.*lf",1,0); save ^CFILE = oppid0; 

	elseif ((Gi >= 25)AND(Gi <= 28));	/* Sovik */


		if (Gi == 25); SFile = "c:/gauss/input/Svk1.dat"; 
		elseif (Gi == 26); SFile = "c:/gauss/input/Svk2.dat"; 
		elseif (Gi == 27); SFile = "c:/gauss/input/Svk3.dat"; 
		else; SFile = "c:/gauss/input/Svk4.dat"; endif;

		load indata[72,8] = ^SFile;

		nsavb = zeros(tns,5); nsavb[1:2,1] = ones(2,1); nsavb[3:4,2] = ones(2,1); 
		nsavb[5:6,3] = ones(2,1); nsavb[7:8,4] = ones(2,1); nsavb[9:10,5] = ones(2,1);

		signal = indata[1:24,2]'; 
		signal = (ones(6,1).*.(1.*((signal.==1)+ (signal.==2)) + 2.*((signal.==3)+ (signal.==4))))|(ones(6,1).*.(3.*(signal.==1) + 4.*((signal.==2)+ (signal.==3)) + 5.*(signal.==4)));

		/* 1 = No and 2 = Yes */

		choice0 = (indata[25:48,3:8]'|indata[49:72,3:8]');
		choice0 = choice0 + 1;
		others0 = zeros(n+nv,t+tv);
		oppid0 = zeros(n+nv,t+tv);

		i = 1; do while i <= 6;
			others0[1:6,.] = others0[1:6,.] + (indata[1:24,3:8]'.==(i+6)).*choice0[i+6,.];
			others0[i+6,.] = others0[i+6,.] + sumc((indata[1:24,3:8]'.==(i+6)).*choice0[1:6,.])';

			oppid0[1:6,.] = oppid0[1:6,.] + (i+6).*(indata[1:24,3:8]'.==(i+6));
			oppid0[i+6,.] = oppid0[i+6,.] + sumc((indata[1:24,3:8]'.==(i+6)).*seqa(1,1,6))';

			i = i+1;
		endo;
		CFile = "oppid" $+ ftos(Gi,"%*.*lf",1,0); save ^CFILE = oppid0; 

		payoff0 = ones(ns,8*ons);
		payoff0[2,2 4 6 8 10 12 14 16] = 32~-28~20~-16~-32~28~-20~16;  

		/* needed for fatfree calculation */
		CFile = "Aother" $+ ftos(Gi-9,"%*.*lf",1,0); save ^CFILE = others0; 

		begpay = ones(12,1).*.indata[1:24,2]'; 
		begpay = 2.*(begpay.==2) + 4.*(begpay.==3) + 6.*(begpay.==4);
		begpay[7:12,.] = begpay[7:12,.] + 4*ons;

		others0 = begpay + others0;

		payoff0 = payoff0.*(2.5*0.0065);		/* rescale from 1 unit payoff to 2.5 ptas, 100 ptas is USD 0.65 (from her paper)*/

	elseif ((Gi >= 30)AND(Gi <= 30));	/* New game */


	endif;

	CFile = "choice" $+ ftos(Gi,"%*.*lf",1,0);  save ^CFILE = choice0;
	CFile = "payoff" $+ ftos(Gi,"%*.*lf",1,0);  save ^CFILE = payoff0;
	CFile = "others" $+ ftos(Gi,"%*.*lf",1,0);  save ^CFILE = others0;

	CFile = "ns" $+ ftos(Gi,"%*.*lf",1,0);  save ^CFILE = ns1;
	CFile = "ons" $+ ftos(Gi,"%*.*lf",1,0);  save ^CFILE = ons1;
	CFile = "begpay" $+ ftos(Gi,"%*.*lf",1,0);  save ^CFILE = begpay;

	CFile = "tns" $+ ftos(Gi,"%*.*lf",1,0);  save ^CFILE = tns1;
	CFile = "nsavb" $+ ftos(Gi,"%*.*lf",1,0);  save ^CFILE = nsavb;
	CFile = "signal" $+ ftos(Gi,"%*.*lf",1,0);  save ^CFILE = signal;

	Gi = Gi + 1;
endo;

retp;
endp;

/* end reading in data sets */
