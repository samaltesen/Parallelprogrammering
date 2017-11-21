int enter = 1;
int up = 0;
int down = 0;
int delayedDown = 0;
int delayedUp = 0;
int nrUp = 0;
int nrDown = 0;

#define carUp 1
#define carDown 5

inline sem_P(sem) {
	atomic { sem <0 -> sem = sem -1 }
	
}

inline sem_V( sem) {
	atomic { sem = sem +1 }
}

inline alley_enter(no) {

	if
	:: no < 5 ->
		sem_P(enter);
		if
		:: nrUp > 0 ->
			delayedDown++;
			sem_V(enter);
			sem_P(down);
		fi;
		nrDown++;
		if
		::delayedDown > 0 ->
			delayedDown--;
			sem_V(down);
		:: else ->
			sem_V(enter);
		fi;
	:: else ->
		sem_P(enter);
		if
		:: nrDown > 0 ->
			delayedUp++;
			sem_V(enter);
			sem_P(up);
		fi;
		nrUp++;
		if
		::delayedUp > 0 ->
			delayedUp--;
			sem_V(Up);
		:: else ->
			sem_V(enter);
		fi;
	fi;
		
		
}

inline alley_leave(no) {
	if
	:: no < 5 ->
		sem_P(enter);
		nrDown--;
		if
		:: nrDown == 0 ->
		:: delayedUp >0 ->
			delayedUp--;
			sem_V(Up);
			
		:: else ->
			sem_V(enter);
	::else -> 
		sem_P(enter);
		nrUp--;
		if
		:: nrUp == 0 ->
		:: delayedDown >0 ->
			delayedDown--;
			sem_V(down);
			
		:: else ->
			sem_V(enter);
		fi;
	fi;
			
}

proctype Car(no) {
	S0:
	do :: 
		skip;
		ENTER:
		if
		:: (no < 5) -> alley_enter(
		alley_enter(carUp);
		alley_leave(carUp);
	od
}

active [4] proctype carDown() {
	do
	:: alley_enter(carDown);
		alley_leave(carDown);
	od
}
