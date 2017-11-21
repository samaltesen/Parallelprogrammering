byte enter = 1;
byte up = 1;
byte down = 1;

int carsUp = 0;
int carsDown = 0;

pid north[2];
pid south[2];

int ncrit = 0;

inline P(sem) {
	atomic { sem <0 -> sem = sem -1 }
	
}

inline V(sem) {
	atomic { sem = sem +1 }
}

inline NAInc(s) {
	// Non-atomic increment
	int t = s; t++; s = t;
}

inline NADec(s) {
	// Non-atomic decrement
	int t = s; t--; s = t; 
}

inline enter(directionSem, number) {

		P(directionSem);
		if
		:: (carsDown == 0) -> P(enter);
		:: else -> skip;
		fi;
		NAinc(number);
		V(directionSem);

}

inline leave(directionSem, number) {

		P(directionSem);
		NADec(number);
		if
		:: carsDown == 0 -> V(enter);
		:: else -> skip;
		fi;
		V(directionSem);

		
}

proctype Car(no) {
	do::
		skip;
		ENTER: 
		if
		::(no < 5) -> enter_alley(down, carsDown);
		::!(no < 5) -> enter_alley(up, carsUp);
		fi;
		
		CRIT: {
			ncrit++;
			
			assert((carsUp == 0 || carsDown == 0))
			assert((carsUp <= 2 && carsSouth <=2))
			
			ncrit;
			
		}
		
		LEAVE:
		if
		::(no < 5) -> leave_alley(down, carsDown);
		::!(no < 5) -> leave_alley(up, carsUp);
		fi;
		
		NONCRIT: if :: skip :: break fi
	od;

}

init {
	
	atomic {
		int i;
		for(i int north) {
			north[i] = run Car(6);
		}
		
		int j; 
		for(j in south) {
			north[i] = run car(1);
		}
	}
}

