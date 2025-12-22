// SIGNATURES (Class mapping)

sig User {
	var makes : set Trip
}

sig BikePath{
	var status: one PathStatus,
	var contains: set Trip,
	isComposedOf: some PathSegment
} 

sig Trip{
	has: one PerformanceMetrics,
	detects: set Obstacle,
	status: one PathStatus,
	var currentState: one State
}

sig PathSegment{
	var contains: set Obstacle,
	initialPoint: one Position,
	endPoint: one Position
}

sig Obstacle{}

sig PerformanceMetrics{
	weather: set WeatherCondition
}

enum PathStatus{Optimal, Medium, Sufficient, RequiresMaintenance}
enum WeatherCondition{Sunny, Cloudy, Rainy, Windy, Stomy, Snowny}
enum State{Inactive, Active, Public}

sig Position{}


// FACTS

// A bike path does not have the same path segments with other bike path
fact {
	all path1: BikePath, path2: BikePath|
		always ((path1 != path2 and path1.isComposedOf = path2.isComposedOf) implies path1.isComposedOf = none)
}
// A trip perfomed in a path is always in that path
fact {
	all path: BikePath |
		always ( path.contains in path.contains' )
}
// The status of a BikePath doesn't change unless a trip on it is published
fact {
	all path: BikePath |
		always (
			(path.status' = path.status) implies
      			(all trip: path.contains |
			        (trip.currentState != Inactive) implies (trip.currentState = trip.currentState'))
			else(
				(one trip: path.contains |
			       	  trip.currentState = Active and trip.currentState'= Public and trip.status = path.status'
				)
			)
		)
}


// Any ACTIVE trip is performed JUST on one bikePath
fact{
	all trip: Trip |
		always ( (trip.currentState != Inactive) implies (
			one path: BikePath |
				trip in path.contains) )
}
// Any INACTIVE trip is not related with any bike path
fact{
	all path: BikePath, trip: Trip |
		always ( (trip in path.contains) implies (trip.currentState != Inactive) )
}
// Any ACTIVE trip is made by exactly 1 User
fact {
	all trip: Trip |
		always ( (trip.currentState != Inactive) implies (
			one user: User |
				trip in user.makes)  )
}
// Any trip has its onw performMetrics
fact{
	all metric: PerformanceMetrics |
		always (one trip: Trip |
				metric in trip.has)	
}
// Any  INACTIVE trip has not yet been made by an user
fact{
	all trip: Trip |
		always ( (trip.currentState = Inactive) implies (trip not in User.makes) )
}
//Current state of a trip should remain logically  
fact{
	all trip:Trip | {
		always( trip.currentState = Inactive
				implies
				historically  trip.currentState = Inactive )
		always( trip.currentState = Inactive
				implies
				eventually  trip.currentState = Active )
		always( trip.currentState = Active
				implies
				after always ( trip.currentState = Active or trip.currentState = Public) )
		always( trip.currentState = Public
				implies
				(once  trip.currentState = Active) and (after always  trip.currentState = Public) )
	}
}


//Any path segment is part of a bike path
fact{
	all segment: PathSegment |
		always (segment in BikePath.isComposedOf)
}
// A obstacle reported on a segment is always in that segment
fact {
	all segment: BikePath |
		always ( segment.contains in segment.contains' )
}
//Any segment cannot have same intial and end position
fact{
	all segment: PathSegment |
		always (segment.initialPoint != segment.endPoint)
}

//The location segments of a bike path should be continuous
fact{
	all path: BikePath |
		always (#path.isComposedOf = 1
				or
				all segment1: path.isComposedOf|
					((one segment2:path.isComposedOf | 
						segment1!=segment2 and segment1.endPoint = segment2.initialPoint)
					or
					 (one segment2:path.isComposedOf | 
						segment1!=segment2 and segment1.initialPoint = segment2.endPoint)
					)
		)
}



//Any obstacle must be on JUST one bike path segment
fact{
	all o: Obstacle |
		always( (one segment: PathSegment |
			o in segment.contains)
			or
			o not in PathSegment.contains)
}
//Any obstacle must be reported in JUST one trip
fact{
	all o: Obstacle |
		always ( one trip: Trip |
			o in trip.detects )
}
// A trip report an obstacle in a segment of the Bike Path where the ACTIVE trip was taken 
fact {
	all o: Obstacle, trip: Trip |
		always ( (o in trip.detects and trip.currentState != Inactive) implies (
			one path: BikePath | 
				trip in path.contains and
				o in path.isComposedOf.contains
		) )
}
// Any obstacle reported on an INACTIVE trip is not in a path segment
fact {
	all o: Obstacle, trip: Trip|
		always ( (trip.currentState = Inactive and o in trip.detects) implies (o not in BikePath.isComposedOf.contains) )
}

// A user made a trip forever
fact{
	all user: User |
		always (user.makes in user.makes')
} 


// PREDICATES/FUNCTIONS

// A user records a new bike path he has taken
pred makeTrip[ user: User, path: BikePath]{
	one trip: Trip  | {
		trip.currentState = Inactive 

		// Trip made on a bike path
 		path.contains' = path.contains +  trip
		// Trip made by the user
		user.makes' = user.makes + trip
		// Obstacles detected in the trip on the path segments
		all obstacle: trip.detects |
			one segment: path.isComposedOf |
				segment.contains' = segment.contains + obstacle
		//Mark trip as recorded
		trip.currentState'  = Active
		all t: Trip - trip | t.currentState' = t.currentState
	}
}

// A user publish a bike path he has alredy recorded
pred publishTrip[ user: User ]{
	one trip: user.makes | {
		trip.currentState = Active
		
		//Mark trip as public
		all t: Trip - trip | t.currentState' = t.currentState
		trip.currentState'   = Public
		//Next step perform update

		one path: BikePath |
			(trip in path.contains) implies (after updatePath[trip, path])
	}
}

// The bike path status is updated
pred updatePath[trip: Trip , path: BikePath ]{
	(path.status != trip.status) implies (
		path.status' = trip.status
	)
}

// Helper function: One step without doing nothing
pred doNothing{
	User' = User
	BikePath' = BikePath
	Trip' = Trip
	PathSegment' = PathSegment
	Obstacle' = Obstacle
	PerformanceMetrics' = PerformanceMetrics
	Position' = Position
}

//Helper functions: get active and inactive trips
fun InactiveTrips : set Trip { {t: Trip | t.currentState = Inactive} }
fun ActiveOnlyTrips : set Trip { {t: Trip | t.currentState = Active} }


// One status change per step
fact OneTripStateChangePerStep {
	always lone t: Trip | t.currentState' != t.currentState
}


// GOALS VERIFICATION

// G1
pred ShowNewRecord [t:  Trip ] {
	t.currentState = Inactive
	t.currentState' = Active
	#t.detects = 1
}


// G2 - G3
assert  NoTripWithoutUser {
	all trip: Trip - InactiveTrips |
		always( one user: User |
				trip in user.makes )
}
pred  ShowUserTrips [u: User]{
	#u.makes >2
	#u.makes.detects=3
}


//G4
pred  ShowPublishRecord [t:  Trip ] {
	t.currentState = Active
	t.currentState' = Public
	#t.detects = 1
}


//G5
assert NoBikePathWithoutStatusAndSegments{
	all path: BikePath |
		always(path.status != none and path.isComposedOf!=none and  path.isComposedOf.initialPoint!=none and path.isComposedOf.endPoint!=none)
}


//G6
pred  ShowChangeStatusBikePaths [u:  User] {
	one t: u.makes | 
		{
		one path: BikePath | {
		t in path.contains 
		path.status != t.status
		}
		t.currentState = Active 
		t.currentState' = Public
		#t.detects = 1
	}
	some t1:Trip | {
		t1.currentState= Inactive
	}
	some t1:Trip | {
		t1.currentState= Active
	}
	#BikePath = 2
	#User = 2
}


// RUNS
//Note: When active comment the system simulation part

//check NoTripWithoutUser for 15 but 3 steps
//run ShowNewRecord for 3 but exactly 2 steps
//run ShowUserTrips for 4 but exactly 2 steps
//run ShowPublishRecord for 3 but exactly 2 steps
//check NoBikePathWithoutStatusAndSegments for 15 but 3 steps
//run ShowChangeStatusBikePaths for 5 but exactly 15 steps

// SYSTEM SIMULATION

//Initialization
 //All paths private (Recorded or not yet recorded)
fact{
	all trip: Trip |
		trip.currentState = Inactive or trip.currentState = Active
}
//Some paths recorded and not recorded
fact InitDiverse {
	(some t: Trip | t.currentState = Inactive)
	and
	(some t: Trip | t.currentState = Active)
}

fact systemBehavior{
	#ActiveOnlyTrips = 2
	#User = 2
	always (
		(some InactiveTrips or some ActiveOnlyTrips) 
		implies 
		(
			( one user: User, path:BikePath | makeTrip[ user ,  path ])
			or
			(one user: User | publishTrip[ user ])
		)else
		(some InactiveTrips)
		implies
		(
			( one user: User, path:BikePath | makeTrip[ user ,  path ])
		) else
		(some ActiveOnlyTrips)
		implies
		(
			(one user: User | publishTrip[ user ])
		) else
		doNothing
	)
}	
