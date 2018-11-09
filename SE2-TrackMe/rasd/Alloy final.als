open util/integer
open util/time

--------------------------------------------------sig ------------------------------------------------


abstract sig User{
	id: Int
}
{ id > 0}

sig Individual extends User {
	has: Data,
	associatedTo: set Request,
	enrolls: set Run,
	seesRun: set Run,
	SOSMessage : set SOS
}

sig Data{
	dataOf : Individual,
	hasThreshold : Threshold,
	hasValue : Int
}
{hasValue >0}

one sig ExternalPartner{
	SOSReceived : set SOS
}

sig SOS{
	SOSAssociatedTo : Individual,
	SOSAbout : Data
}

sig Threshold{
	hasThresholdValue : Int
}
{hasThresholdValue >0}


abstract sig Request{
	status: Status
}

sig IndividualRequest extends Request{
	concerns : Individual
}

sig GroupRequest extends Request {}

abstract sig Status{}

one sig Accepted extends Status{}

one sig Refused extends Status{}

sig ThirdParty{
	requires : set Request,
	seesData : set Data,
	creates : set Run
}

sig Date{}   

sig Run{ 
	title: Int,  
	date: Date, 
	startTime: Time, 
	endTime: Time, 
	enrolledBy: some Individual, 
	hasPath: Path, 
} 
--the beginning of a run must precede its end 
{gt[endTime, startTime]} 

sig Path{
 hasNode: some Node
}

sig Node{}


--------------------------------------------------facts------------------------------------------------
------------------DATA4HELP--------------------
-- Individuals have a unique ID
fact{
 all disj  u1, u2: User | u1.id != u2.id 
}

--Every request is required by a third party
fact{
	all r : Request | one t : ThirdParty | r in t.requires
}
--Every individual has its own data
fact{
	all disj i1, i2 : Individual | i1.has != i2.has
}

--Every data is linked to one individual
fact {
	all d: Data | one i: Individual | d in i.has
}

--Requests concers only individuals
fact {
	concerns = ~associatedTo
}

--If a request is accepted the third party sees the data and vivecersa
fact{
	all t: ThirdParty, r: Request | (r in t.requires and r.status = Accepted) <=> r.concerns.has in t.seesData
}

--Data are seen by third parties if and only if the request has been previously accepted by the individual
fact {
	all t:ThirdParty, d : Data | d in t.seesData <=> 
	( some i : Individual, r : Request | d in i.has and i in t.requires.concerns and r.status = Accepted  and r in t.requires)
}


------------------AUTOMATEDSOS----------------
fact {
	SOSAssociatedTo = ~SOSMessage
}

fact {
	dataOf = ~ has
}
--Every SOS is received by the external partner
fact{
	all s: SOS | s in ExternalPartner.SOSReceived
}
--Every threshold is associated to one health status
fact{
	all t : Threshold | one d : Data | t in d.hasThreshold
}
--If the value of data is above  its threshold, there are no SOS 
fact {
	all d: Data | d.hasValue >= d.hasThreshold.hasThresholdValue <=> no s : SOS | s.SOSAbout = d
}
--There are no different SOS referring to the same data
fact{
	no disj s1,s2 : SOS | s1.SOSAbout = s2.SOSAbout
}

--Every SOS is associated to the individual that has the same data of the SOS
fact{
	all s : SOS | s.SOSAssociatedTo = s.SOSAbout.dataOf
}

------------------TRACK4RUN--------------------

--Runs can be enrolled only by individuals
fact{
	enrolls = ~ enrolledBy
}
--A run can be created by only one Third party
fact {
	all r: Run | one t : ThirdParty | t.creates = r
}
--An individual cannot see a run for which he/she has enrolled and viceversa
fact{
	all i: Individual | i.enrolls & i.seesRun = none
}
--There are no two different runs with the same date and with a time overlap that cross a same node 
fact{
	no disj r1, r2 : Run | r1.date = r2.date and  ( (lte[r1.startTime, r2.startTime] and gte[r1.endTime, r2.endTime]) or 
										  (lte[r1.startTime, r2.startTime] and lte[r1.endTime, r2.endTime]) ) and 
										   r1.hasPath.hasNode  & r2.hasPath.hasNode != none
}

--Every node belongs to at least one path
fact{
	all n: Node| some p: Path | n in p.hasNode
}

--Every path is associated to a run
fact {
	all p: Path | some r : Run | r.hasPath = p
}

--Every path has at least two nodes
fact{
	all p : Path | some disj n1, n2 : Node | n1 in p.hasNode and n2 in p.hasNode
}

--------------------------------------------------predicates------------------------------------------------
--Add a request to a third party
pred addRequest [r :IndividualRequest, t, t' : ThirdParty]{
	t'.requires = t.requires + r
}
--Accept an individual request
pred acceptRequest[r:IndividualRequest]{
	r.status = Accepted
}

pred addRun[r: Run, t,t': ThirdParty]{
	t'.creates = t.creates + r
}

--predicate to show only the part concerning the requests
pred showRequest{
	#ThirdParty>=2
	#Individual >= 3
	#Run = 0
	#SOS = 0
	#IndividualRequest >= 1
}

--predicate to show only the part concerning the SOS
pred showSOS{
	#ThirdParty=0
	#Run=0
	#Individual >= 3
	#SOS >=1
	some d : Data | d.hasValue >d.hasThreshold.hasThresholdValue
}


pred showRun{
	#ThirdParty>=1
	#Individual >= 2
	#Run >= 2
	#SOS = 0
	#IndividualRequest = 0
}

pred show {}
--------------------------------------------------assertion------------------------------------------------
--If a third party sends a new request and this request is accepted then the third party can see the required data
assert ThirdPartySeesData {
	all r: IndividualRequest, t, t':ThirdParty | addRequest[r,t,t'] and acceptRequest[r] implies r.concerns.has in  t'.seesData 
}

--run showRun
check  ThirdPartySeesData  for 15





