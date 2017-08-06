module teamSchedule

/*
* TEAM SCHEDULE FORMAL SPECIFICATION
* For Team Schedule source code, see:
*	https://github.com/TeamScheduler/team-scheduler
*/
---------------------------SIGNATURES---------------------------
abstract sig User{
	userSchedule: one UserSchedule,
	changes: set Change
}
sig Member extends User{}
sig Admin extends User{}

abstract sig Schedule{}
sig UserSchedule extends Schedule{}
sig TeamSchedule extends Schedule{
	teamSchedule: set UserSchedule
}

sig Team {
	admin: one Admin,
	members: set  Member,
	teamSchedule: one TeamSchedule,
	changesLog: set Change,
	tags: set Tag
}

sig Tag{
	tagged: some User
}

sig Change{}

---------------------------FACTS---------------------------
fact noOrphans{
	all a:Admin | one a.~admin
	all m:Member | one m.~members
	all ts:TeamSchedule | one ts.~teamSchedule
	all us:UserSchedule | one us.~userSchedule
	all t:Tag | one t.~tags
	all c:Change | one c.~changes
	all c:Change | one c.~changesLog
}

fact teamSchedule{
	all u:Member, t:Team| (u in t.members) <=> (u.userSchedule in t.teamSchedule.teamSchedule)
	all u:Admin, t:Team| (u = t.admin) <=> (u.userSchedule in t.teamSchedule.teamSchedule)
}


fact tags{
	all t:Tag, tm:Team, m:Member| (m in tm.members) and (m in t.tagged) => (t in tm.tags)
	all t:Tag, tm:Team, a:Admin| (a = tm.admin) and (a in t.tagged) => (t in tm.tags)
}

---------------------------FUNCTIONS---------------------------
fact changes{
	all c:Change, tm:Team| c in tm.changesLog => (c in getChanges[tm]) 
}

fun getChanges[tm:Team]: set Change{
	tm.admin.changes + tm.members.changes
}

---------------------------ASSERTS---------------------------
assert oneAdminPerTeam {
	all aa:Admin, ab:Admin, ta:Team| aa = ta.admin and ab=ta.admin => aa = ab
	#Admin = #Team
}

assert noTagWithNoone{
	no t:Tag| #t.tagged = 0
}

check oneAdminPerTeam for 10
check noTagWithNoone for 10

pred show[]{
#Tag = 4
#Team = 3
#changes = 3
}

run show for 10


