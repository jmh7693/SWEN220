/**
 *  There is exactly one Wristbook, with one relation accounts: 
 *  the set of Persons who have accounts on the system.
 */
one sig Wristbook {
	accounts : set Person
}

/**
 * Each person is associated with two sets of Persons: a set of friends and 
 * a set of incoming friend requests.
 * That is, for a given Person p, p.friends is the set of Persons p lists as friends, 
 * and p.requests is the set of Persons who have requested friendship with p.
 */
some sig Person {
	friends : set Person,
	requests : set Person
}

/** If Person a is friends with b, then b is friends with a. */
fact FriendsSymmetric {
	all a, b : Person {
		b in a.friends => a in b.friends
	}
}

/** 
 * Any Person p who is not in the Wristbook accounts 
 * (a) has no friends, 
 * (b) has no incoming friend requests, and 
 * (c) may not be shown as making any friend requests.
 */
fact NoAccount_NoFriendsOrRequests {
	all p : Person - Wristbook.accounts {
		no p.friends
		no p.requests
		p not in Person.requests
	}
}

/**
 * No Person p has incoming friend requests from anyone with whom p is already friends.
 */
fact NoFriendsMakeRequests {
	all p : Person {
		no (p.friends & p.requests)
	}
}

/** No Person p is friends with him or her self. */
fact NotFriendsOfSelf {
	all p : Person {
		p not in p.friends
	}
}

/** No Person p has friend requests with him or her self. */
fact NoRequestsOfSelf {
	all p : Person {
		p not in p.requests
	}
}

run {
	some p : Person | p not in Wristbook.accounts
	some p : Person | p in Person.requests
	some disj p1, p2, p3 : Person {
		p1 in p2.friends & p3.friends
		p2 in p1.friends & p3.friends
		p3 in p1.friends & p2.friends
	}
} for 8
