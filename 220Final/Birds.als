/*
 * Months are ordered with the tag 'mo'.
 * This means one can use the notation mo/function to
 * get the version of function applicable to type Month.
 * Example: mo/nexts[Jan] is the set of months following Jan.
 */
open util/ordering[Month] as mo

/*
 * The months and the pet birds.
 */
enum Month {Jan, Feb, Mar, Apr}
enum Bird {Lorikeet, Parakeet, Macaw, Parrot}

/*
 * Each girl has a month in which she made her
 * purchase and the pet bird she bought.
 */
abstract sig Girl{
	when : Month,
	pet : Bird
}
one sig Mary, Laura, Pam, Sally extends Girl{}

/*
 * Each girl has a month and pet that differs from
 * every other girl.
 */
fact OneToOne {
	Month = Girl.when
	Bird = Girl.pet
}

 /*
  * Fact 1 - Pam's pet is the lorikeet
  */
fact F1 {
	Pam.pet = Lorikeet
}

 /*
  * Fact 2 - Laura's pet is either the bird bought in February or the parakeet.
  * NOTE: This clue also tells us something about the relationship between 
  * the February bird and the parakeet.
  */
fact F2 {
	Laura.when = Feb || Laura.pet = Parakeet
}

 /*
  * Fact 3 - Laura's pet was bought sometime after Sally's pet.
  */
fact F3 {
	Laura.when in nexts[Sally.when]
}

 /*
  * Fact 4 - The lorikeet was bought sometime after the parakeet.
  */
fact F4 {
	let girl1 = pet.Lorikeet {
		let girl2 = pet.Parakeet {
			next[girl2.when] = girl1.when
		} 
	}
}

 /*
  * Fact 5 - Of the bird bought in March and Mary's pet, 
  * one is the macaw and the other is the lorikeet.
  */
fact F5 {
	one g : Girl | (g.when = Mar && g != Mary) && ( ((g.pet = Lorikeet) && (Mary.pet = Macaw)) || ((g.pet = Macaw) && (Mary.pet = Lorikeet)))
}

run{}
