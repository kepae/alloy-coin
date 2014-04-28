module event [TimeState]

open util/ordering [TimeState]

abstract sig Event {
	pre, post: TimeState,
}{
	post = pre.next
}

fact EventTraces {
	all t: TimeState - last | one e: Event | e.pre = t
}

run {} for 3
