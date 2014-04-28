module event [TimeState]

open util/ordering [TimeState]

sig Event {
	pre, post: TimeState,
}

fact EventTraces {
	all t: TimeState - last | some e: Event | e.pre = t and e.post = t.next
	last not in Event.pre
}

run {} for 3
