module transactionsWithHistory
/*
	
*/

-- This a demo, IRL block chain history is what counts

open transaction
open event[TimeState]

sig TimeState {
	thusFar : some Transaction
}

sig newTransaction extends event/Event {}{
	pre.thusFar in post.thusFar							-- we don't forget old transactions
	post.thusFar.^(hash.old) in pre.thusFar		-- we must build off preexisting transactions
	pre.thusFar != post.thusFar						-- we must do _something_ new
}

fact {
	TimeState.thusFar = Transaction					-- all transaction in the trace
	first.thusFar in GenesisTransaction				-- begin with only spawned coins
}

fact { -- no double spending
	(hash.old).~(hash.old) in iden
}


/*
	Cyclic transactions, ie where following the trail of hashes results in a cycle
	can only be created when a number of transactions are proposed/created
	at the same time. [Also a fixpoint of sorts in the hashing alogorithm needs
	to be found, which is rarely hard to do, and something that may not even exist.]

	Since we mandate that transactions must be "based" off previous transactions,
	we have made it not possible to propose such a cycle.
*/
check AcylicTransactionHistory {
	no ^(hash.old) & iden
} for 8

check NoFraud {
	all t : TimeState {
		-- the number of coins in circulation == number of coins spawned thus far
		#(t.thusFar - t.thusFar.hash.old) = #(GenesisTransaction & t.thusFar)
	}
} for 6

run {some Transaction }
