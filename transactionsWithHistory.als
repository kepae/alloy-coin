module transactionsWithHistory

-- This a demo, IRL block chain history is what counts

open transaction
open event[TimeState]

sig TimeState {
	leaves : some Transaction
}

sig newTransaction extends event/Event {}{
	pre.leaves in post.leaves								-- we don't forget old transactions
	post.leaves.^(hash.old) in pre.leaves		-- we must build off preexisting transactions
	pre.leaves != post.leaves							-- we must do _something_ new
}

fact {
	TimeState.leaves = Transaction					-- all transaction in trace
	first.leaves in GenesisTransaction				-- begin with only spawned coins
}

fact { -- no double spending
	(hash.old).~(hash.old) in iden
}



check AcylicTransactionHistory {
	no ^(hash.old) & iden
} for 8

check NoFraud { -- the number of coins in circulation == number of coins spawned thus far
	all t : TimeState {
		#(t.leaves - t.leaves.hash.old) = #(GenesisTransaction & t.leaves)
	}
} for 6

run {some Transaction }
