module transactionsWithHistory

-- This a demo, IRL block chain history is what counts

open transaction[SpawnedCoin]
open event[TimeState]

sig SpawnedCoin {}

sig TimeState {
	leaves : some Transaction + SpawnedCoin
}

sig newTranaction extends event/Event {}{
	pre.leaves in post.leaves								-- we don't forget old transactions
	post.leaves.^(hash.old) in pre.leaves		-- we must build off preexisting transactions
	pre.leaves != post.leaves							-- we must do _something_ new
}

fact {
	TimeState.leaves = Transaction + SpawnedCoin	-- all transaction in trace
	first.leaves in SpawnedCoin									-- begin with only spawned coins
}

assert AcylicTransactionHistory {
	no ^(hash.old) & iden
}
check AcylicTransactionHistory for 8

assert NoFraud { -- the number of coins in circulation == number of coins spawned thus far
	all t : TimeState {
		#(t.leaves - t.leaves.hash.old) = #(SpawnedCoin & t.leaves)
	}
}
check NoCheating for 8
