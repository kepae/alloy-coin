
open asymmetricKey

sig Wallet {
	pub: one PubKey,
	priv: one PrivKey
}

fact {
	all w : Wallet | w.priv.pub = w.pub
	all disj a,b : Wallet |
		{a.priv != b.priv
		a.pub != b.pub}
}

abstract sig Transaction {}

one sig GTransaction extends Transaction {}

sig VTransaction extends Transaction {
	newOwner : one Wallet,
	oldOwner : one Wallet,
	signed: one PrivKey,
	verify: one PubKey,
	hash: one Transaction - this
}

fact {
	all t :VTransaction | t.oldOwner.pub = t.signed.pub and t.signed.pub = t.verify
}

run { } for 9
