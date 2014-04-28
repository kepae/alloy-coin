module asymmetricKey

abstract sig Key {}

sig PubKey extends Key {
//	priv : one PrivKey
}

sig PrivKey extends Key {
	pub : one PubKey
}

fact asdf {
//	priv = ~pub
}

fact one2one {
	-- 1-1 between private and pub keys
	pub.~pub in iden
//	(~pub).pub in iden
	univ.pub = PubKey
}
