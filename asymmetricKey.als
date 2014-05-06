module asymmetricKey
/*
	a basic model of assymetric keys.
	we have unique public-private key pairs

	priv = ~pub 
	so not too much use having both
*/

abstract sig Key {}

sig PubKey extends Key {}

sig PrivKey extends Key {
	pub : one PubKey
}

fact one2one {
	-- 1-1 between private and pub keys
	pub.~pub in iden
	univ.pub = PubKey
}
