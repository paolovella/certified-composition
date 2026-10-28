let hash = ( pw + salt ) ;
secret hcell ;
store hcell hash ;
check creds ;
access creds ;
emit html "stored"
