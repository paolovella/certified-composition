let done = 0 ;
check downstream ;
for i = 5 { if done { skip } else { access downstream ; let done = ok ; for d = 10 { skip } } } ;
if done { emit html "ok" } else { emit html "gave_up" }
