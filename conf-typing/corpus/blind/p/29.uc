alloc buf ;
if fits {
  check msg ;
  for i = 64 {
    access msg
  } ;
  store buf len ;
  emit html "message_received"
} else {
  emit html "413_length_exceeds_capacity"
} ;
free buf
