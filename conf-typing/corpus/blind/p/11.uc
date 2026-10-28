check downstream ;
for attempt = 5 {
  access downstream ;
  for d = 3 {
    skip
  }
} ;
emit log "retries_done"
