check conns ;
for i = 8 { access conns ; if open { emit log "closed" } else { skip } }
