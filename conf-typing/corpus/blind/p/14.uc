for j = 10 {
  if allowed {
    check job ;
    access job ;
    emit log "job_processed"
  } else {
    emit log "job_skipped"
  }
}
