if oprestart {
  emit sh "service_app_restart"
} else {
  if opstatus {
    emit sh "service_app_status"
  } else {
    emit log "rejected_unknown_command"
  }
}
