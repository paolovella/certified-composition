if isrestart { emit sh "systemctl_restart_app" } else { if isstatus { emit sh "systemctl_status_app" } else { emit html "unknown_command" } }
