if hostallowed {
  emit location ( "https://app.example.com/" ++ san ( input ) )
} else {
  emit location "https://app.example.com/"
}
