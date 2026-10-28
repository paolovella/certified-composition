if hosta { emit location ( "https://a.example.com/" ++ san ( input ) ) } else { if hostb { emit location ( "https://b.example.com/" ++ san ( input ) ) } else { emit html "invalid_redirect" } }
