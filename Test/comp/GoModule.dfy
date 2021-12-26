// RUN: %dafny /compile:3 /spillTargetCode:2 "%s" /compileTarget:go > "%t"
// note: putting /compileTarget:go after "%s" overrides user-provided option
// RUN: %diff "%s.expect" "%t"

// "url" is a built-in package, so it should be accessible to the
// test suite without further requirements on the setup.
module {:extern "url", "net/url"} URL {
    class URL {
        var {:extern "Host"} host: string
        var {:extern "Path"} pathname: string
        var {:extern "RawQuery"} search: string
    }

    trait {:extern "", "error"} Error { }

    method {:extern "url", "Parse"} Parse(address: string) returns (url: URL, error: Error?)
}

method TryUrl(address: string) {
    var u, e := URL.Parse(address);
    if (e != null) {
        print "Parse error: ", e, "\n";
    } else {
        print "The address ", address, "\n";
        print "has the following parts:\n";
        print "host: ", u.host, "\n";
        print "pathname: ", u.pathname, "\n";
        print "search: ", u.search, "\n";
    }
}

method Main() {
    TryUrl("http://localhost:8080/default.htm?year=1915&month=august&day=29");
    TryUrl("http://localhost:8080/default.htm%");
}
