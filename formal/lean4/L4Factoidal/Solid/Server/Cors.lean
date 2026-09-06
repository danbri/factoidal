/-
L4Factoidal.Solid.Server.Cors — the Cross-Origin Resource Sharing header
fields a Solid server generates.

Wraps: `L4Factoidal.LWS.Operations.step`, whose response this decorates.
Adds: everything — the LWS draft says nothing about CORS.

Source: https://solidproject.org/TR/protocol §8.1 CORS Server, verbatim:

  "A server MUST implement the CORS protocol [FETCH] such that browsers
  allow Solid apps to send any request and combination of request headers to
  the server, and allow the app to read any response and response headers
  received from the server."

  "Whenever a server receives an HTTP request containing a valid Origin
  header [RFC6454], the server MUST respond with the appropriate
  Access-Control-* header fields."

  "The server MUST set the Access-Control-Allow-Origin header field value to
  the valid Origin header field value from the request and list Origin in
  the Vary header field value."

  "The server MUST make all used response headers readable for the Solid app
  through Access-Control-Expose-Headers."

  "A server MUST also support the HTTP OPTIONS method such that it can
  respond appropriately to CORS preflight requests."

  "Servers SHOULD explicitly enumerate all used response header fields under
  Access-Control-Expose-Headers rather than resorting to *."

  "Servers SHOULD also explicitly list Accept under
  Access-Control-Allow-Headers."

Web Access Control §5.3.4, verbatim:

  "When a server participates in the CORS protocol [FETCH], the server MUST
  include WAC-Allow in the Access-Control-Expose-Headers field-value in the
  HTTP response."
-/
import L4Factoidal.LWS.Operations

namespace L4Factoidal.Solid.Server

open L4Factoidal.HTTP (Request Response)

/-- Every response header field a Solid app has to be able to read.
§8.1 says to enumerate them rather than to answer `*`, and WAC §5.3.4 puts
`WAC-Allow` in the list. -/
def exposedHeaders : List String :=
  [ "Accept-Patch", "Accept-Post", "Accept-Put", "Allow", "Content-Type"
  , "ETag", "Last-Modified", "Link", "Location", "Updates-Via", "WAC-Allow" ]

/-- Request header fields a preflight is answered for. `Accept` is listed
explicitly, which §8.1 says a server SHOULD do. -/
def allowedRequestHeaders : List String :=
  [ "Accept", "Authorization", "Content-Type", "DPoP", "If-Match"
  , "If-None-Match", "Link", "Slug" ]

def allowedMethods : List String :=
  ["GET", "HEAD", "OPTIONS", "POST", "PUT", "PATCH", "DELETE"]

/-- The `Access-Control-*` and `Vary` fields for a request that carried an
`Origin`. An absent `Origin` gets no CORS fields at all — §8.1 conditions
them on "an HTTP request containing a valid Origin header". -/
def corsHeaders (origin : Option String) (preflight : Bool) :
    List (String × String) :=
  match origin with
  | none => []
  | some o =>
      [ ("access-control-allow-origin", o)
      , ("vary", "Origin")
      , ("access-control-allow-credentials", "true")
      , ("access-control-expose-headers", String.intercalate ", " exposedHeaders) ]
      ++ (if preflight then
            [ ("access-control-allow-methods", String.intercalate ", " allowedMethods)
            , ("access-control-allow-headers", String.intercalate ", " allowedRequestHeaders)
            , ("access-control-max-age", "86400") ]
          else [])

/-- Is this an `OPTIONS` request that a browser sent as a CORS preflight?
The Fetch standard marks one with `Access-Control-Request-Method`. -/
def isPreflight (r : Request) : Bool :=
  r.method == "OPTIONS" && (r.header? "access-control-request-method").isSome

/-- Add the CORS fields to a response. -/
def withCors (r : Request) (resp : Response) : Response :=
  { resp with headers := resp.headers ++ corsHeaders (r.header? "origin") (isPreflight r) }

end L4Factoidal.Solid.Server
