# oak

## syntax

The Oak syntax is very simple. There are only a few constructs, so rather than 
list them all here, let's just work through an example.

```elm
Lexer: type 
  = input:    string 
  & current:  char 
  & position: int 
  & readPos:  int 
```

There are a couple of things going on in this example.
This syntax defines a type, which is composed of other
types. In this case, we are essentially crafting a class.

```elm
Lexer: type
```
The type declaration begins with a label, which is used to
identify the type, as well as to establish visibility. As
in Go, a capital letter will indicate a public type, 
otherwise the type will be private.

The colon denotes a type annotation. The type of Lexer is
another type. This makes sense; classes are also types.

```elm
Lexer: type 
  = input:    string 
```

In the next line, we assign to the Lexer label. We are stating
that Lexer is a public type, which has a property named 'input'
of type 'string'. The following lines are all the same. They 
begin with '&' and are followed by a property name, and finally
a type annotation:

```elm
Lexer: type 
  = input:    string 
  & current:  char 
  & position: int 
  & readPos:  int 
```

In conclusion, we have type which is an intersection of a collection
of other named types. This is type composition, and the primary 
construct of the language. 

The language also provides syntactic sugar for using types in a 
more familiar manner. Instead of using intersection '&', a 
property dot notation is provided:

```elm
Lexer: type 
  .input:    string 
  .current:  char
  .position: int
  .readPos:  int
```



## builtins

- map 
- filter 
- reduce
- take
- limit 
- zip
- transform



## Random shit


```fs
type StatusCode = 
    | InformationalCode
    | SuccessCode
    | RedirectionCode
    | ClientErrorCode 
    | ServerErrorCode

type InformationalCode = 
    | Continue // 100 
    | SwitchingProtocols // 101
    | Processing // 102 (WebDAV)

type SuccessCode =
    | Ok // 200
    | Created // 201
    | Accepted // 202
    | NonAuthoritiveInformation // 203
    | NoContent // 204
    | ResetContent // 205
    | PartialContent // 206
    | MultiStatus // 207 (WebDAV)
    | AlreadyReported // 208 (WebDAV)
    | ImUsed // 226

type RedirectionCode =
    | MultipleChoices // 300
    



type Continue = 100
type SwitchingProtocols = 101
type Processing = 102

type Ok = 200
type Created = 201
type Accepted = 202
type NonAuthoritiveInformation = 203
type NoContent = 204
type ResetContent = 205
type PartialContent = 206
type MultiStatus = 207
type AlreadyReported = 208
type ImUsed = 226

type MultipleChoices = 300
type MovedPermanently = 301
type Found = 302
type SeeOther = 303
type NotModified = 304
type UseProxy = 305
// 306 removed
type TemporaryRedirect = 307
// 308 experimental

type BadRequest = 400
type Unauthorized = 401
type PaymentRequired = 402
type Forbidden = 403
type NotFound = 404
type MethodNotAllowed = 405
type NotAcceptable = 406
type ProxyAuthenticationRequired = 407
type RequestTimeout = 408
type Conflict = 409
type Gone = 410
type LengthRequired = 411
type PreconditionFailed = 412
type RequestEntityTooLarge = 413
type RequestUriTooLong = 414
type UnsupportedMediaType = 415
type RequestedRangeNotSatisfiable = 416
type ExpectationFailed = 417
type ImATeaPot = 418 // rfc 2324, not sure if teapot is one or two words
// 419 unused
type EnhanceYourCalm = 420 // twitter
// 421 unused
type UnprocessableEntity = 422 // WebDAV
type Locked = 423 // WebDAV
type FailedDependency = 424 // WebDAV
// 425 unused 
type UpgradeRequired = 426
// 427 unused
type PreconditionRequired = 428
type TooManyRequests = 429 
// 430 unused
type RequestHeaderFieldsTooLarge = 431
// 432 - 443 unused
type NoResponse = 444 // Nginx
// 445 - 448 unused
type RetryWith = 449 // Microsoft
type BlockByWindowsParentalControls = 450 // Microsoft
type UnavailableForLegalReasons = 451
// 452 - 498 unused
type ClientClosedRequest = 499 // Nginx

type InternalServerError = 500
type NotImplemented = 501
type BadGateway = 502
type ServiceUnavailable = 503
type GatewayTimeout = 504
type HttpVersionNotSupported = 505
// 506 experimental 
type InsufficientStorage = 507 // WebDAV
type LoopDetected = 508 // WebDAV
type BandwidthLimitExceeded = 509 // Apache
type NotExtended = 510 
type NetworkAuthenticationRequired = 511
// 512 - 597 unused
type NetworkReadTimeoutError = 598
type NetworkConnectTimeoutError = 599
```
