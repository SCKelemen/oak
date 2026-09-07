package main

import (
    "bytes"
    "crypto/sha256"
    "encoding/hex"
    "encoding/json"
    "fmt"
    "io"
    "os"
    "strconv"
)

func digest(data string) string { h:=sha256.Sum256([]byte(data));return hex.EncodeToString(h[:]) }
// decode rejects duplicate keys before typed decoding can silently overwrite them.
func decode(data []byte,target any) error {
    if len(data)>55_000_000{return fmt.Errorf("JSON input limit")}
    d:=json.NewDecoder(bytes.NewReader(data));d.UseNumber()
    var scan func(int) error
    scan=func(depth int) error {
        if depth>128{return fmt.Errorf("JSON nesting limit")}
        token,e:=d.Token();if e!=nil{return e}
        delimiter,ok:=token.(json.Delim);if !ok{return nil}
        if delimiter=='{' {
            keys:=map[string]bool{}
            for d.More(){t,e:=d.Token();if e!=nil{return e};key,ok:=t.(string);if !ok||keys[key]{return fmt.Errorf("invalid/duplicate JSON key")};keys[key]=true;if e:=scan(depth+1);e!=nil{return e}}
        } else if delimiter=='[' {for d.More(){if e:=scan(depth+1);e!=nil{return e}}} else{return fmt.Errorf("unexpected JSON delimiter")}
        _,e=d.Token();return e
    }
    if e:=scan(0);e!=nil{return e};if _,e:=d.Token();e!=io.EOF{return fmt.Errorf("trailing JSON")}
    d=json.NewDecoder(bytes.NewReader(data));d.UseNumber();d.DisallowUnknownFields();return d.Decode(target)
}
func readJSON(path string,target any) error {
    f,e:=os.Open(path);if e!=nil{return e};defer f.Close()
    b,e:=io.ReadAll(io.LimitReader(f,55_000_001));if e!=nil{return e};return decode(b,target)
}
func jsonText(v any) string {b,e:=json.MarshalIndent(v,"","  ");if e!=nil{panic(e)};return string(b)+"\n"}
func number(v any)(int,error){
    switch n:=v.(type){case int:return n,nil;case int64:if n>=-2147483647&&n<=2147483647{return int(n),nil};case json.Number:return strconv.Atoi(string(n))}
    return 0,fmt.Errorf("integer required, got %T",v)
}
