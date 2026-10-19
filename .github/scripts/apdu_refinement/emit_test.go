package apduextract

import (
    "flag"
    "testing"
)

var sourceRootFlag = flag.String("apdu-source-root", "", "owner-authenticated published Oak module root")
var fixtureFlag = flag.String("apdu-fixture", "", "exact immutable qualified fixture directory")
var outputFlag = flag.String("apdu-output", "", "fresh private empty owner-reserved evidence directory")

func TestAPDUParserExtractionEmit(t *testing.T) {
    if *sourceRootFlag == "" || *fixtureFlag == "" || *outputFlag == "" {
        t.Fatal("all three exact owner-bound APDU path flags are required; no default or skip")
    }
    if err := Extract(*sourceRootFlag, *fixtureFlag, *outputFlag); err != nil {
        t.Fatal(err)
    }
}
