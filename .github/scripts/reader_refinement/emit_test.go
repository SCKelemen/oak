package readerextract

import (
    "flag"
    "testing"
)

var sourceRootFlag = flag.String("reader-source-root", "", "owner-authenticated published Oak module root")
var fixtureFlag = flag.String("reader-fixture", "", "exact immutable qualified fixture directory")
var outputFlag = flag.String("reader-output", "", "fresh private empty owner-reserved evidence directory")

func TestBoundedReaderExtractionEmit(t *testing.T) {
    if *sourceRootFlag == "" || *fixtureFlag == "" || *outputFlag == "" {
        t.Fatal("all three exact owner-bound reader path flags are required; no default or skip")
    }
    if err := Extract(*sourceRootFlag, *fixtureFlag, *outputFlag); err != nil {
        t.Fatal(err)
    }
}
