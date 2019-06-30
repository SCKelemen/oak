package main

import (
	"fmt"
	"os"
	"os/user"

	"github.com/SCKelemen/oak/repl"
)

func main() {
	usr, err := user.Current()
	if err != nil {
		panic(err)
	}

	fmt.Printf("Hello %s, welcome to Oak 🌳\n", usr.Username)
	repl.Start(os.Stdin, os.Stdout)
}
