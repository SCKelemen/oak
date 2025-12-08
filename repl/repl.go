package repl

import (
	"bufio"
	"fmt"
	"io"
	"os"
	"strings"

	"golang.org/x/term"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/evaluator"
	"github.com/SCKelemen/oak/object"
	"github.com/SCKelemen/oak/parser"
	"github.com/SCKelemen/oak/scanner"
	"github.com/SCKelemen/oak/typechecker"
)

const PROMPT = "🌳> "
const CONTINUATION_PROMPT = "  > "

// History stores command history
type History struct {
	lines []string
	index int
}

func NewHistory() *History {
	return &History{
		lines: make([]string, 0),
		index: -1,
	}
}

func (h *History) Add(line string) {
	if line == "" {
		return
	}
	// Don't add duplicate consecutive entries
	if len(h.lines) > 0 && h.lines[len(h.lines)-1] == line {
		return
	}
	h.lines = append(h.lines, line)
	h.index = len(h.lines)
}

func (h *History) Previous() string {
	if len(h.lines) == 0 {
		return ""
	}
	if h.index > 0 {
		h.index--
	}
	if h.index >= 0 && h.index < len(h.lines) {
		return h.lines[h.index]
	}
	return ""
}

func (h *History) Next() string {
	if len(h.lines) == 0 {
		return ""
	}
	if h.index < len(h.lines)-1 {
		h.index++
		return h.lines[h.index]
	}
	h.index = len(h.lines)
	return ""
}

func (h *History) Reset() {
	h.index = len(h.lines)
}

// readLineWithHistory reads a line with history support and cursor movement
func readLineWithHistory(prompt string, history *History, in *os.File, out *os.File) (string, error) {
	// Check if we're in a terminal
	if !term.IsTerminal(int(in.Fd())) {
		// Fall back to simple scanner for non-terminal input
		scanner := bufio.NewScanner(in)
		fmt.Fprint(out, prompt)
		if !scanner.Scan() {
			return "", io.EOF
		}
		return scanner.Text(), nil
	}

	// Enable raw mode for terminal control
	oldState, err := term.MakeRaw(int(in.Fd()))
	if err != nil {
		// Fall back to simple scanner
		scanner := bufio.NewScanner(in)
		fmt.Fprint(out, prompt)
		if !scanner.Scan() {
			return "", io.EOF
		}
		return scanner.Text(), nil
	}
	defer func() {
		term.Restore(int(in.Fd()), oldState)
		// After restoring terminal state, ensure cursor is at the start of a new line
		// This fixes the issue where prompts appear indented when there's no output
		fmt.Fprint(out, "\r")
	}()

	var line strings.Builder
	var cursorPos int
	var historyLine string

	fmt.Fprint(out, prompt)

	buf := make([]byte, 1)
	for {
		n, err := in.Read(buf)
		if err != nil || n == 0 {
			return "", err
		}

		char := buf[0]

		// Handle special keys
		if char == 3 { // Ctrl-C
			fmt.Fprint(out, "^C\n")
			return "", fmt.Errorf("interrupted")
		}

		if char == 4 { // Ctrl-D (EOF)
			if line.Len() == 0 {
				return "", io.EOF
			}
		}

		// Handle escape sequences (arrow keys)
		if char == 27 { // ESC
			// Read the next bytes to determine the key
			seq := make([]byte, 2)
			n, _ := in.Read(seq)
			if n < 2 || seq[0] != '[' {
				// Not a recognized escape sequence, ignore
				continue
			}
			if seq[0] == '[' {
				switch seq[1] {
				case 'A': // Up arrow - history previous
					historyLine = history.Previous()
					if historyLine != "" {
						// Clear current line
						fmt.Fprint(out, "\r\033[K")
						line.Reset()
						line.WriteString(historyLine)
						cursorPos = len(historyLine)
						fmt.Fprint(out, prompt+historyLine)
					}
					continue
				case 'B': // Down arrow - history next
					historyLine = history.Next()
					// Clear current line
					fmt.Fprint(out, "\r\033[K")
					line.Reset()
					if historyLine != "" {
						line.WriteString(historyLine)
						cursorPos = len(historyLine)
						fmt.Fprint(out, prompt+historyLine)
					} else {
						cursorPos = 0
						fmt.Fprint(out, prompt)
					}
					continue
				case 'C': // Right arrow - move cursor right
					if cursorPos < line.Len() {
						cursorPos++
						fmt.Fprint(out, "\033[C") // Move cursor right
					}
					continue
				case 'D': // Left arrow - move cursor left
					if cursorPos > 0 {
						cursorPos--
						fmt.Fprint(out, "\033[D") // Move cursor left
					}
					continue
				}
			}
		}

		// Handle Enter
		if char == '\r' || char == '\n' {
			// Print newline and ensure cursor is at the start of a fresh line
			// Use \r\n to move to start of line, then new line
			fmt.Fprint(out, "\r\n")
			result := line.String()
			if result != "" {
				history.Add(result)
			}
			// Ensure output is flushed before returning
			out.Sync()
			return result, nil
		}

		// Handle backspace
		if char == 127 || char == 8 { // Backspace or Ctrl-H
			if cursorPos > 0 {
				// Remove character at cursor position
				lineStr := line.String()
				newLine := lineStr[:cursorPos-1] + lineStr[cursorPos:]
				line.Reset()
				line.WriteString(newLine)
				cursorPos--
				// Redraw line
				fmt.Fprint(out, "\r\033[K") // Clear line
				fmt.Fprint(out, prompt+newLine)
				// Move cursor to correct position
				if cursorPos < len(newLine) {
					fmt.Fprint(out, "\033[", len(newLine)-cursorPos, "D")
				}
			}
			continue
		}

		// Handle regular characters
		if char >= 32 && char < 127 {
			lineStr := line.String()
			// Insert character at cursor position
			newLine := lineStr[:cursorPos] + string(char) + lineStr[cursorPos:]
			line.Reset()
			line.WriteString(newLine)
			cursorPos++
			// Redraw line from cursor position
			fmt.Fprint(out, string(char))
			if cursorPos < len(newLine) {
				// Redraw rest of line
				fmt.Fprint(out, newLine[cursorPos:])
				// Move cursor back to correct position after the inserted char
				remaining := len(newLine) - cursorPos
				if remaining > 0 {
					fmt.Fprintf(out, "\033[%dD", remaining)
				}
			}
		}
	}
}

// hasLineContinuation checks if a line ends with backslash (\) indicating continuation
func hasLineContinuation(line string) bool {
	trimmed := strings.TrimRight(line, " \t")
	return strings.HasSuffix(trimmed, "\\")
}

// removeLineContinuation removes trailing backslash and whitespace from a line
func removeLineContinuation(line string) string {
	trimmed := strings.TrimRight(line, " \t")
	if strings.HasSuffix(trimmed, "\\") {
		return strings.TrimRight(trimmed[:len(trimmed)-1], " \t")
	}
	return line
}

func Start(in io.Reader, out io.Writer) {
	history := NewHistory()
	env := object.NewEnvironment()
	typeChecker := typechecker.New(env)

	// Try to get file descriptors for terminal control
	var inFile *os.File
	var outFile *os.File

	if f, ok := in.(*os.File); ok {
		inFile = f
	} else {
		// Fall back to stdin
		inFile = os.Stdin
	}

	if f, ok := out.(*os.File); ok {
		outFile = f
	} else {
		// Fall back to stdout
		outFile = os.Stdout
	}

	for {
		// Read multiline input
		var inputLines []string
		var fullInput strings.Builder

		var lastHadContinuation bool
		for {
			var line string
			var err error

			if len(inputLines) == 0 {
				line, err = readLineWithHistory(PROMPT, history, inFile, outFile)
			} else {
				line, err = readLineWithHistory(CONTINUATION_PROMPT, history, inFile, outFile)
			}

			if err == io.EOF {
				fmt.Fprintf(out, "\nGoodbye!\n")
				return
			}
			if err != nil {
				// On error (like Ctrl-C), reset and continue
				history.Reset()
				continue
			}

			// Check if this line has a continuation marker
			hasContinuation := hasLineContinuation(line)
			processedLine := line
			if hasContinuation {
				// Remove the backslash and whitespace
				processedLine = removeLineContinuation(line)
			}

			// Add the processed line to input
			inputLines = append(inputLines, line) // Store original for history
			if len(inputLines) == 1 {
				fullInput.WriteString(processedLine)
			} else {
				// If previous line had continuation, join with space; otherwise newline
				if lastHadContinuation {
					fullInput.WriteString(" ")
					fullInput.WriteString(strings.TrimLeft(processedLine, " \t"))
				} else {
					fullInput.WriteString("\n")
					fullInput.WriteString(processedLine)
				}
			}

			// Update state for next iteration
			lastHadContinuation = hasContinuation

			// If this line has continuation, continue reading
			if hasContinuation {
				continue
			}

			// Try parsing to see if input is complete
			currentInput := fullInput.String()
			lxr := scanner.New(currentInput)
			p := parser.New(lxr)
			_ = p.ParseProgram()

			// If parsing succeeds, we're done
			if len(p.Errors()) == 0 {
				break
			}

			// If we have syntax errors, check if they suggest incomplete input
			if suggestsIncomplete(p.Errors()) {
				continue // Continue reading
			}

			// If we get here, we have errors but they don't suggest incomplete input
			// Break and let the parser report the errors
			break
		}

		input := fullInput.String()
		if strings.TrimSpace(input) == "" {
			continue
		}

		// Parse and evaluate
		lxr := scanner.New(input)
		p := parser.New(lxr)
		program := p.ParseProgram()

		if len(p.Errors()) != 0 {
			printParserErrors(out, p.Errors())
			continue
		}

		// Check for REPL commands
		if len(program.Statements) > 0 {
			if replCmd, ok := program.Statements[0].(*ast.REPLCommand); ok {
				switch replCmd.Name {
				case "exit", "quit":
					fmt.Fprintf(out, "Goodbye!\n")
					return
				case "help":
					fmt.Fprintf(out, "Oak REPL Commands:\n")
					fmt.Fprintf(out, "  :exit, :quit     - Exit the REPL\n")
					fmt.Fprintf(out, "  :help            - Show this help message\n")
					fmt.Fprintf(out, "  :clear           - Clear the screen\n")
					fmt.Fprintf(out, "  :reset           - Reset the environment\n")
					fmt.Fprintf(out, "  :typeof(expr)    - Show the type of an expression\n")
					fmt.Fprintf(out, "  :ptrsize(size)   - Set size of ptr/uptr (32 or 64)\n")
					fmt.Fprintf(out, "  :ptrsize()       - Print current ptr/uptr size\n")
					fmt.Fprintf(out, "  :intsize(size)   - Set size of int/uint (32 or 64)\n")
					fmt.Fprintf(out, "  :intsize()       - Print current int/uint size\n")
					fmt.Fprintf(out, "\n")
					fmt.Fprintf(out, "Multiline input: End a line with \\ to continue on the next line\n")
					fmt.Fprintf(out, "  Example: Color: type = \\\n")
					fmt.Fprintf(out, "            | Red | Green | Blue\n")
					continue
				case "clear":
					fmt.Fprintf(out, "\033[2J\033[H")
					continue
				case "reset":
					env = object.NewEnvironment()
					typeChecker = typechecker.New(env)
					fmt.Fprintf(out, "Environment reset.\n")
					continue
				case "typeof":
					if len(replCmd.Args) == 0 {
						fmt.Fprintf(out, "Usage: :typeof(expression)\n")
						continue
					}
					expr := replCmd.Args[0]
					typeChecker.ClearErrors()
					var exprType typechecker.Type
					exprType = typeChecker.ParseTypeExpression(expr)
					if exprType == nil {
						typeChecker.ClearErrors()
						exprType = typeChecker.CheckExpression(expr)
					}
					if len(typeChecker.Errors()) > 0 {
						fmt.Fprintf(out, "Type errors:\n")
						for _, err := range typeChecker.Errors() {
							fmt.Fprintf(out, "  %s\n", err)
						}
					} else if exprType != nil {
						fmt.Fprintf(out, "%s\n", exprType.String())
					} else {
						fmt.Fprintf(out, "unknown type\n")
					}
					continue
				case "ptrsize":
					if len(replCmd.Args) == 0 {
						fmt.Fprintf(out, "ptr/uptr size: %d bits\n", typeChecker.GetPtrSize())
					} else if len(replCmd.Args) == 1 {
						if intLit, ok := replCmd.Args[0].(*ast.IntegerLiteral); ok {
							size := int(intLit.Value)
							if size == 32 || size == 64 {
								typeChecker.SetPtrSize(size)
								fmt.Fprintf(out, "ptr/uptr size set to %d bits\n", size)
							} else {
								fmt.Fprintf(out, "Error: ptrsize must be 32 or 64, got %d\n", size)
							}
						} else {
							fmt.Fprintf(out, "Error: ptrsize argument must be an integer literal\n")
						}
					} else {
						fmt.Fprintf(out, "Usage: :ptrsize() or :ptrsize(32) or :ptrsize(64)\n")
					}
					continue
				case "intsize":
					if len(replCmd.Args) == 0 {
						fmt.Fprintf(out, "int/uint size: %d bits\n", typeChecker.GetIntSize())
					} else if len(replCmd.Args) == 1 {
						if intLit, ok := replCmd.Args[0].(*ast.IntegerLiteral); ok {
							size := int(intLit.Value)
							if size == 32 || size == 64 {
								typeChecker.SetIntSize(size)
								fmt.Fprintf(out, "int/uint size set to %d bits\n", size)
							} else {
								fmt.Fprintf(out, "Error: intsize must be 32 or 64, got %d\n", size)
							}
						} else {
							fmt.Fprintf(out, "Error: intsize argument must be an integer literal\n")
						}
					} else {
						fmt.Fprintf(out, "Usage: :intsize() or :intsize(32) or :intsize(64)\n")
					}
					continue
				}
			}
		}

		typeChecker.ClearErrors()
		typeChecker.CheckProgram(program)
		if len(typeChecker.Errors()) != 0 {
			for _, msg := range typeChecker.Errors() {
				io.WriteString(out, "\t[type error] "+msg+"\n")
			}
			continue
		}

		val := evaluator.Eval(program, env)
		if val != nil {
			if val.Type() == object.ERROR_OBJ {
				io.WriteString(out, val.Inspect())
				io.WriteString(out, "\n")
			} else if val.Type() != object.NULL_OBJ {
				io.WriteString(out, val.Inspect())
				io.WriteString(out, "\n")
			}
		}
		// When there's no output, readLineWithHistory already printed \n
		// The next call to readLineWithHistory will print the prompt on a fresh line

		// Ensure output is flushed
		if f, ok := out.(*os.File); ok {
			f.Sync() // Flush output
		}

		// Reset history index for next command
		history.Reset()
	}
}

func hasSyntaxError(errors []string) bool {
	for _, err := range errors {
		if strings.Contains(err, "expected") || strings.Contains(err, "unexpected") {
			return true
		}
	}
	return false
}

func suggestsIncomplete(errors []string) bool {
	for _, err := range errors {
		lower := strings.ToLower(err)
		// Check for EOF or unexpected end errors
		if strings.Contains(lower, "eof") || strings.Contains(lower, "unexpected end") {
			return true
		}
		// Check for "expected" errors that suggest missing tokens
		if strings.Contains(lower, "expected") {
			// These suggest incomplete input
			if strings.Contains(lower, "}") || strings.Contains(lower, ")") ||
				strings.Contains(lower, "]") || strings.Contains(lower, "expression") ||
				strings.Contains(lower, "identifier") || strings.Contains(lower, "token") {
				return true
			}
		}
		// Check for errors about undefined variables when they might be part of incomplete ADT
		// "undefined variable" errors might indicate incomplete parsing
		if strings.Contains(lower, "undefined variable") {
			// This could be incomplete, but also could be a real error
			// We'll be conservative and not treat it as incomplete
		}
		// Check for "no prefix parse function" - this often means incomplete input
		if strings.Contains(lower, "no prefix parse function") {
			return true
		}
		// Check for "nil expression" - might indicate incomplete parsing
		if strings.Contains(lower, "nil expression") {
			return true
		}
	}
	return false
}

func printParserErrors(out io.Writer, errors []string) {
	for _, msg := range errors {
		io.WriteString(out, "\t"+msg+"\n")
	}
}
