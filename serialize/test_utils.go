package serialize

import (
	"bufio"
	"encoding/json"
	"fmt"
	"os"
	"reflect"
	"strings"
)

// CompareJSONLFiles compares two JSONL files line by line
// Returns true if they are equal, false otherwise
// If they differ, returns the first differing line numbers and descriptions
func CompareJSONLFiles(file1, file2 string) (bool, int, int, string, error) {
	f1, err := os.Open(file1)
	if err != nil {
		return false, 0, 0, "", fmt.Errorf("failed to open file1: %w", err)
	}
	defer f1.Close()

	f2, err := os.Open(file2)
	if err != nil {
		return false, 0, 0, "", fmt.Errorf("failed to open file2: %w", err)
	}
	defer f2.Close()

	scanner1 := bufio.NewScanner(f1)
	scanner2 := bufio.NewScanner(f2)

	lineNum := 0
	for {
		lineNum++
		hasLine1 := scanner1.Scan()
		hasLine2 := scanner2.Scan()

		if !hasLine1 && !hasLine2 {
			// Both files ended at the same time - they're equal
			return true, 0, 0, "", nil
		}

		if !hasLine1 {
			return false, lineNum, 0, "file1 ended before file2", nil
		}

		if !hasLine2 {
			return false, 0, lineNum, "file2 ended before file1", nil
		}

		line1 := scanner1.Text()
		line2 := scanner2.Text()

		// Parse both lines as JSON
		var obj1, obj2 interface{}
		if err := json.Unmarshal([]byte(line1), &obj1); err != nil {
			return false, lineNum, lineNum, fmt.Sprintf("file1 line %d is not valid JSON: %v", lineNum, err), nil
		}

		if err := json.Unmarshal([]byte(line2), &obj2); err != nil {
			return false, lineNum, lineNum, fmt.Sprintf("file2 line %d is not valid JSON: %v", lineNum, err), nil
		}

		// Compare the JSON objects
		if !reflect.DeepEqual(obj1, obj2) {
			return false, lineNum, lineNum, fmt.Sprintf("objects differ at line %d", lineNum), nil
		}
	}
}

// ReadJSONLFile reads a JSONL file and returns all objects
func ReadJSONLFile(filepath string) ([]interface{}, error) {
	file, err := os.Open(filepath)
	if err != nil {
		return nil, fmt.Errorf("failed to open file: %w", err)
	}
	defer file.Close()

	var objects []interface{}
	scanner := bufio.NewScanner(file)
	for scanner.Scan() {
		line := scanner.Text()
		if line == "" {
			continue // Skip empty lines
		}

		var obj interface{}
		if err := json.Unmarshal([]byte(line), &obj); err != nil {
			return nil, fmt.Errorf("failed to parse JSON at line: %w", err)
		}
		objects = append(objects, obj)
	}

	if err := scanner.Err(); err != nil {
		return nil, fmt.Errorf("error reading file: %w", err)
	}

	return objects, nil
}

// DiffJSONLFiles returns a human-readable diff of two JSONL files
func DiffJSONLFiles(file1, file2 string) (string, error) {
	objs1, err := ReadJSONLFile(file1)
	if err != nil {
		return "", fmt.Errorf("failed to read file1: %w", err)
	}

	objs2, err := ReadJSONLFile(file2)
	if err != nil {
		return "", fmt.Errorf("failed to read file2: %w", err)
	}

	var diff strings.Builder
	diff.WriteString(fmt.Sprintf("File1 has %d lines, File2 has %d lines\n", len(objs1), len(objs2)))

	maxLen := len(objs1)
	if len(objs2) > maxLen {
		maxLen = len(objs2)
	}

	for i := 0; i < maxLen; i++ {
		if i >= len(objs1) {
			obj2JSON, _ := json.MarshalIndent(objs2[i], "", "  ")
			diff.WriteString(fmt.Sprintf("Line %d: file1 missing, file2 has:\n%s\n", i+1, obj2JSON))
			continue
		}

		if i >= len(objs2) {
			obj1JSON, _ := json.MarshalIndent(objs1[i], "", "  ")
			diff.WriteString(fmt.Sprintf("Line %d: file1 has, file2 missing:\n%s\n", i+1, obj1JSON))
			continue
		}

		if !reflect.DeepEqual(objs1[i], objs2[i]) {
			obj1JSON, _ := json.MarshalIndent(objs1[i], "", "  ")
			obj2JSON, _ := json.MarshalIndent(objs2[i], "", "  ")
			diff.WriteString(fmt.Sprintf("Line %d differs:\nFile1:\n%s\nFile2:\n%s\n", i+1, obj1JSON, obj2JSON))
		}
	}

	return diff.String(), nil
}
