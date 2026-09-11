# Oak for Visual Studio Code

Syntax highlighting for `.oak` files and `oak.mod`, plus the Oak language
server (`oak lsp`) for diagnostics as you type, hover types, go to
definition, document symbols, and semantic highlighting.

Requirements: the `oak` executable on your PATH (or set `oak.serverPath`).

Development install:

```sh
cd editors/vscode
npm install
npx vsce package          # produces oak-language-0.1.0.vsix
code --install-extension oak-language-0.1.0.vsix
```

Or open this folder in VS Code and press F5 to run it in an Extension
Development Host.
