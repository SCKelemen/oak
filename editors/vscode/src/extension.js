// The Oak VS Code extension: syntax highlighting comes from the TextMate
// grammar in ../syntaxes; everything else comes from the language server
// (`oak lsp`, docs/spec/115-tooling.md section 4), spawned over stdio with a
// fixed argument list.
const vscode = require("vscode");
const { LanguageClient, TransportKind } = require("vscode-languageclient/node");

let client;

function activate(context) {
  const config = vscode.workspace.getConfiguration("oak");
  const command = config.get("serverPath", "oak");
  const serverOptions = {
    command,
    args: ["lsp"],
    transport: TransportKind.stdio,
  };
  const clientOptions = {
    documentSelector: [{ scheme: "file", language: "oak" }],
    synchronize: { fileEvents: vscode.workspace.createFileSystemWatcher("**/*.oak") },
  };
  client = new LanguageClient("oak", "Oak language server", serverOptions, clientOptions);
  context.subscriptions.push(client.start());
}

function deactivate() {
  return client ? client.stop() : undefined;
}

module.exports = { activate, deactivate };
