'use strict';
// LambdaLab for VS Code: a language client with no dependencies.
//
// Each language's compiler doubles as its language server (`stlc --lsp`, …), speaking the Language
// Server Protocol on stdin and stdout. This file is the client half: it starts one server per
// language as files of that language are opened, keeps it in sync with the editor (the whole text
// on each change), shows the diagnostics it publishes, and asks it for the outline and for
// formatting. Positions need no conversion: the protocol and VS Code both count UTF-16 units.

const vscode = require('vscode');
const cp = require('child_process');
const fs = require('fs');
const path = require('path');

/** Language id → the compiler that serves it. */
const SERVERS = {
  stlc: 'stlc', systemf: 'systemf', coc: 'coc', coic: 'coic', ecc: 'ecc', float: 'float',
};

/** How long to wait after a keystroke before sending the text. */
const DEBOUNCE_MS = 250;

let output;
let diagnostics;
const servers = new Map();       // language id → Server
const pendingChanges = new Map(); // uri → timer

class Server {
  constructor(lang, exe, cwd) {
    this.lang = lang;
    this.nextId = 1;
    this.pending = new Map();
    this.buffer = Buffer.alloc(0);
    this.dead = false;
    this.open = new Set();
    this.proc = cp.spawn(exe, ['--lsp'], { cwd });
    this.proc.stdout.on('data', (chunk) => this.onData(chunk));
    this.proc.stderr.on('data', (chunk) => output.append(chunk.toString()));
    this.proc.on('error', (e) => this.onExit(`could not start ${exe}: ${e.message}`));
    this.proc.on('exit', (code) => this.onExit(`exited with code ${code}`));
    this.ready = this.request('initialize', {
      processId: process.pid, rootUri: null, capabilities: {},
    }).then(() => this.notify('initialized', {}));
    this.ready.catch(() => {});
  }

  onExit(why) {
    if (this.dead) return;
    this.dead = true;
    output.appendLine(`[${this.lang}] server ${why}`);
    for (const p of this.pending.values()) p.reject(new Error(why));
    this.pending.clear();
    for (const uri of this.open) diagnostics.delete(vscode.Uri.parse(uri));
    if (servers.get(this.lang) === this) servers.delete(this.lang);
  }

  send(msg) {
    if (this.dead) return;
    const body = Buffer.from(JSON.stringify(msg), 'utf8');
    this.proc.stdin.write(`Content-Length: ${body.length}\r\n\r\n`);
    this.proc.stdin.write(body);
  }

  request(method, params) {
    const id = this.nextId++;
    return new Promise((resolve, reject) => {
      if (this.dead) return reject(new Error('server is not running'));
      this.pending.set(id, { resolve, reject });
      this.send({ jsonrpc: '2.0', id, method, params });
    });
  }

  notify(method, params) {
    this.send({ jsonrpc: '2.0', method, params });
  }

  onData(chunk) {
    this.buffer = Buffer.concat([this.buffer, chunk]);
    for (;;) {
      const sep = this.buffer.indexOf('\r\n\r\n');
      if (sep < 0) return;
      const header = this.buffer.subarray(0, sep).toString('ascii');
      const m = /Content-Length:\s*(\d+)/i.exec(header);
      if (!m) { this.buffer = this.buffer.subarray(sep + 4); continue; }
      const len = parseInt(m[1], 10);
      if (this.buffer.length < sep + 4 + len) return;
      const body = this.buffer.subarray(sep + 4, sep + 4 + len).toString('utf8');
      this.buffer = this.buffer.subarray(sep + 4 + len);
      let msg;
      try { msg = JSON.parse(body); } catch (e) { continue; }
      this.onMessage(msg);
    }
  }

  onMessage(msg) {
    if (msg.id !== undefined && msg.method === undefined) {
      const p = this.pending.get(msg.id);
      if (!p) return;
      this.pending.delete(msg.id);
      if (msg.error) p.reject(new Error(msg.error.message)); else p.resolve(msg.result);
    } else if (msg.method === 'textDocument/publishDiagnostics') {
      const uri = vscode.Uri.parse(msg.params.uri);
      diagnostics.set(uri, msg.params.diagnostics.map(toDiagnostic));
    }
  }

  didOpen(doc) {
    const uri = doc.uri.toString();
    this.open.add(uri);
    this.ready.then(() => this.notify('textDocument/didOpen', {
      textDocument: { uri, languageId: doc.languageId, version: doc.version, text: doc.getText() },
    }), () => {});
  }

  didChange(doc) {
    this.ready.then(() => this.notify('textDocument/didChange', {
      textDocument: { uri: doc.uri.toString(), version: doc.version },
      contentChanges: [{ text: doc.getText() }],
    }), () => {});
  }

  didClose(doc) {
    const uri = doc.uri.toString();
    this.open.delete(uri);
    this.ready.then(() => this.notify('textDocument/didClose', { textDocument: { uri } }), () => {});
  }

  stop() {
    if (this.dead) return Promise.resolve();
    const done = this.request('shutdown', null).catch(() => {}).then(() => {
      this.notify('exit', null);
      setTimeout(() => { if (!this.dead) this.proc.kill(); }, 1000);
    });
    return done;
  }
}

function toRange(r) {
  return new vscode.Range(r.start.line, r.start.character, r.end.line, r.end.character);
}

function toDiagnostic(d) {
  const diag = new vscode.Diagnostic(toRange(d.range), d.message, vscode.DiagnosticSeverity.Error);
  diag.source = d.source;
  return diag;
}

/** Where the compilers live: the setting, or the workspace's `.lake/build/bin`. */
function serverDirectory(doc) {
  const configured = vscode.workspace.getConfiguration('lambdalab').get('serverDirectory');
  if (configured) return { dir: configured, cwd: configured };
  const folder = vscode.workspace.getWorkspaceFolder(doc.uri)
    || (vscode.workspace.workspaceFolders || [])[0];
  if (!folder) return undefined;
  return { dir: path.join(folder.uri.fsPath, '.lake', 'build', 'bin'), cwd: folder.uri.fsPath };
}

const warned = new Set();

/** The server for a document's language, started if need be. */
function serverFor(doc) {
  const exeName = SERVERS[doc.languageId];
  if (!exeName) return undefined;
  const running = servers.get(doc.languageId);
  if (running && !running.dead) return running;
  const where = serverDirectory(doc);
  if (!where) return undefined;
  const exe = path.join(where.dir, exeName);
  if (!fs.existsSync(exe)) {
    if (!warned.has(exe)) {
      warned.add(exe);
      vscode.window.showWarningMessage(
        `LambdaLab: no ${exeName} compiler at ${exe}. Run \`lake build ${exeName}\`, then ` +
        '"LambdaLab: Restart Language Servers".');
    }
    return undefined;
  }
  const server = new Server(doc.languageId, exe, where.cwd);
  servers.set(doc.languageId, server);
  output.appendLine(`[${doc.languageId}] started ${exe} --lsp`);
  return server;
}

function onOpen(doc) {
  const server = serverFor(doc);
  if (server) server.didOpen(doc);
}

/** Send a document's latest text now, rather than after the debounce. */
function flush(doc) {
  const uri = doc.uri.toString();
  const timer = pendingChanges.get(uri);
  if (timer) {
    clearTimeout(timer);
    pendingChanges.delete(uri);
    const server = serverFor(doc);
    if (server) server.didChange(doc);
  }
}

function onChange(event) {
  const doc = event.document;
  if (!SERVERS[doc.languageId]) return;
  const uri = doc.uri.toString();
  clearTimeout(pendingChanges.get(uri));
  pendingChanges.set(uri, setTimeout(() => {
    pendingChanges.delete(uri);
    const server = serverFor(doc);
    if (!server) return;
    if (!server.open.has(uri)) server.didOpen(doc); else server.didChange(doc);
  }, DEBOUNCE_MS));
}

function onClose(doc) {
  const server = servers.get(doc.languageId);
  const uri = doc.uri.toString();
  clearTimeout(pendingChanges.get(uri));
  pendingChanges.delete(uri);
  if (server && server.open.has(uri)) server.didClose(doc);
  diagnostics.delete(doc.uri);
}

async function ask(doc, method) {
  flush(doc);
  const server = serverFor(doc);
  if (!server) return undefined;
  if (!server.open.has(doc.uri.toString())) server.didOpen(doc);
  await server.ready;
  return server.request(method, { textDocument: { uri: doc.uri.toString() } });
}

const symbolProvider = {
  async provideDocumentSymbols(doc) {
    const result = await ask(doc, 'textDocument/documentSymbol');
    return (result || []).map((s) => new vscode.DocumentSymbol(
      s.name, s.detail || '', s.kind - 1, toRange(s.range), toRange(s.selectionRange)));
  },
};

const formattingProvider = {
  async provideDocumentFormattingEdits(doc) {
    const result = await ask(doc, 'textDocument/formatting');
    return (result || []).map((e) => vscode.TextEdit.replace(toRange(e.range), e.newText));
  },
};

async function restart() {
  await Promise.all([...servers.values()].map((s) => s.stop()));
  servers.clear();
  warned.clear();
  vscode.workspace.textDocuments.forEach(onOpen);
}

function activate(context) {
  output = vscode.window.createOutputChannel('LambdaLab');
  diagnostics = vscode.languages.createDiagnosticCollection('lambdalab');
  const selector = Object.keys(SERVERS).map((language) => ({ language }));
  context.subscriptions.push(
    output,
    diagnostics,
    vscode.workspace.onDidOpenTextDocument(onOpen),
    vscode.workspace.onDidChangeTextDocument(onChange),
    vscode.workspace.onDidCloseTextDocument(onClose),
    vscode.languages.registerDocumentSymbolProvider(selector, symbolProvider),
    vscode.languages.registerDocumentFormattingEditProvider(selector, formattingProvider),
    vscode.commands.registerCommand('lambdalab.restartServers', restart),
  );
  vscode.workspace.textDocuments.forEach(onOpen);
}

function deactivate() {
  return Promise.all([...servers.values()].map((s) => s.stop()));
}

module.exports = { activate, deactivate };
