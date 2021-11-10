## Granule language server

The Granule language server allows for information from the Granule compiler to be accessed and worked with 'live', during development. It implements (a subset of!) the [Language Server Protocol](https://microsoft.github.io/language-server-protocol).

Currently, the following features are implemented:
* Live error feedback from the lexer, parser and typechecker
* More to come!

### Supported editors

[Any editor](https://microsoft.github.io/language-server-protocol/implementors/tools/) that supports the LSP should work with the Granule language server, as long as the `grls` binary has been installed (via `stack install`). If you run into problems specific to your editor, feel free to open an issue.

Some examples:

* VS Code, via the [granule-vscode-extension](https://github.com/granule-project/granule-vscode-extension). Note that this extension also includes additional features such as syntax highlighting, snippets and commands for program synthesis.

<img src="https://github.com/granule-project/granule/blob/language-server/server/vscode-diagnostics.gif" width=500px alt="Error feedback in VS Code" />

* VIM, using [vim-lsc](https://github.com/natebosch/vim-lsc).

<img src="https://github.com/granule-project/granule/blob/language-server/server/vim-diagnostics.gif" width=500px alt="Error feedback in VIM" />




