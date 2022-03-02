# Documentation and Help

## Useful links

* https://binaryanalysisplatform.github.io/bap/api/master/index.html - The official BAP documentation.
* https://ocaml.janestreet.com/ocaml-core/latest/doc/ - Jane Street core documentation.
* https://github.com/BinaryAnalysisPlatform/bap-tutorial - The BAP tutorial


## The command line tool

For help with the command line tool:

```
bap --help
```

List the installed plugins:

```
bap list plugins
```

View the help of any plugin:

```
bap --PLUGIN-help
```

where PLUGIN should be replaced by the name of one of the plugins, e.g., `bap --print-help`.

To run the bap command line tool in debug mode, set the environment variable:

```
BAP_DEBUG=1
```

Bap writes its logs to:

```
${XDG_STATE_HOME}/bap/log
```

E.g.:

```
~/.local/state/bap/log
```

More information about system directories that BAP utilizes can be found in the (Bap_main.Extension.Configuration)[https://binaryanalysisplatform.github.io/bap/api/master/bap-main/Bap_main/Extension/Configuration/index.html] module.
