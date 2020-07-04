plugin = "bildb"
name = "bildb"
desc = "A Primus-based BIL debugger"
Is = "lib,lib/screens"
pkgs = "bap-primus"

all: plugin.uninstall plugin.clean plugin.build plugin.install

clean: plugin.uninstall plugin.clean

plugin.build:
	bapbuild -use-ocamlfind -pkgs $(pkgs) -Is $(Is) $(plugin).plugin
	bapbundle update -name $(name) $(plugin).plugin
	bapbundle update -desc $(desc) $(plugin).plugin

plugin.install:
	bapbundle install $(plugin).plugin

plugin.clean:
	bapbuild -clean

plugin.uninstall:
	bapbundle remove $(plugin).plugin

