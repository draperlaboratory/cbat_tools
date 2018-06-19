plugin:
	touch explicit_edge.ml
	bapbuild -package cbat-plugin-explicit-edge explicit_edge.plugin
	bapbundle update -desc "`ocamlfind query -format "%D" cbat-plugin-explicit-edge`" explicit_edge.plugin
	bapbundle install explicit_edge.plugin
	bapbuild -clean
	rm explicit_edge.ml
