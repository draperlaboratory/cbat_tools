plugin:
	touch value_set.ml
	bapbuild -package cbat-plugin-value-set value_set.plugin
	bapbundle update -desc "`ocamlfind query -format "%D" cbat-plugin-value-set`" value_set.plugin
	bapbundle install value_set.plugin
	bapbuild -clean
	rm value_set.ml

