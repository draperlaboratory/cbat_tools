PASS_NAME=save_project

$(PASS_NAME).plugin: $(PASS_NAME).ml
	bapbuild $(PASS_NAME).plugin
	bapbundle install $(PASS_NAME).plugin

all: $(PASS_NAME).plugin
	echo $(PASS_NAME)

clean:
	rm -rf _build $(PASS_NAME).plugin
