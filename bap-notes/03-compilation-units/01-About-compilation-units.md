# Compilation units

The KB lets you create your own slots, objects, and classes, which you can use to store whatever information you like.

BAP also has many pre-defined slots, objects, and classes. They are arranged in a hierarchy. Some of the slots hold objects, which themselves have slots, which can in turn hold further objects, and so on.

At the top of the hierarchy is an object called a "label." A label basically represents a location in a binary program. 

A label has various slots, e.g.:

* An address slot (to hold the address at that point in the program)
* A name slot (if there is a symbol name associated with this location)
* A memory slot (to hold the memory layout of the program at this point)

But a label also has slots that can hold further KB objects:

* A "unit" slot (to hold a compilation unit object)
* A "semantics" slot (to hold a semantics object)

Note that these slots hold KB _objects_, and so those objects themselves have further slots. 

Here is a picture of a label object:

```
                    +--------------+    +---------------------+
                 +--| Address slot |--> | Can hold an address |
                 |  +--------------+    +---------------------+ 
                 |  
                 |  +-----------+    +-----------------+
                 +--| Name slot |--> | Can hold a name |
                 |  +-----------+    +-----------------+ 
                 |  
                 |  +-------------+    +------------------+
                 |--| Memory slot |--> | Can hold the mem |
  +-----------+  |  +-------------+    +------------------+
* | Label obj |--+
  +-----------+  |  +-----------------------+    +---------------------------+
                 |--| Compilation unit slot |--> | Can hold a Comp. unit obj |
                 |  +-----------------------+    +---------------------------+
                 |
                 |  +----------------+    +--------------------------+
                 +--| Semantics slot |--> | Can hold a Semantics obj |
                 |  +----------------+    +--------------------------+
                 |  
                 +-- ... Various other slots (see documentation)
```

Here is a picture of a Compilation unit object:

```
                         +------------------+    +----------------+
                      +--| Target arch slot |--> | Holds Target.t |
                      |  +------------------+    +----------------+
  +----------------+  |
* | Comp. unit obj |--+
  +----------------+  |
                      |
                      +-- ... Various other slots (see documentation)
```

