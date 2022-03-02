# The Knowledge Base

The knowledge base (or "KB" for short) is a kind of database that your plugins can use to store information.


## Objects

What do we actually store in the KB? We store "objects."

An object is an entity that has a series of slots that you can put information in. If you like, you can think of an object as a storage cabinet with a bunch of slots.

At first, the slots are empty, but your plugin can add information to (and read information from) the slots as needed.


## Slots

Slots are "typed," in the sense that each slot can only hold data that comes from a specified domain of values.

Slots take information in an additive, non-destructive way. If you try to put some information into a slot that conflicts with information already there, BAP will reject it. Similarly, if you try to remove or overwrite information that's already there, BAP will prevent it.

In BAP's documentation, slots are often called "slots," but they are also called "properties" (of objects). Domains are always called "domains."


## Snapshots

At any point during your plugin's lifetime, you can take a snapshot of an object. This is just a record of the information contained in each of the object's slots, at the time that the snapshot is taken.

In BAP's documentation, a snapshot is called a KB "value," but keep in mind that a KB-value is not a single piece of information. Rather, it is an array of values, taken from the slots when the snapshot was taken.


## Classes

Before you create an object, you must first create a blueprint for it. In the blueprint, you specify which slots the object should have, and which domain of values each slot should hold.

Once you've created a blueprint, you can create many objects (instances) from the same blueprint. All instances of the blueprint will therefore have the same array of slots.

The blueprint is called a KB "class" in BAP's documentation. Hence, to say that each object is created from a blueprint is to say that each object is an instance of a class.


## Documentation

For more about the KB and its API, see the [documentation](http://binaryanalysisplatform.github.io/bap/api/master/bap-knowledge/Bap_knowledge/Knowledge/index.html).