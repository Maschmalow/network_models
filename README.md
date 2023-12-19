# network_models
This is an experimental formalisation of the network model introduced in [my thesis](https://tel.archives-ouvertes.fr/tel-03583890/document).

This project is a learning ground, questionable code lies ahead.

* listidx.v adds a ```indexOf l``` type that let us easily work with indexes of list ```l```
* sequences.v defines the types of coinductive lists, or equivalently, streams thay may be finite. It also defines the ```indexOf s``` type for a sequence ```s```.
* network.v is the main files, which will be broken up in the future. Currently implemented:
  - Types for protocols, modules
  - associated events, executions as sequences of events, nodes states and IO during execution
  - admissibility predicates for : modules admissibilty predicates, execution of the protocol by honest nodes, corruption structures
  - satisfication of module specification by a protocol
  - the 'asynchronous network' module
  - reductions between modules
