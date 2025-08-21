The boundary of this sublibrary to the outside world is
via `Definitions.idr` and `Instances.idr` files


In `src/Data/Container` 

1) In every subfolder, `Definition.idr` never depends on any `Instances.idr` from any subfolder.
2) In every subfolder:
  2.1) `Instance.idr` always depends on `Definition.idr`
  2.2) `Definition.idr` never depends on `Instance.idr` (this follows from 2.1)
  2.3) `Instance.idr` can depend on other `Definition.idr`'s and `Instance.idr`'s from other subfolders


Notably, `Object.Definition.idr` is a root of this dependency graph.

Definitions is a vertical slice [0] (in numpy format)
Instances is another vertical slice [1] (in numpy format)