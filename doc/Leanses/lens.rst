Lens
====

This is the lens introduction

Type definitions
----------------

.. def:: Lens

  .. code:: lean

    def Lens s t a b : Type := ...

Function definitions
--------------------

.. def:: lens

  ``lens`` takes a getter and a setter function, and returns a :def:`Lens`.

  .. code:: lean

    def lens (get: s → a) (set: s → b → t): Lens s t a b := ...

:lean:`def random`
