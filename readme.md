# Scala 2.x Compiler Plugin for The Sireum Language (Slang)

This plugin provides syntactic program transformations to allow compiling
Slang programs using the latest Scala 2.x standard compiler.

The following program transformations are applied (in order) 
right after the scalac parsing phase if the ``.scala`` file's first line (without whitespace) contains 
``#Sireum`` in a comment (or if the first import is ``org.sireum._`` or ``org.sireum.logika._`` for
``.sc`` and ``.logika`` files):

* ``s"..."`` ⟹ ``s"..."``

  (preserved as is, i.e., unaffected by other transformations below)

* ``tup( ... ) = <exp>`` ⟹ ``tup( ... ) = <exp2>``

  where ``<exp2>`` is *transform*(``<exp>``)
  
  (``tup( ... )`` is preserved as is)

* ``def ... = l"""..."""`` ⟹ ``def ...``

   if in a trait  

* ``def ... = l""" ... """`` ⟹ ``def ... = lDef""" ... """``
  
  if not in a trait 

* ``l""" ... """"`` ⟹ ``lUnit""" ... """"``
 
* ``<lit>: Int`` ⟹ ``z"<N>"``

  where ``<N>`` is ``<lit>.toString``
 
* ``<lit>: Long`` ⟹ ``z"<N>"``

  where ``<N>`` is ``<lit>.toString``

* ``case <pat> if <exp> => <body>`` ⟹ ``case <pat> if <exp2> => <body2>``

  where:
   
  * ``<exp2>`` is *transform*(``<exp>``)
  
  * ``<body2>`` is *transform*(``<body>``)
  
  (``<pat>`` is preserved as is)

* ``<exp>(<arg>, ..., <arg>)`` ⟹ ``<exp>(<arg2>, ..., <arg2>)``

  where each ``<arg2>`` is:
  
  * *transform*(``<arg>``)
  
    if ``<arg>`` is a literal
   
  * ``<id> = `` ``_assign (`` *transform*(``<exp>``) ``)``
  
    if ``<arg>`` is ``<id> = <exp>``
   
  * ``_assign(`` *transform*(``<arg>``) ``)``
  
    otherwise
  
* ``<lhs> = <exp>`` ⟹ ``<lhs> = <exp2>``

  where ``<exp2>`` is ``_assign(`` *transform*(``<exp>``) ``)``

* ``<exp>(<arg>, ..., <arg>) = <rhs>`` ⟹ ``<exp2>(<arg2>, ..., <arg2>) = <rhs2>``
  
  where:
   
  * ``<exp2>`` is *transform*(``<exp>``)
   
  * each ``<arg2>`` is *transform*(``<arg>``)
  
  * ``<rhs2>`` is ``_assign(`` *transform*(``<rhs>``) ``)``
  
* ``(<exp>, ..., <exp>)`` ⟹ ``(<exp2>, ..., <exp2>)``

  where each ``<exp2>`` is ``_assign(`` *transform*(``<exp>``) ``)``

* ``val <pat>: <type> = <exp>`` ⟹ ``val <pat>: <type> = <exp2>`` 

  where ``<exp2>`` is ``_assign(`` *transform*(``<exp>``) ``)``
  
  (``<pat>`` is preserved as is)

* ``var <pat>: <type> = <exp>`` ⟹ ``val <pat>: <type> = <exp2>``

  where ``<exp2>`` is ``_assign(`` *transform*(``<exp>``) ``)``
  
  (``<pat>`` is preserved as is)


# To Do

* customize precedence for Slang unicode operators