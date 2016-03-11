module RerightDoneRight where

  open import Agda.Builtin.Reflection
  open import Agda.Builtin.Nat
  open import Agda.Builtin.List

  data NamedSort   : Set
  data NamedClause : Set
  data NamedTerm   : Set
  NamedType = NamedTerm

  AnnotationId = Nat

  data Annotation : Set where
    boundAnnotation : AnnotationId → Annotation
    freeAnnotation : Nat → AnnotationId → Annotation

  data NamedTerm where
    var           : (x : Annotation) (args : List (Arg NamedTerm)) → NamedTerm
    con           : (c : Name) (args : List (Arg NamedTerm)) → NamedTerm
    def           : (f : Name) (args : List (Arg NamedTerm)) → NamedTerm
    lam           : (v : Visibility) (t : Abs NamedTerm) → NamedTerm
    pat-lam       : (cs : List Clause) (args : List (Arg NamedTerm)) → NamedTerm
    pi            : (a : Arg NamedType) (b : Abs NamedType) → NamedTerm
    agda-sort     : (s : NamedSort) → NamedTerm
    lit           : (l : Literal) → NamedTerm
    meta          : (x : Meta) → List (Arg NamedTerm) → NamedTerm
    unknown       : NamedTerm
   
  data NamedSort where
    set     : (t : NamedTerm) → NamedSort
    lit     : (n : Nat) → NamedSort
    unknown : NamedSort
   
  data NamedClause where
    clause        : (ps : List (Arg Pattern)) (t : NamedTerm) → NamedClause
    absurd-clause : (ps : List (Arg Pattern)) → NamedClause

  open import Prelude
  open import Container.Traversable

  record AnnotationFromDeBruijn : Set where
    inductive
    field
      lookupAnnotation : Nat → AnnotationFromDeBruijn × Annotation
      registerNewAnnotation : Nat → AnnotationFromDeBruijn
      
      
  open AnnotationFromDeBruijn

  mutual
    transformTerm : AnnotationFromDeBruijn → Term → AnnotationFromDeBruijn × NamedTerm
    transformTerm db (var x args) = let Σargs' = transformTerms db args
                                        db' = fst Σargs'
                                        args' = snd Σargs'
                                        Σx' = lookupAnnotation db' x
                                        db' = fst Σx'
                                        x' = snd Σx'
                                    in db' , var x' args'
    transformTerm db (con c args) = {!!}
    transformTerm db (def f args) = {!!}
    transformTerm db (lam v t) = {!!}
    transformTerm db (pat-lam cs args) = {!!}
    transformTerm db (pi a b) = {!!}
    transformTerm db (agda-sort s) = {!!}
    transformTerm db (lit l) = db , lit l
    transformTerm db (meta x x₁) = {!!}
    transformTerm db unknown = db , unknown

    transformTerms : AnnotationFromDeBruijn → List (Arg Term) → AnnotationFromDeBruijn × List (Arg NamedTerm)
    transformTerms db [] = db , []
    transformTerms db (t ∷ ts) = let Σts' = transformTerms db ts
                                     db' = fst Σts'
                                     ts' = snd Σts'
                                     t' = transformTerm db' t
                                 in fst t' , snd t' ∷ ts'
