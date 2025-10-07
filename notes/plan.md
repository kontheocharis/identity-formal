# Plan for OpTT metatheory


## Untyped computational fragment

1. Show that the natural number η and β rules are confluent. (lambdapi)

## Total theory

1. Encode the whole thing in Agda as an indexed CwF
2. Produce a realisability semantics for it:

  - First, we require that the input PCA implements all the primitives of the untyped
    language. Most of these can be emulated in any PCA (not η rules!) but we want to allow
    the user of the model to choose what to interpret them as.
    
  - We should provide at least one model of this input PCA---ideally it should be a partial PCA
    whose elements are lambda calculus+ normal forms. Application is defined only if the resulting
    term is normalised.

  - We cannot get a constructive normalisation procedure for this but at least we can get a proof that
    any closed program yields a normalising term. Also open programs map normal terms to normal terms.


  - What does the realisability semantics look like?

    ConC = ℕ 
    ConL = Set
    ConT ΓL ΓC = TotalRRel ΓC ΓL

    SubC ΓC ΔC = (A [ ΓC ])^ ΔC   -- ΔC-tuples of terms in A with ΓC free variabels
    SubL ΓL ΔL = ΓL → ΔL   
    SubT Γ Δ σL σC = σC tracks σL 

  - Do we want a separation between resourced and unresourced types?
    
    - Not for now... it doesn't play well with the idea that 'types are purely
      logical'
    - If types are aware of computational content, and we put the total theory
      in type position, we no longer have good reduction because no β
    - If types are not aware of computational content, we cannot have general
      extension types.
    
