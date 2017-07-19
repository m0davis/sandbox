{-

  possible properties of (_⊸_ : ∀ {𝔬} {𝔒 : Ø 𝔬} {𝔯} → 𝔒 → 𝔒 → Ø 𝔯)
    R : reflexive
      ∀ x → x ⊸ x
    S : symmetric
      ∀ x y → x ⊸ y → y ⊸ x
    T : transitive
      ∀ x y z → x ⊸ y → y ⊸ z → x ⊸ z
    more?

  prototypical examples

    +R+S+T : = (equality)
    +R+S-T : is-near-to, is-within-two-of, shares-some-of-the-same-factors-as
    +R-S+T : ≤ (non-strict inequality)
    +R-S-T : isn't-to-the-east-of,
    -R+S+T : is-in-a-community-of-nontrivial-size-with
    -R+S-T : ≠ (anti-equality), is-far-from, is-coprime-with
    -R-S+T : < (strict inequality)
    -R-S-T : is-to-the-east-of, is-the-father-of, is-responsible-for, loves

  Anti-equality (labeled -R+S-T) is not only not reflexive, but also anti-reflexive. It is not transitive, but it is not anti-transitive. If we include the anti's in our categorisation, we will expand the number of combinations from 2³ = 8 to 3³ = 27. (Not 2⁶, because each property logically excludes its opposite.)

-}
