import .basic ..colim

open eq pointed succ_str is_equiv equiv spectrum.smap seq_colim nat

namespace spectrum

  /- Prespectrification -/
  definition is_sconnected {N : succ_str} {X Y : gen_prespectrum N} (h : X →ₛ Y) : Type :=
  Π (E : gen_spectrum N), is_equiv (λ g : Y →ₛ E, g ∘ₛ h)

  -- We introduce a prespectrification operation X ↦ prespectrification X, with the goal of implementing spectrification as the sequential colimit of iterated applications of the prespectrification operation.
  definition prespectrification [constructor] {N : succ_str} (X : gen_prespectrum N) : gen_prespectrum N :=
  gen_prespectrum.mk (λ n, Ω (X (S n))) (λ n, Ω→ (glue X (S n)))

  -- To define the unit η : X → prespectrification X, we need its underlying family of pointed maps
  definition to_prespectrification_pfun {N : succ_str} (X : gen_prespectrum N) (n : N) : X n →* prespectrification X n :=
  glue X n

  -- And similarly we need the pointed homotopies witnessing that the squares commute
  definition to_prespectrification_psq {N : succ_str} (X : gen_prespectrum N) (n : N) :
  psquare (to_prespectrification_pfun X n) (Ω→ (to_prespectrification_pfun X (S n))) (glue X n)
    (glue (prespectrification X) n) :=
  psquare_of_phomotopy phomotopy.rfl

  -- We bundle the previous two definitions into a morphism of prespectra
  definition to_prespectrification {N : succ_str} (X : gen_prespectrum N) : X →ₛ prespectrification X :=
  begin
    fapply smap.mk,
    exact to_prespectrification_pfun X,
    exact to_prespectrification_psq X,
  end

  -- When E is a spectrum, then the map η : E → prespectrification E is an equivalence.
  definition is_sequiv_smap_to_prespectrification_of_is_spectrum {N : succ_str} (E : gen_prespectrum N) (H : is_spectrum E) : is_sequiv_smap (to_prespectrification E) :=
  begin
    intro n, induction E, induction H, exact is_equiv_glue n,
  end

  -- If η : E → prespectrification E is an equivalence, then E is a spectrum.
  definition is_spectrum_of_is_sequiv_smap_to_prespectrification {N : succ_str} (E : gen_prespectrum N) (H : is_sequiv_smap (to_prespectrification E)) : is_spectrum E :=
  begin
    fapply is_spectrum.mk,
    exact H
  end

  -- Our next goal is to show that if X is a prespectrum and E is a spectrum, then maps X →ₛ E extend uniquely along η : X → prespectrification X.

  -- In the following we define the underlying family of pointed maps of such an extension
  definition is_sconnected_to_prespectrification_inv_pfun {N : succ_str} {X : gen_prespectrum N} {E : gen_spectrum N} : (X →ₛ E) → Π (n : N), prespectrification X n →* E n :=
  λ (f : X →ₛ E) n, (equiv_glue E n)⁻¹ᵉ* ∘* Ω→ (f (S n))

  -- In the following we define the commuting squares of the extension
  definition is_sconnected_to_prespectrification_inv_psq {N : succ_str} {X : gen_prespectrum N} {E : gen_spectrum N} (f : X →ₛ E) (n : N) :
  psquare (is_sconnected_to_prespectrification_inv_pfun f n)
      (Ω→ (is_sconnected_to_prespectrification_inv_pfun f (S n)))
      (glue (prespectrification X) n)
      (glue (gen_spectrum.to_prespectrum E) n)
  :=
  begin
    fapply psquare_of_phomotopy,
    refine (passoc (glue (gen_spectrum.to_prespectrum E) n) (pequiv.to_pmap
    (equiv_glue (gen_spectrum.to_prespectrum E) n)⁻¹ᵉ*) (Ω→ (to_fun f (S n))))⁻¹* ⬝* _,
    refine pwhisker_right (Ω→ (to_fun f (S n))) (pright_inv (equiv_glue E n)) ⬝* _,
    refine _ ⬝* pwhisker_right (glue (prespectrification X) n) ((ap1_pcompose (pequiv.to_pmap (equiv_glue (gen_spectrum.to_prespectrum E) (S n))⁻¹ᵉ*) (Ω→ (to_fun f (S (S n)))))⁻¹*),
    refine pid_pcompose (Ω→ (f (S n))) ⬝* _,
    repeat exact sorry
  end

  -- Now we bundle the definition into a map (X →ₛ E) → (prespectrification X →ₛ E)
  definition is_sconnected_to_prespectrification_inv {N : succ_str} (X : gen_prespectrum N) (E : gen_spectrum N)
  : (X →ₛ E) → (prespectrification X →ₛ E) :=
  begin
    intro f,
    fapply smap.mk,
    exact is_sconnected_to_prespectrification_inv_pfun f,
    exact is_sconnected_to_prespectrification_inv_psq f
  end

  definition is_sconnected_to_prespectrification_isretr_pfun {N : succ_str} {X : gen_prespectrum N} {E : gen_spectrum N} (f : prespectrification X →ₛ E) (n : N) : to_fun (is_sconnected_to_prespectrification_inv X E (f ∘ₛ to_prespectrification X)) n ~* to_fun f n := begin exact sorry end

  definition is_sconnected_to_prespectrification_isretr_psq {N : succ_str} {X : gen_prespectrum N} {E : gen_spectrum N} (f : prespectrification X →ₛ E) (n : N) :
  ptube_v (is_sconnected_to_prespectrification_isretr_pfun f n)
      (Ω⇒ (is_sconnected_to_prespectrification_isretr_pfun f (S n)))
      (glue_square (is_sconnected_to_prespectrification_inv X E (f ∘ₛ to_prespectrification X)) n)
      (glue_square f n)
  :=
  begin
    repeat exact sorry
  end

  definition is_sconnected_to_prespectrification_isretr {N : succ_str} (X : gen_prespectrum N) (E : gen_spectrum N) (f : prespectrification X →ₛ E) : is_sconnected_to_prespectrification_inv X E (f ∘ₛ to_prespectrification X) = f :=
  begin
    fapply eq_of_shomotopy,
    fapply shomotopy.mk,
    exact is_sconnected_to_prespectrification_isretr_pfun f,
    exact is_sconnected_to_prespectrification_isretr_psq f,
  end

  definition is_sconnected_to_prespectrification_issec_pfun {N : succ_str} {X : gen_prespectrum N} {E : gen_spectrum N} (g : X →ₛ E) (n : N) :
  to_fun (is_sconnected_to_prespectrification_inv X E g ∘ₛ to_prespectrification X) n ~* to_fun g n
  :=
  begin
    repeat exact sorry
  end

  definition is_sconnected_to_prespectrification_issec_psq {N : succ_str} {X : gen_prespectrum N} {E : gen_spectrum N} (g : X →ₛ E) (n : N) :
  ptube_v (is_sconnected_to_prespectrification_issec_pfun g n)
      (Ω⇒ (is_sconnected_to_prespectrification_issec_pfun g (S n)))
      (glue_square (is_sconnected_to_prespectrification_inv X E g ∘ₛ to_prespectrification X) n)
      (glue_square g n)
  :=
  begin
    repeat exact sorry
  end

  definition is_sconnected_to_prespectrification_issec {N : succ_str} (X : gen_prespectrum N) (E : gen_spectrum N) (g : X →ₛ E) :
  is_sconnected_to_prespectrification_inv X E g ∘ₛ to_prespectrification X = g :=
  begin
    fapply eq_of_shomotopy,
    fapply shomotopy.mk,
    exact is_sconnected_to_prespectrification_issec_pfun g,
    exact is_sconnected_to_prespectrification_issec_psq g,
  end

  definition is_sconnected_to_prespectrify {N : succ_str} (X : gen_prespectrum N) :
    is_sconnected (to_prespectrification X) :=
  begin
    intro E,
    fapply adjointify,
    exact is_sconnected_to_prespectrification_inv X E,
    exact is_sconnected_to_prespectrification_issec X E,
    exact is_sconnected_to_prespectrification_isretr X E
  end

  -- Conjecture
  definition is_spectrum_of_local (X : gen_prespectrum +ℕ) (Hyp : is_equiv (λ (f : prespectrification (psp_sphere) →ₛ X), f ∘ₛ to_prespectrification (psp_sphere))) : is_spectrum X :=
  begin
    fapply is_spectrum.mk,
    exact sorry
  end

  /- Spectrification -/

  open chain_complex
  definition spectrify_type_term {N : succ_str} (X : gen_prespectrum N) (n : N) (k : ℕ) : Type* :=
  Ω[k] (X (n +' k))

  definition spectrify_type_fun' {N : succ_str} (X : gen_prespectrum N) (n : N) (k : ℕ) :
    Ω[k] (X n) →* Ω[k+1] (X (S n)) :=
  !loopn_succ_in⁻¹ᵉ* ∘* Ω→[k] (glue X n)

  definition spectrify_type_fun {N : succ_str} (X : gen_prespectrum N) (n : N) (k : ℕ) :
    spectrify_type_term X n k →* spectrify_type_term X n (k+1) :=
  spectrify_type_fun' X (n +' k) k

  definition spectrify_type_fun_zero {N : succ_str} (X : gen_prespectrum N) (n : N) :
    spectrify_type_fun X n 0 ~* glue X n :=
  !pid_pcompose

  definition spectrify_type {N : succ_str} (X : gen_prespectrum N) (n : N) : Type* :=
  pseq_colim (spectrify_type_fun X n)

  /-
    Let Y = spectify X ≡ colim_k Ω^k X (n + k). Then
    Ω Y (n+1) ≡ Ω colim_k Ω^k X ((n + 1) + k)
          ... = colim_k Ω^{k+1} X ((n + 1) + k)
          ... = colim_k Ω^{k+1} X (n + (k + 1))
          ... = colim_k Ω^k X(n + k)
          ... ≡ Y n
  -/

  definition spectrify_type_fun'_succ {N : succ_str} (X : gen_prespectrum N) (n : N) (k : ℕ) :
    spectrify_type_fun' X n (succ k) ~* Ω→ (spectrify_type_fun' X n k) :=
  begin
    refine !ap1_pcompose⁻¹*
  end

  definition spectrify_pequiv {N : succ_str} (X : gen_prespectrum N) (n : N) :
    spectrify_type X n ≃* Ω (spectrify_type X (S n)) :=
  begin
    refine !pshift_equiv ⬝e* _,
    transitivity pseq_colim (λk, spectrify_type_fun' X (S n +' k) (succ k)),
    fapply pseq_colim_pequiv,
    { intro n, apply loopn_pequiv_loopn, apply pequiv_ap X, apply succ_str.add_succ },
    { exact abstract begin intro k,
      refine !passoc⁻¹* ⬝* _, refine pwhisker_right _ (loopn_succ_in_inv_natural (succ k) _) ⬝* _,
      refine !passoc ⬝* _ ⬝* !passoc⁻¹*, apply pwhisker_left,
      refine !apn_pcompose⁻¹* ⬝* _ ⬝* !apn_pcompose, apply apn_phomotopy,
      exact !glue_ptransport⁻¹* end end },
    refine _ ⬝e* !pseq_colim_loop⁻¹ᵉ*,
    exact pseq_colim_equiv_constant (λn, !spectrify_type_fun'_succ),
  end

  definition spectrify [constructor] {N : succ_str} (X : gen_prespectrum N) : gen_spectrum N :=
  spectrum.MK (spectrify_type X) (spectrify_pequiv X)

  definition spectrify_map {N : succ_str} {X : gen_prespectrum N} : X →ₛ spectrify X :=
  begin
    fapply smap.mk,
    { intro n, exact pinclusion _ 0 },
    { intro n, apply phomotopy_of_psquare,
      refine !pid_pcompose⁻¹* ⬝ph* _,
      refine !passoc ⬝* pwhisker_left _ (pshift_equiv_pinclusion (spectrify_type_fun X n) 0) ⬝* _,
      refine !passoc⁻¹* ⬝* _,
      refine _ ◾* (spectrify_type_fun_zero X n ⬝* !pid_pcompose⁻¹*),
      refine !passoc ⬝* pwhisker_left _ !pseq_colim_pequiv_pinclusion ⬝* _,
      refine pwhisker_left _ (pwhisker_left _ (ap1_pid) ⬝* !pcompose_pid) ⬝* _,
      refine !passoc ⬝* pwhisker_left _ !seq_colim_equiv_constant_pinclusion ⬝* _,
      apply pinv_left_phomotopy_of_phomotopy,
      exact !pseq_colim_loop_pinclusion⁻¹*
    }
  end

  definition spectrify.elim_n {N : succ_str} {X : gen_prespectrum N} {Y : gen_spectrum N}
    (f : X →ₛ Y) (n : N) : (spectrify X) n →* Y n :=
  begin
    fapply pseq_colim.elim,
    { intro k, refine !equiv_gluen⁻¹ᵉ* ∘* apn k (f (n +' k)) },
    { intro k, refine !passoc ⬝* pwhisker_right _ !equiv_gluen_inv_succ ⬝* _,
      refine !passoc ⬝* _, apply pwhisker_left,
      refine !passoc ⬝* _,
      refine pwhisker_left _ ((passoc _ _ (_ ∘* _))⁻¹*) ⬝* _,
      refine pwhisker_left _ !passoc⁻¹* ⬝* _,
      refine pwhisker_left _ (pwhisker_right _ (phomotopy_pinv_right_of_phomotopy (!loopn_succ_in_natural)⁻¹*)⁻¹*) ⬝* _,
      refine pwhisker_right _ !apn_pinv ⬝* _,
      refine (phomotopy_pinv_left_of_phomotopy _)⁻¹*,
      refine apn_psquare k _,
      refine psquare_of_phomotopy !smap.glue_square }
  end

  definition spectrify.elim {N : succ_str} {X : gen_prespectrum N} {Y : gen_spectrum N}
    (f : X →ₛ Y) : spectrify X →ₛ Y :=
  begin
    fapply smap.mk,
    { intro n, exact spectrify.elim_n f n },
    { intro n, exact sorry }
  end

  definition phomotopy_spectrify.elim {N : succ_str} {X : gen_prespectrum N} {Y : gen_spectrum N}
    (f : X →ₛ Y) (n : N) : spectrify.elim_n f n ∘* spectrify_map n ~* f n :=
  begin
    refine pseq_colim.elim_pinclusion _ _ 0 ⬝* _,
    exact !pid_pcompose
  end

  definition spectrify_fun {N : succ_str} {X Y : gen_prespectrum N} (f : X →ₛ Y) : spectrify X →ₛ spectrify Y :=
  spectrify.elim ((@spectrify_map _ Y) ∘ₛ f)


end spectrum
