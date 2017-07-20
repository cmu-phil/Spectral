import .spectrification ..homotopy.smash_adjoint

open pointed is_equiv equiv eq susp succ_str smash int
namespace spectrum

  /- Smash product of a prespectrum and a type -/

definition smash_prespectrum (X : Type*) (Y : prespectrum) : prespectrum :=
prespectrum.mk (λ z, X ∧ Y z) begin
  intro n, refine loop_susp_pintro (X ∧ Y n) (X ∧ Y (n + 1)) _,
  refine _ ∘* (smash_susp X (Y n))⁻¹ᵉ*,
  refine smash_functor !pid _,
  refine susp_pelim (Y n) (Y (n + 1)) _,
  exact !glue
end

definition smash_prespectrum_fun {X X' : Type*} {Y Y' : prespectrum} (f : X →* X') (g : Y →ₛ Y') : smash_prespectrum X Y →ₛ smash_prespectrum X' Y' :=
smap.mk (λn, smash_functor f (g n)) begin
  intro n,
  refine susp_to_loop_psquare _ _ _ _ _,
  refine pvconcat (psquare_transpose (phinverse (smash_susp_natural f (g n)))) _,
  refine vconcat_phomotopy _ (smash_functor_split f (g (S n))),
  refine phomotopy_vconcat (smash_functor_split f (susp_functor (g n))) _,
  refine phconcat _ _,
  let glue_adjoint := susp_pelim (Y n) (Y (S n)) (glue Y n),
  exact pid X' ∧→ glue_adjoint,
  exact smash_functor_psquare (pvrefl f) (phrefl glue_adjoint),
  refine smash_functor_psquare (phrefl (pid X')) _,
  refine loop_to_susp_square _ _ _ _ _,
  exact smap.glue_square g n
end

  /- smash of a spectrum and a type -/
definition smash_spectrum (X : Type*) (Y : spectrum) : spectrum :=
spectrify (smash_prespectrum X Y)

definition smash_spectrum_fun {X X' : Type*} {Y Y' : spectrum} (f : X →* X') (g : Y →ₛ Y') : smash_spectrum X Y →ₛ smash_spectrum X' Y' :=
spectrify_fun (smash_prespectrum_fun f g)


end spectrum
