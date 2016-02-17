import .LES_of_homotopy_groups homotopy.connectedness homotopy.homotopy_group

open eq is_trunc pointed homotopy is_equiv fiber equiv trunc nat

namespace is_conn

  theorem is_contr_HG_fiber_of_is_connected {A B : Type*} (n k : ℕ) (f : A →* B)
    [H : is_conn_map n f] (H2 : k ≤ n) : is_contr (π[k] (pfiber f)) :=
  @(trivial_homotopy_group_of_is_conn (pfiber f) H2) (H pt)

  theorem is_equiv_π_of_is_connected {A B : Type*} (n k : ℕ) (f : A →* B)
    [H : is_conn_map n f] (H : k ≤ n) : is_equiv (π→[k] f) :=
  begin
    exact sorry
  end

end is_conn
