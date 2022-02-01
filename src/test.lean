import data.real.basic
import tactic

example (a b : ℝ): a ≥ b →|a - b| = a - b :=
begin
intro h,
rw abs_eq_self,
rw sub_nonneg,

end