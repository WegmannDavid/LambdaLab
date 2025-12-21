import LambdaLab.CoC.Tm

open Subst

inductive Step : Tm → Tm → Prop where
| app1 :

  Step t t' →
  --------------------
  Step (t ⬝ s) (t' ⬝ s)

| app2 :

  Step s s' →
  --------------------
  Step (t ⬝ s) (t ⬝ s')

| bnd1 :

  Step t t →
  -----------------------------------
  Step (.bnd b x t s) (.bnd b x t' s)

| bnd2 :

  Step t t →
  -----------------------------------
  Step (.bnd b x t s) (.bnd b x t' s)
