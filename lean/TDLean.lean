/-
  TDLean -- root import file.

  TDLean.Audit is imported LAST and on purpose: it wraps every headline theorem in
  `#guard_msgs in #print axioms`, so a green `lake build TDLean` *is* the axiom audit.
  If a `sorry` appears anywhere in a headline's dependency graph, `sorryAx` enters the
  message, `#guard_msgs` fails, and the build fails.

  TDLean.Audit.CrossCheck is deliberately NOT imported here -- it is the only file
  allowed to touch banned mathlib modules, and keeping it out of this graph is what
  guarantees those lemmas never discharge a headline.
-/
import TDLean.Basic

-- Cluster B -- monoid algebra of prime length
import TDLean.MonoidAlgebra.ZMod.PrimeIsWithZero
import TDLean.MonoidAlgebra.Sym.SignType
import TDLean.MonoidAlgebra.PrimorialLimit

-- Cluster C -- Newman contour route
import TDLean.Newman.Region
import TDLean.Newman.Kernel
import TDLean.Newman.Contour
import TDLean.Newman.Winding
import TDLean.Newman.StarPrimitive
import TDLean.Newman.TruncCauchy
import TDLean.Newman.Laplace
import TDLean.Newman.Split
import TDLean.Newman.LeftLimit
import TDLean.Newman.Tauberian

-- Cluster C9 -- zeta from scratch
import TDLean.Zeta.Basic
import TDLean.Zeta.Continuation
import TDLean.Zeta.Holo
import TDLean.Zeta.Telescope
import TDLean.Zeta.LogDeriv
import TDLean.Zeta.DirichletMul
import TDLean.Zeta.VonMangoldt
import TDLean.Zeta.Identity
import TDLean.Zeta.RayIdentity
import TDLean.Zeta.Conj
import TDLean.Zeta.CriticalLine
import TDLean.Zeta.Mertens
import TDLean.Zeta.LogDerivOrder
import TDLean.Zeta.NonVanishing
import TDLean.Zeta.PhiHolo
import TDLean.PNT.Chebyshev
import TDLean.PNT.Mellin
import TDLean.PNT.Substitution
import TDLean.PNT.NewmanInput
import TDLean.PNT.GNewman
import TDLean.PNT.Region
import TDLean.PNT.Tauberian
import TDLean.PNT.Squeeze
import TDLean.PNT.Transfer
import TDLean.PNT.PiCount
import TDLean.PNT.PrimeCountingAsymp
import TDLean.FE.Theta.Transform
import TDLean.FE.Mellin.Term
import TDLean.FE.Mellin.Completed
import TDLean.FE.Mellin.Split
import TDLean.FE.Theta.Decay
import TDLean.FE.Mellin.Integrable
import TDLean.FE.Mellin.FunctionalEquation
import TDLean.Operator.Ell2C
import TDLean.Operator.Number
import TDLean.Operator.Isometry
import TDLean.Operator.BCAlgebra
import TDLean.Operator.QModZ
import TDLean.Operator.Rep
import TDLean.Operator.RootSum

import TDLean.Audit
