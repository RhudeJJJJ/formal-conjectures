/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor003Cell242
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 12
def witness : ComputedPolynomialCell.Witness := {
  a := (317349/8192)
  b := (1396335/32768)
  s := [(154514683111/18014398509481984),(-2921646852815/1152921504606846976),(232959360695/576460752303423488)]
  L := [(75657017661359326921875/75557863725914323419136),(-1143897765/4398046511104),(254544943/6597069766656),(-1365153/274877906944),(195149/412316860416)]
  c := (275176504235/274877906944)
  R := (54285051489/100000000000000)
  total := (231123956351/100000000000000)
  k := 0
  n := 32
  sFloor := (1858302896919/576460752303423488)
  nFloor := 52824063260567927515551959719116430092052015171020461385378960467863267247652864
  eFloor := 52753928555557857394781214442012177795112841064513269055851584886982487459233792
}

#check "COMPACT_WITNESS_READY"
theorem checked : ComputedPolynomialCell.checks data witness=true := by decide +kernel
#check "COMPACT_CHECK_PASSED"

noncomputable section
theorem actual_integral {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 12)
        (CoreQuotient.fused G u 9 12) ((51/26 : ℚ) : ℝ) y :=
  ComputedPolynomialCell.computed_actual_integral (51/26) 9 12 witness checked G u hd
#print axioms checked
#print axioms actual_integral
end
end Gebendorfer.RadenkovicGutman.CompactAnchor003Cell242
