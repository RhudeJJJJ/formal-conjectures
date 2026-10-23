/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor002Cell045
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 11
def witness : ComputedPolynomialCell.Witness := {
  a := (1194217/4398046511104)
  b := (656819/2199023255552)
  s := [(2199023245263/2199023255552),(-2059/2199023255552),(-51/1099511627776)]
  L := [(532237841238543945682506615/166153499473114484112975882535043072),(2269053079597/3541774862152233910272),(56725993313/1770887431076116955136),(5/221360928884514619392),(-5/110680464442257309696)]
  c := (1890888658943/590295810358705651712)
  R := (-122244296463899/12500000000000)
  total := (-264231449/1000000000000000)
  k := 29
  n := 32
  sFloor := (1099511621551/2199023255552)
  nFloor := (1413064391233/302231454903657293676544)
  eFloor := (1031995198571/302231454903657293676544)
}

#check "COMPACT_WITNESS_READY"
theorem checked : ComputedPolynomialCell.checks data witness=true := by decide +kernel
#check "COMPACT_CHECK_PASSED"

noncomputable section
theorem actual_integral {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 11)
        (CoreQuotient.fused G u 9 11) ((51/26 : ℚ) : ℝ) y :=
  ComputedPolynomialCell.computed_actual_integral (51/26) 9 11 witness checked G u hd
#print axioms checked
#print axioms actual_integral
end
end Gebendorfer.RadenkovicGutman.CompactAnchor002Cell045
