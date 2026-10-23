/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor000Cell242
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 9
def witness : ComputedPolynomialCell.Witness := {
  a := (317349/8192)
  b := (1396335/32768)
  s := [(154514683111/18014398509481984),(-1460823426407/576460752303423488),(116479680347/288230376151711744)]
  L := [(75657017661224596397229/75557863725914323419136),(-1143897765/4398046511104),(254544943/6597069766656),(-1365153/274877906944),(195149/412316860416)]
  c := (550353008469/549755813888)
  R := (54285051399/100000000000000)
  total := (2311239560093/1000000000000000)
  k := 0
  n := 32
  sFloor := (1858302896919/576460752303423488)
  nFloor := 15567280450611790380981535891696022612107674604204499980215646494392320
  eFloor := 15546611714545838202002230478348695087872128628839890011612820554121216
}

#check "COMPACT_WITNESS_READY"
theorem checked : ComputedPolynomialCell.checks data witness=true := by decide +kernel
#check "COMPACT_CHECK_PASSED"

noncomputable section
theorem actual_integral {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 9)
        (CoreQuotient.fused G u 9 9) ((51/26 : ℚ) : ℝ) y :=
  ComputedPolynomialCell.computed_actual_integral (51/26) 9 9 witness checked G u hd
#print axioms checked
#print axioms actual_integral
end
end Gebendorfer.RadenkovicGutman.CompactAnchor000Cell242
