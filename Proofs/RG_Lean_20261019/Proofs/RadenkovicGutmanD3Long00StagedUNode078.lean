/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00StagedUNode034
import Proofs.RadenkovicGutmanD3Long00StagedUNode052
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e078 : NestedArithmetic.Expr 3 := .times e034 e052
noncomputable def p078 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,-27],[0,-27]],[[0,0,0],[0,0,0],[0,0]],[[0,-243,-243],[-243,-972,-117],[-243,-117]],[[0,0,0],[0,0,0],[0,0]],[[-4374,-9720,-1701],[-9720,-6804,-144],[-1701,-144]],[[0,0,0],[0,0,0],[0,0]],[[-107892,-81000,-4698],[-81000,-18792,-63],[-4698,-63]],[[0,0,0],[0,0,0],[0,0]],[[-964224,-320526,-6813],[-320526,-27252,-9],[-6813,-9]],[[0,0,0],[0,0],[0]],[[-4682772,-749034,-5724],[-749034,-22896],[-5724]],[[0,0,0],[0,0],[0]],[[-14482422,-1138752,-2871],[-1138752,-11484],[-2871]],[[0,0,0],[0,0],[0]],[[-30950496,-1183770,-846],[-1183770,-3384],[-846]],[[0,0,0],[0,0],[0]],[[-47938104,-862893,-135],[-862893,-540],[-135]],[[0,0,0],[0,0],[0]],[[-55414926,-444933,-9],[-444933,-36],[-9]],[[0,0],[0]],[[-48675906,-161361],[-161361]],[[0,0],[0]],[[-32814126,-40230],[-40230]],[[0,0],[0]],[[-17035200,-6561],[-6561]],[[0,0],[0]],[[-6791328,-630],[-630]],[[0,0],[0]],[[-2058930,-27],[-27]],[[0]],[[-465804]],[[0]],[[-76104]],[[0]],[[-8478]],[[0]],[[-576]],[[0]],[[-18]]]
theorem step078 : p078=NestedArithmetic.mul p034 p052 := by decide +kernel
#print axioms step078
theorem h078 : NestedArithmetic.compile e078=p078 := by
  change NestedArithmetic.mul (NestedArithmetic.compile e034) (NestedArithmetic.compile e052)=p078
  rw [h034,h052]
  exact step078.symm
#print axioms h078
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
