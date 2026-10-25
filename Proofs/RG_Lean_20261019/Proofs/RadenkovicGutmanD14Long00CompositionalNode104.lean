/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD14Long00CompositionalNode092
import Proofs.RadenkovicGutmanD14Long00CompositionalNode103
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree14Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e104 : NestedArithmetic.Expr 3 := .plus e092 e103
noncomputable def p104 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0]],[[0,0,0],[0,-1008,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-9072,-9072,0],[-9072,-8484,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-236628,-100548,0],[-100548,-27496,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-2298996,-473256,0],[-473256,-43876,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-12121536,-1249500,0],[-1249500,-36904,0],[0,0]],[[0,0,0],[0,0],[0]],[[-40262404,-2058952,0],[-2058952,-15568],[0]],[[0,0,0],[0,0],[0]],[[-91001484,-2219532,0],[-2219532,-2072],[0]],[[0,0,0],[0,0],[0]],[[-146284824,-1582672,0],[-1582672,700],[0]],[[0,0,0],[0,0],[0]],[[-171518144,-725032,0],[-725032,280],[0]],[[0,0,0],[0,0],[0]],[[-148383676,-187712,0],[-187712,28],[0]],[[0,0],[0]],[[-94551128,-9772],[-9772]],[[0,0],[0]],[[-43470616,10360],[10360]],[[0,0],[0]],[[-13546960,3556],[3556]],[[0,0],[0]],[[-2271612,504],[504]],[[0,0],[0]],[[146468,28],[28]],[[0]],[[201096]],[[0]],[[57456]],[[0]],[[8876]],[[0]],[[756]],[[0]],[[28]]]
theorem step104 : p104=NestedHorner.add p092 p103 := by decide +kernel
#print axioms step104
theorem h104 : NestedArithmetic.compile e104=p104 := StagedExprCompile.compile_plus e104 e092 e103 p092 p103 p104 rfl h092 h103 step104
#print axioms h104
end Gebendorfer.RadenkovicGutman.FixedDegree14Long00Compositional
