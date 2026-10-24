/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00StagedUNode057
import Proofs.RadenkovicGutmanD3Long00StagedUNode051
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e058 : NestedArithmetic.Expr 3 := .times e057 e051
noncomputable def p058 : NestedHorner.Poly 3 := [[[],[]],[[0],[0,-2]],[[0,0],[0]],[[-18,-18],[-18]],[[0,0],[0]],[[-318,-48],[-48]],[[0,0],[0]],[[-1394,-44],[-44]],[[0,0],[0]],[[-2860,-16],[-16]],[[0,0],[0]],[[-3288,-2],[-2]],[[0]],[[-2272]],[[0]],[[-962]],[[0]],[[-244]],[[0]],[[-34]],[[0]],[[-2]]]
theorem step058 : p058=NestedArithmetic.mul p057 p051 := by decide +kernel
#print axioms step058
theorem h058 : NestedArithmetic.compile e058=p058 := StagedExprCompile.compile_times e058 e057 e051 p057 p051 p058 rfl h057 h051 step058
#print axioms h058
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
