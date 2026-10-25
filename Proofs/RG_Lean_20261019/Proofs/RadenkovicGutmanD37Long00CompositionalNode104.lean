/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD37Long00CompositionalNode092
import Proofs.RadenkovicGutmanD37Long00CompositionalNode103
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree37Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e104 : NestedArithmetic.Expr 3 := .plus e092 e103
noncomputable def p104 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0]],[[0,0,0],[0,-2664,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-23976,-23976,0],[-23976,-22422,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-625374,-265734,0],[-265734,-72668,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-6075918,-1250748,0],[-1250748,-115958,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-32035488,-3302250,0],[-3302250,-97532,0],[0,0]],[[0,0,0],[0,0],[0]],[[-106407782,-5441516,0],[-5441516,-41144],[0]],[[0,0,0],[0,0],[0]],[[-240503922,-5865906,0],[-5865906,-5476],[0]],[[0,0,0],[0,0],[0]],[[-386609892,-4182776,0],[-4182776,1850],[0]],[[0,0,0],[0,0],[0]],[[-453297952,-1916156,0],[-1916156,740],[0]],[[0,0,0],[0,0],[0]],[[-392156858,-496096,0],[-496096,74],[0]],[[0,0],[0]],[[-249885124,-25826],[-25826]],[[0,0],[0]],[[-114886628,27380],[27380]],[[0,0],[0]],[[-35802680,9398],[9398]],[[0,0],[0]],[[-6003546,1332],[1332]],[[0,0],[0]],[[387094,74],[74]],[[0]],[[531468]],[[0]],[[151848]],[[0]],[[23458]],[[0]],[[1998]],[[0]],[[74]]]
theorem step104 : p104=NestedHorner.add p092 p103 := by decide +kernel
#print axioms step104
theorem h104 : NestedArithmetic.compile e104=p104 := StagedExprCompile.compile_plus e104 e092 e103 p092 p103 p104 rfl h092 h103 step104
#print axioms h104
end Gebendorfer.RadenkovicGutman.FixedDegree37Long00Compositional
