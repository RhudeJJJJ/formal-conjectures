/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD30Long00CompositionalNode071
import Proofs.RadenkovicGutmanD30Long00CompositionalNode072
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree30Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e073 : NestedArithmetic.Expr 3 := .plus e071 e072
noncomputable def p073 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[0,-48600,0],[-48600,-10260,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0]],[[-821340,-918540,0],[-918540,-121860,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-16822080,-7385580,0],[-7385580,-587580,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-152731980,-33534180,0],[-33534180,-1492020,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-817957620,-96174900,0],[-96174900,-2182440,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-2900793840,-184754940,0],[-184754940,-1910040,0],[0,0]],[[0,0,0],[0,0],[0]],[[-7251007260,-246175860,0],[-246175860,-1007340],[0]],[[0,0,0],[0,0],[0]],[[-13276595640,-232323840,0],[-232323840,-312420],[0]],[[0,0,0],[0,0],[0]],[[-18261219660,-156934560,0],[-156934560,-52380],[0]],[[0,0,0],[0,0],[0]],[[-19184839980,-75950940,0],[-75950940,-3660],[0]],[[0,0,0],[0,0],[0]],[[-15555510960,-26071860,0],[-26071860,0],[0]],[[0,0],[0]],[[-9785365800,-6188700],[-6188700]],[[0,0],[0]],[[-4777518780,-964980],[-964980]],[[0,0],[0]],[[-1801665960,-88860],[-88860]],[[0,0],[0]],[[-518992140,-3660],[-3660]],[[0,0],[0]],[[-111954600,0],[0]],[[0]],[[-17489700]],[[0]],[[-1867200]],[[0]],[[-121800]],[[0]],[[-3660]],[[0]],[[0]]]
theorem step073 : p073=NestedHorner.add p071 p072 := by decide +kernel
#print axioms step073
theorem h073 : NestedArithmetic.compile e073=p073 := StagedExprCompile.compile_plus e073 e071 e072 p071 p072 p073 rfl h071 h072 step073
#print axioms h073
end Gebendorfer.RadenkovicGutman.FixedDegree30Long00Compositional
