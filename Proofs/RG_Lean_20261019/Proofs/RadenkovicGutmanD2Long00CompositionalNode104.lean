/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD2Long00CompositionalNode093
import Proofs.RadenkovicGutmanD2Long00CompositionalNode103
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e104 : NestedArithmetic.Expr 3 := .plus e093 e103
noncomputable def p104 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0]],[[0,0,0],[0,-144,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-1296,-1296,0],[-1296,-1248,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-34128,-14688,0],[-14688,-4240,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-336960,-71280,0],[-71280,-7328,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-1815888,-196320,0],[-196320,-7104,0],[0,0]],[[0,0,0],[0,0],[0]],[[-6205744,-343216,0],[-343216,-4000],[0]],[[0,0,0],[0,0],[0]],[[-14551648,-402880,0],[-402880,-1296],[0]],[[0,0,0],[0,0],[0]],[[-24535744,-326816,0],[-326816,-224],[0]],[[0,0,0],[0,0],[0]],[[-30636528,-185280,0],[-185280,-16],[0]],[[0,0,0],[0,0],[0]],[[-28856800,-73136,0],[-73136,0],[0]],[[0,0],[0]],[[-20721504,-19680],[-19680]],[[0,0],[0]],[[-11390464,-3440],[-3440]],[[0,0],[0]],[[-4782896,-352],[-352]],[[0,0],[0]],[[-1520240,-16],[-16]],[[0,0],[0]],[[-359136,0],[0]],[[0]],[[-61056]],[[0]],[[-7056]],[[0]],[[-496]],[[0]],[[-16]],[[0]],[[0]]]
theorem step104 : p104=NestedHorner.add p093 p103 := by decide +kernel
#print axioms step104
theorem h104 : NestedArithmetic.compile e104=p104 := StagedExprCompile.compile_plus e104 e093 e103 p093 p103 p104 rfl h093 h103 step104
#print axioms h104
end Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
