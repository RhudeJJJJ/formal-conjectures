/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD41Long00CompositionalNode035
import Proofs.RadenkovicGutmanD41Long00CompositionalNode074
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree41Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e076 : NestedArithmetic.Expr 3 := .times e035 e074
noncomputable def p076 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0]],[[0,0,-15129],[0,-30258],[-15129]],[[0,0,0],[0,0],[0]],[[0,-499257,-131118],[-499257,-262236],[-131118]],[[0,0,0],[0,0],[0]],[[-4084830,-5582601,-445465],[-5582601,-890930],[-445465]],[[0,0,0],[0,0],[0]],[[-55826010,-26672427,-769898],[-26672427,-1539796],[-769898]],[[0,0,0],[0,0],[0]],[[-340311726,-72198950,-746364],[-72198950,-1492728],[-746364]],[[0,0,0],[0,0],[0]],[[-1231863696,-123928363,-420250],[-123928363,-840500],[-420250]],[[0,0,0],[0,0],[0]],[[-2973009876,-142779097,-136161],[-142779097,-272322],[-136161]],[[0,0,0],[0,0],[0]],[[-5086900996,-113696116,-23534],[-113696116,-47068],[-23534]],[[0,0,0],[0,0],[0]],[[-6398568486,-63304779,-1681],[-63304779,-3362],[-1681]],[[0,0],[0]],[[-6048167398,-24557729],[-24557729]],[[0,0],[0]],[[-4349970768,-6498746],[-6498746]],[[0,0],[0]],[[-2392698418,-1117865],[-1117865]],[[0,0],[0]],[[-1004932058,-112627],[-112627]],[[0,0],[0]],[[-319437068,-5043],[-5043]],[[0]],[[-75463452]],[[0]],[[-12829392]],[[0]],[[-1482642]],[[0]],[[-104222]],[[0]],[[-3362]]]
theorem step076 : p076=NestedArithmetic.mul p035 p074 := by decide +kernel
#print axioms step076
theorem h076 : NestedArithmetic.compile e076=p076 := StagedExprCompile.compile_times e076 e035 e074 p035 p074 p076 rfl h035 h074 step076
#print axioms h076
end Gebendorfer.RadenkovicGutman.FixedDegree41Long00Compositional
