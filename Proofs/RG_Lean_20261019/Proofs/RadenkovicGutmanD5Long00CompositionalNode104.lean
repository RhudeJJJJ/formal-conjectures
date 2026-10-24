/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD5Long00CompositionalNode092
import Proofs.RadenkovicGutmanD5Long00CompositionalNode103
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree05Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e104 : NestedArithmetic.Expr 3 := .plus e092 e103
noncomputable def p104 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0]],[[0,0,0],[0,-360,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-3240,-3240,0],[-3240,-3030,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-84510,-35910,0],[-35910,-9820,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-821070,-169020,0],[-169020,-15670,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-4329120,-446250,0],[-446250,-13180,0],[0,0]],[[0,0,0],[0,0],[0]],[[-14379430,-735340,0],[-735340,-5560],[0]],[[0,0,0],[0,0],[0]],[[-32500530,-792690,0],[-792690,-740],[0]],[[0,0,0],[0,0],[0]],[[-52244580,-565240,0],[-565240,250],[0]],[[0,0,0],[0,0],[0]],[[-61256480,-258940,0],[-258940,100],[0]],[[0,0,0],[0,0],[0]],[[-52994170,-67040,0],[-67040,10],[0]],[[0,0],[0]],[[-33768260,-3490],[-3490]],[[0,0],[0]],[[-15525220,3700],[3700]],[[0,0],[0]],[[-4838200,1270],[1270]],[[0,0],[0]],[[-811290,180],[180]],[[0,0],[0]],[[52310,10],[10]],[[0]],[[71820]],[[0]],[[20520]],[[0]],[[3170]],[[0]],[[270]],[[0]],[[10]]]
theorem step104 : p104=NestedHorner.add p092 p103 := by decide +kernel
#print axioms step104
theorem h104 : NestedArithmetic.compile e104=p104 := StagedExprCompile.compile_plus e104 e092 e103 p092 p103 p104 rfl h092 h103 step104
#print axioms h104
end Gebendorfer.RadenkovicGutman.FixedDegree05Long00Compositional
