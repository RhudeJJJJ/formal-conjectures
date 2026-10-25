/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD21Long00CompositionalNode092
import Proofs.RadenkovicGutmanD21Long00CompositionalNode103
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree21Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e104 : NestedArithmetic.Expr 3 := .plus e092 e103
noncomputable def p104 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0]],[[0,0,0],[0,-1512,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-13608,-13608,0],[-13608,-12726,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-354942,-150822,0],[-150822,-41244,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-3448494,-709884,0],[-709884,-65814,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-18182304,-1874250,0],[-1874250,-55356,0],[0,0]],[[0,0,0],[0,0],[0]],[[-60393606,-3088428,0],[-3088428,-23352],[0]],[[0,0,0],[0,0],[0]],[[-136502226,-3329298,0],[-3329298,-3108],[0]],[[0,0,0],[0,0],[0]],[[-219427236,-2374008,0],[-2374008,1050],[0]],[[0,0,0],[0,0],[0]],[[-257277216,-1087548,0],[-1087548,420],[0]],[[0,0,0],[0,0],[0]],[[-222575514,-281568,0],[-281568,42],[0]],[[0,0],[0]],[[-141826692,-14658],[-14658]],[[0,0],[0]],[[-65205924,15540],[15540]],[[0,0],[0]],[[-20320440,5334],[5334]],[[0,0],[0]],[[-3407418,756],[756]],[[0,0],[0]],[[219702,42],[42]],[[0]],[[301644]],[[0]],[[86184]],[[0]],[[13314]],[[0]],[[1134]],[[0]],[[42]]]
theorem step104 : p104=NestedHorner.add p092 p103 := by decide +kernel
#print axioms step104
theorem h104 : NestedArithmetic.compile e104=p104 := StagedExprCompile.compile_plus e104 e092 e103 p092 p103 p104 rfl h092 h103 step104
#print axioms h104
end Gebendorfer.RadenkovicGutman.FixedDegree21Long00Compositional
