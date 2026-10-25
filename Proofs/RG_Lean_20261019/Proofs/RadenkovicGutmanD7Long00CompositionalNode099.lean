/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD7Long00CompositionalNode096
import Proofs.RadenkovicGutmanD7Long00CompositionalNode098
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree07Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e099 : NestedArithmetic.Expr 3 := .plus e096 e098
noncomputable def p099 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,294],[0,294,-70]],[[0,0,0],[0,0,0],[0,0]],[[0,0,3528],[0,12411,56],[3528,56]],[[0,0,0],[0,0,0],[0,0]],[[14175,101493,20874],[101493,68628,-1610],[20874,-1610]],[[0,0,0],[0,0,0],[0,0]],[[923265,934416,49532],[934416,146951,-2170],[49532,-2170]],[[0,0,0],[0,0,0],[0,0]],[[10190880,3772251,58338],[3772251,143080,-924],[58338,-924]],[[0,0,0],[0,0,0],[0,0]],[[54704559,8777706,32438],[8777706,39424,-126],[32438,-126]],[[0,0,0],[0,0],[0]],[[179858035,13022205,2646],[13022205,-42882],[2646]],[[0,0,0],[0,0],[0]],[[400347668,12845140,-6384],[12845140,-44345],[-6384]],[[0,0,0],[0,0],[0]],[[636364820,8481298,-3402],[8481298,-17388],[-3402]],[[0,0,0],[0,0],[0]],[[744619365,3623592,-714],[3623592,-3241],[-714]],[[0,0,0],[0,0],[0]],[[652033844,872067,-56],[872067,-238],[-56]],[[0,0],[0]],[[429836386,33740],[33740]],[[0,0],[0]],[[212397276,-48181],[-48181]],[[0,0],[0]],[[77250817,-15442],[-15442]],[[0,0],[0]],[[19779235,-2093],[-2093]],[[0,0],[0]],[[3157980,-112],[-112]],[[0]],[[161840]],[[0]],[[-52101]],[[0]],[[-13489]],[[0]],[[-1379]],[[0]],[[-56]]]
theorem step099 : p099=NestedHorner.add p096 p098 := by decide +kernel
#print axioms step099
theorem h099 : NestedArithmetic.compile e099=p099 := StagedExprCompile.compile_plus e099 e096 e098 p096 p098 p099 rfl h096 h098 step099
#print axioms h099
end Gebendorfer.RadenkovicGutman.FixedDegree07Long00Compositional
