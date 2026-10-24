/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD2Long00CompositionalNode108
import Proofs.RadenkovicGutmanD2Long00CompositionalNode109
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e110 : NestedArithmetic.Expr 3 := .plus e108 e109
noncomputable def p110 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,4]],[[0,0],[0,0,0],[0,0,0]],[[0,0,36],[0,0,120],[36,120,8]],[[0,0,0],[0,0,0],[0,0,0]],[[324,1080,1212],[1080,3312,592],[1212,592,4]],[[0,0,0],[0,0,0],[0,0]],[[23760,36072,8140],[36072,25896,1096],[8140,1096]],[[0,0,0],[0,0,0],[0,0]],[[476496,314640,25116],[314640,85280,976],[25116,976]],[[0,0,0],[0,0,0],[0,0]],[[4220472,1370776,43872],[1370776,155848,440],[43872,440]],[[0,0,0],[0,0,0],[0,0]],[[21497728,3629232,47424],[3629232,175152,96],[47424,96]],[[0,0,0],[0,0,0],[0,0]],[[71586000,6397752,33092],[6397752,126624,8],[33092,8]],[[0,0,0],[0,0],[0]],[[167424588,7892600,15136],[7892600,59728],[15136]],[[0,0,0],[0,0],[0]],[[287414920,7010056,4500],[7010056,18184],[4500]],[[0,0,0],[0,0],[0]],[[372644344,4550664,836],[4550664,3424],[836]],[[0,0,0],[0,0],[0]],[[371818856,2169992,88],[2169992,360],[88]],[[0,0,0],[0,0],[0]],[[288951328,756784,4],[756784,16],[4]],[[0,0],[0]],[[176073304,190104],[190104]],[[0,0],[0]],[[84307860,33360],[33360]],[[0,0],[0]],[[31645952,3864],[3864]],[[0,0],[0]],[[9243276,264],[264]],[[0,0],[0]],[[2072184,8],[8]],[[0]],[[348588]],[[0]],[[42424]],[[0]],[[3512]],[[0]],[[176]],[[0]],[[4]]]
theorem step110 : p110=NestedHorner.add p108 p109 := by decide +kernel
#print axioms step110
theorem h110 : NestedArithmetic.compile e110=p110 := StagedExprCompile.compile_plus e110 e108 e109 p108 p109 p110 rfl h108 h109 step110
#print axioms h110
end Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
