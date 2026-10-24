/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD2Long00CompositionalNode069
import Proofs.RadenkovicGutmanD2Long00CompositionalNode070
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e071 : NestedArithmetic.Expr 3 := .plus e069 e070
noncomputable def p071 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[0,-216,0],[-216,-180,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0]],[[-4860,-5292,0],[-5292,-1740,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-106920,-46836,0],[-46836,-6860,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-1001268,-218996,0],[-218996,-14460,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-5408820,-627308,0],[-627308,-18040,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-19108152,-1187276,0],[-1187276,-13880,0],[0,0]],[[0,0,0],[0,0],[0]],[[-47256244,-1550220,0],[-1550220,-6620],[0]],[[0,0,0],[0,0],[0]],[[-85302504,-1431584,0],[-1431584,-1900],[0]],[[0,0,0],[0,0],[0]],[[-115480076,-946672,0],[-946672,-300],[0]],[[0,0,0],[0,0],[0]],[[-119347492,-449052,0],[-449052,-20],[0]],[[0,0,0],[0,0],[0]],[[-95208928,-151308,0],[-151308,0],[0]],[[0,0],[0]],[[-58956632,-35308],[-35308]],[[0,0],[0]],[[-28355228,-5420],[-5420]],[[0,0],[0]],[[-10542304,-492],[-492]],[[0,0],[0]],[[-2996548,-20],[-20]],[[0,0],[0]],[[-638360,0],[0]],[[0]],[[-98564]],[[0]],[[-10408]],[[0]],[[-672]],[[0]],[[-20]],[[0]],[[0]]]
theorem step071 : p071=NestedHorner.add p069 p070 := by decide +kernel
#print axioms step071
theorem h071 : NestedArithmetic.compile e071=p071 := StagedExprCompile.compile_plus e071 e069 e070 p069 p070 p071 rfl h069 h070 step071
#print axioms h071
end Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
