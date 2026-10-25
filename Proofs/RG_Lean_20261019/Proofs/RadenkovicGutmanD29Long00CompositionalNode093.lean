/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD29Long00CompositionalNode033
import Proofs.RadenkovicGutmanD29Long00CompositionalNode064
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree29Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e093 : NestedArithmetic.Expr 3 := .times e033 e064
noncomputable def p093 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,841]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,20184],[0,20184,58]],[[0,0,0],[0,0,0],[0,0]],[[-68121,-45414,113535],[-45414,439002,63278],[113535,63278]],[[0,0,0],[0,0,0],[0,0]],[[-1866672,1725732,685908],[1725732,2612436,66700],[685908,66700]],[[0,0,0],[0,0,0],[0,0]],[[-8006175,16918020,1720512],[16918020,6436318,27782],[1720512,27782]],[[0,0,0],[0,0,0],[0,0]],[[19268934,67615066,2338850],[67615066,8585044,4292],[2338850,4292]],[[0,0,0],[0,0,0],[0,0]],[[275810909,155610636,1884478],[155610636,6791104,116],[1884478,116]],[[0,0,0],[0,0],[0]],[[1143062376,232552972,924346],[232552972,3276884],[924346]],[[0,0,0],[0,0],[0]],[[2818536506,238744472,272136],[238744472,952302],[272136]],[[0,0,0],[0,0],[0]],[[4772478264,173021482,44950],[173021482,156252],[44950]],[[0,0,0],[0,0],[0]],[[5889381538,89370518,3451],[89370518,12122],[3451]],[[0,0,0],[0,0],[0]],[[5459239908,32752194,58],[32752194,232],[58]],[[0,0],[0]],[[3861518896,8347360],[8347360]],[[0,0],[0]],[[2097942360,1418100],[1418100]],[[0,0],[0]],[[874884441,147668],[147668]],[[0,0],[0]],[[277890528,7830],[7830]],[[0,0],[0]],[[66151842,116],[116]],[[0]],[[11475184]],[[0]],[[1383097]],[[0]],[[106372]],[[0]],[[4379]],[[0]],[[58]]]
theorem step093 : p093=NestedArithmetic.mul p033 p064 := by decide +kernel
#print axioms step093
theorem h093 : NestedArithmetic.compile e093=p093 := StagedExprCompile.compile_times e093 e033 e064 p033 p064 p093 rfl h033 h064 step093
#print axioms h093
end Gebendorfer.RadenkovicGutman.FixedDegree29Long00Compositional
