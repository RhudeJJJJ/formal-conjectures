/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD29Long00CompositionalNode035
import Proofs.RadenkovicGutmanD29Long00CompositionalNode061
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree29Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e094 : NestedArithmetic.Expr 3 := .times e035 e061
noncomputable def p094 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0,0]],[[0,0,-7569],[0,-15138,4698],[-7569,4698]],[[0,0,0],[0,0,0],[0,0]],[[0,-207495,-23316],[-207495,37932,20358],[-23316,20358]],[[0,0,0],[0,0,0],[0,0]],[[-1282554,-1101681,73109],[-1101681,738166,25056],[73109,25056]],[[0,0,0],[0,0,0],[0,0]],[[-9156402,749853,432274],[749853,2499452,10962],[432274,10962]],[[0,0,0],[0,0,0],[0,0]],[[-2482110,19650574,812058],[19650574,3995040,1566],[812058,1566]],[[0,0,0],[0,0],[0]],[[198504072,68330873,785726],[68330873,3563404],[785726]],[[0,0,0],[0,0],[0]],[[1032552192,126710831,431433],[126710831,1861974],[431433]],[[0,0,0],[0,0],[0]],[[2840422748,149094104,135430],[149094104,565268],[135430]],[[0,0,0],[0,0],[0]],[[5140042650,118472163,22649],[118472163,92278],[22649]],[[0,0,0],[0,0],[0]],[[6616314446,65132173,1566],[65132173,6264],[1566]],[[0,0],[0]],[[6293328396,24825508],[24825508]],[[0,0],[0]],[[4512597026,6440755],[6440755]],[[0,0],[0]],[[2461359862,1085267],[1085267]],[[0,0],[0]],[[1021877524,107097],[107097]],[[0,0],[0]],[[320499648,4698],[4698]],[[0]],[[74631384]],[[0]],[[12500334]],[[0]],[[1423030]],[[0]],[[98542]],[[0]],[[3132]]]
theorem step094 : p094=NestedArithmetic.mul p035 p061 := by decide +kernel
#print axioms step094
theorem h094 : NestedArithmetic.compile e094=p094 := StagedExprCompile.compile_times e094 e035 e061 p035 p061 p094 rfl h035 h061 step094
#print axioms h094
end Gebendorfer.RadenkovicGutman.FixedDegree29Long00Compositional
