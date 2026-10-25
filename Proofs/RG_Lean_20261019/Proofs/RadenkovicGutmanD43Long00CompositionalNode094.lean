/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD43Long00CompositionalNode035
import Proofs.RadenkovicGutmanD43Long00CompositionalNode061
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree43Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e094 : NestedArithmetic.Expr 3 := .times e035 e061
noncomputable def p094 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0,0]],[[0,0,-16641],[0,-33282,10578],[-16641,10578]],[[0,0,0],[0,0,0],[0,0]],[[0,-453951,-49020],[-453951,92364,45838],[-49020,45838]],[[0,0,0],[0,0,0],[0,0]],[[-2779434,-2332449,176429],[-2332449,1685686,56416],[176429,56416]],[[0,0,0],[0,0,0],[0,0]],[[-19135602,2395917,993730],[2395917,5668604,24682],[993730,24682]],[[0,0,0],[0,0,0],[0,0]],[[3438882,46160414,1848226],[46160414,9034816,3526],[1848226,3526]],[[0,0,0],[0,0],[0]],[[479629224,157141049,1780286],[157141049,8045644],[1780286]],[[0,0,0],[0,0],[0]],[[2403757104,289089215,975025],[289089215,4199638],[975025]],[[0,0,0],[0,0],[0]],[[6530428060,338715816,305558],[338715816,1274004],[305558]],[[0,0,0],[0,0],[0]],[[11743039162,268430811,51041],[268430811,207862],[51041]],[[0,0,0],[0,0],[0]],[[15057712222,147302821,3526],[147302821,14104],[3526]],[[0,0],[0]],[[14285429212,56069420],[56069420]],[[0,0],[0]],[[10224019442,14531635],[14531635]],[[0,0],[0]],[[5568647318,2446571],[2446571]],[[0,0],[0]],[[2309329620,241273],[241273]],[[0,0],[0]],[[723637712,10578],[10578]],[[0]],[[168380088]],[[0]],[[28185038]],[[0]],[[3206854]],[[0]],[[221966]],[[0]],[[7052]]]
theorem step094 : p094=NestedArithmetic.mul p035 p061 := by decide +kernel
#print axioms step094
theorem h094 : NestedArithmetic.compile e094=p094 := StagedExprCompile.compile_times e094 e035 e061 p035 p061 p094 rfl h035 h061 step094
#print axioms h094
end Gebendorfer.RadenkovicGutman.FixedDegree43Long00Compositional
