/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD43Long00CompositionalNode033
import Proofs.RadenkovicGutmanD43Long00CompositionalNode061
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree43Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e089 : NestedArithmetic.Expr 3 := .times e033 e061
noncomputable def p089 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,5547],[0,5547,-3526]],[[0,0,0],[0,0,0],[0,0]],[[0,-49923,49923],[-49923,183051,-39431],[49923,-39431]],[[0,0,0],[0,0,0],[0,0]],[[-463239,549153,63855],[549153,111198,-139664],[63855,-139664]],[[0,0,0],[0,0,0],[0,0]],[[207819,2580516,-558054],[2580516,-2722201,-142201],[-558054,-142201]],[[0,0,0],[0,0,0],[0,0]],[[17733114,-6183013,-2027579],[-6183013,-8957158,-54567],[-2027579,-54567]],[[0,0,0],[0,0,0],[0,0]],[[50220087,-60850590,-3055236],[-60850590,-13041900,-7052],[-3055236,-7052]],[[0,0,0],[0,0],[0]],[[-104895877,-176340721,-2534205],[-176340721,-10599070],[-2534205]],[[0,0,0],[0,0],[0]],[[-993790974,-290455454,-1236594],[-290455454,-5096145],[-1236594]],[[0,0,0],[0,0],[0]],[[-3053234264,-311916023,-353073],[-311916023,-1438178],[-353073]],[[0,0,0],[0,0],[0]],[[-5722403837,-230157629,-54567],[-230157629,-220117],[-54567]],[[0,0,0],[0,0],[0]],[[-7455188812,-118997598,-3526],[-118997598,-14104],[-3526]],[[0,0],[0]],[[-7117202276,-43071810],[-43071810]],[[0,0],[0]],[[-5105944184,-10692552],[-10692552]],[[0,0],[0]],[[-2783380755,-1734362],[-1734362]],[[0,0],[0]],[[-1154578509,-165550],[-165550]],[[0,0],[0]],[[-361815330,-7052],[-7052]],[[0]],[[-84190044]],[[0]],[[-14092519]],[[0]],[[-1603427]],[[0]],[[-110983]],[[0]],[[-3526]]]
theorem step089 : p089=NestedArithmetic.mul p033 p061 := by decide +kernel
#print axioms step089
theorem h089 : NestedArithmetic.compile e089=p089 := StagedExprCompile.compile_times e089 e033 e061 p033 p061 p089 rfl h033 h061 step089
#print axioms h089
end Gebendorfer.RadenkovicGutman.FixedDegree43Long00Compositional
