/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD27Long00CompositionalNode033
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree27Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e113 : NestedArithmetic.Expr 3 := .pow e033 2
noncomputable def p113 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,729]],[[0,0],[0,0,0],[0,0]],[[0,0,0],[0,-13122,13122],[0,13122]],[[0,0,0],[0,0,0],[0,0]],[[59049,-118098,59049],[-118098,122472,34992],[59049,34992]],[[0,0,0],[0,0,0],[0,0]],[[-39366,-275562,314928],[-275562,873342,32076],[314928,32076]],[[0,0,0],[0,0,0],[0,0]],[[-2184813,2007666,708588],[2007666,2166588,11664],[708588,11664]],[[0,0,0],[0,0,0],[0,0]],[[-6014250,12579624,874800],[12579624,2851848,1458],[874800,1458]],[[0,0,0],[0,0],[0]],[[12659085,33284682,645894],[33284682,2219076],[645894]],[[0,0,0],[0,0],[0]],[[120112956,53238870,291600],[53238870,1048302],[291600]],[[0,0,0],[0,0],[0]],[[375270246,56929068,78732],[56929068,294516],[78732]],[[0,0,0],[0,0],[0]],[[721574406,42363648,11664],[42363648,45198],[11664]],[[0,0,0],[0,0],[0]],[[971162136,22238874,729],[22238874,2916],[729]],[[0,0],[0]],[[963032328,8201250],[8201250]],[[0,0],[0]],[[720596088,2077650],[2077650]],[[0,0],[0]],[[410900850,344088],[344088]],[[0,0],[0]],[[178631973,33534],[33534]],[[0,0],[0]],[[58731156,1458],[1458]],[[0]],[[14345262]],[[0]],[[2520882]],[[0]],[[301077]],[[0]],[[21870]],[[0]],[[729]]]
theorem step113 : p113=NestedArithmetic.power p033 2 := by decide +kernel
#print axioms step113
theorem h113 : NestedArithmetic.compile e113=p113 := StagedExprCompile.compile_pow 2 e113 e033 p033 p113 rfl h033 step113
#print axioms h113
end Gebendorfer.RadenkovicGutman.FixedDegree27Long00Compositional
