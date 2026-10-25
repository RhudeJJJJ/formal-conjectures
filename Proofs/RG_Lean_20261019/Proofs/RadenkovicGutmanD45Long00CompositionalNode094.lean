/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD45Long00CompositionalNode035
import Proofs.RadenkovicGutmanD45Long00CompositionalNode061
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree45Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e094 : NestedArithmetic.Expr 3 := .times e035 e061
noncomputable def p094 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0,0]],[[0,0,-18225],[0,-36450,11610],[-18225,11610]],[[0,0,0],[0,0,0],[0,0]],[[0,-496935,-53460],[-496935,102060,50310],[-53460,50310]],[[0,0,0],[0,0,0],[0,0]],[[-3039930,-2545425,194805],[-2545425,1852470,61920],[194805,61920]],[[0,0,0],[0,0,0],[0,0]],[[-20856690,2699325,1092690],[2699325,6225660,27090],[1092690,27090]],[[0,0,0],[0,0,0],[0,0]],[[4663170,50852430,2030490],[50852430,9920160,3870],[2030490,3870]],[[0,0,0],[0,0],[0]],[[529639560,172795545,1955070],[172795545,8832780],[1955070]],[[0,0,0],[0,0],[0]],[[2646034560,317665935,1070505],[317665935,4610070],[1070505]],[[0,0,0],[0,0],[0]],[[7180828380,372058200,335430],[372058200,1398420],[335430]],[[0,0,0],[0,0],[0]],[[12905412570,294784515,56025],[294784515,228150],[56025]],[[0,0,0],[0,0],[0]],[[16542553230,161737965,3870],[161737965,15480],[3870]],[[0,0],[0]],[[15690490380,61556580],[61556580]],[[0,0],[0]],[[11227733730,15952275],[15952275]],[[0,0],[0]],[[6114554550,2685555],[2685555]],[[0,0],[0]],[[2535464340,264825],[264825]],[[0,0],[0]],[[794433600,11610],[11610]],[[0]],[[184840920]],[[0]],[[30938670]],[[0]],[[3519990]],[[0]],[[243630]],[[0]],[[7740]]]
theorem step094 : p094=NestedArithmetic.mul p035 p061 := by decide +kernel
#print axioms step094
theorem h094 : NestedArithmetic.compile e094=p094 := StagedExprCompile.compile_times e094 e035 e061 p035 p061 p094 rfl h035 h061 step094
#print axioms h094
end Gebendorfer.RadenkovicGutman.FixedDegree45Long00Compositional
