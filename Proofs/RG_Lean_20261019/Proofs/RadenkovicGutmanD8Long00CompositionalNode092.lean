/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD8Long00CompositionalNode089
import Proofs.RadenkovicGutmanD8Long00CompositionalNode091
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree08Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e092 : NestedArithmetic.Expr 3 := .plus e089 e091
noncomputable def p092 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,384],[0,384,-96]],[[0,0,0],[0,0,0],[0,0]],[[0,0,4608],[0,15552,-16],[4608,-16]],[[0,0,0],[0,0,0],[0,0]],[[12960,126576,26832],[126576,82368,-2352],[26832,-2352]],[[0,0,0],[0,0,0],[0,0]],[[1056672,1145664,62288],[1145664,164352,-3072],[62288,-3072]],[[0,0,0],[0,0,0],[0,0]],[[11801376,4544064,70560],[4544064,135680,-1296],[70560,-1296]],[[0,0,0],[0,0,0],[0,0]],[[63196608,10376288,35152],[10376288,-1472,-176],[35152,-176]],[[0,0,0],[0,0],[0]],[[206544736,15068896,-2048],[15068896,-88192],[-2048]],[[0,0,0],[0,0],[0]],[[456514528,14474560,-10896],[14474560,-69504],[-10896]],[[0,0,0],[0,0],[0]],[[720281792,9199648,-5152],[9199648,-25088],[-5152]],[[0,0,0],[0,0],[0]],[[836441408,3668688,-1040],[3668688,-4480],[-1040]],[[0,0,0],[0,0],[0]],[[726696672,722192,-80],[722192,-320],[-80]],[[0,0],[0]],[[474983968,-65968],[-65968]],[[0,0],[0]],[[232368864,-81376],[-81376]],[[0,0],[0]],[[83400512,-21872],[-21872]],[[0,0],[0]],[[20901152,-2784],[-2784]],[[0,0],[0]],[[3174560,-144],[-144]],[[0]],[[106112]],[[0]],[[-69184]],[[0]],[[-16128]],[[0]],[[-1600]],[[0]],[[-64]]]
theorem step092 : p092=NestedHorner.add p089 p091 := by decide +kernel
#print axioms step092
theorem h092 : NestedArithmetic.compile e092=p092 := StagedExprCompile.compile_plus e092 e089 e091 p089 p091 p092 rfl h089 h091 step092
#print axioms h092
end Gebendorfer.RadenkovicGutman.FixedDegree08Long00Compositional
