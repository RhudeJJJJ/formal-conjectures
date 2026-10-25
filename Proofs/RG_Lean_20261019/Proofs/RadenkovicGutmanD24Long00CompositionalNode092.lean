/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD24Long00CompositionalNode089
import Proofs.RadenkovicGutmanD24Long00CompositionalNode091
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree24Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e092 : NestedArithmetic.Expr 3 := .plus e089 e091
noncomputable def p092 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,3456],[0,3456,-1056]],[[0,0,0],[0,0,0],[0,0]],[[0,0,41472],[0,139968,-3888],[41472,-3888]],[[0,0,0],[0,0,0],[0,0]],[[132192,1136592,223344],[1136592,668736,-31632],[223344,-31632]],[[0,0,0],[0,0,0],[0,0]],[[9732960,9927360,459504],[9927360,1074816,-37632],[459504,-37632]],[[0,0,0],[0,0,0],[0,0]],[[105885792,37793088,398304],[37793088,274176,-15408],[398304,-15408]],[[0,0,0],[0,0,0],[0,0]],[[554567616,81942816,13296],[81942816,-1225536,-2064],[13296,-2064]],[[0,0,0],[0,0],[0]],[[1771623840,110626848,-249600],[110626848,-1718400],[-249600]],[[0,0,0],[0,0],[0]],[[3816352416,94433472,-205488],[94433472,-1055232],[-205488]],[[0,0,0],[0,0],[0]],[[5837599296,47332704,-76128],[47332704,-344832],[-76128]],[[0,0,0],[0,0],[0]],[[6515318592,8209776,-13872],[8209776,-58368],[-13872]],[[0,0,0],[0,0],[0]],[[5362768800,-5858640,-1008],[-5858640,-4032],[-1008]],[[0,0],[0]],[[3237988704,-4947216],[-4947216]],[[0,0],[0]],[[1391641248,-1791264],[-1791264]],[[0,0],[0]],[[387240768,-365904],[-365904]],[[0,0],[0]],[[43233504,-40992],[-40992]],[[0,0],[0]],[[-15352608,-1968],[-1968]],[[0]],[[-8982144]],[[0]],[[-2246208]],[[0]],[[-326016]],[[0]],[[-26688]],[[0]],[[-960]]]
theorem step092 : p092=NestedHorner.add p089 p091 := by decide +kernel
#print axioms step092
theorem h092 : NestedArithmetic.compile e092=p092 := StagedExprCompile.compile_plus e092 e089 e091 p089 p091 p092 rfl h089 h091 step092
#print axioms h092
end Gebendorfer.RadenkovicGutman.FixedDegree24Long00Compositional
