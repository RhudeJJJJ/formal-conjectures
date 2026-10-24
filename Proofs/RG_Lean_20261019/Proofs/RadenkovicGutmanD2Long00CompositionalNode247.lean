/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD2Long00CompositionalNode246
import Proofs.RadenkovicGutmanD2Long00CompositionalNode120
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e247 : NestedArithmetic.Expr 3 := .times e246 e120
noncomputable def p247 : NestedHorner.Poly 3 := [[[8],[0],[0]],[[0,0],[0,0],[0]],[[280,0,0],[0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[4520,0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[44648,0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[301904,0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[1481240,12,0],[12,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[5453672,316,0],[316,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[15372112,3732,0],[3732,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[33542280,26116,0],[26116,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[56919616,120524,0],[120524,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[75046256,386336,4],[386336,16,0],[4,0]],[[0,0,0],[0,0,0],[0,0]],[[76385928,882528,72],[882528,272,0],[72,0]],[[0,0,0],[0,0,0],[0,0]],[[59270528,1450716,548],[1450716,1968,0],[548,0]],[[0,0,0],[0,0,0],[0,0]],[[34341176,1711728,2300],[1711728,7904,0],[2300,0]],[[0,0,0],[0,0,0],[0,0]],[[14380392,1428800,5820],[1428800,19280,0],[5820,0]],[[0,0,0],[0,0,0],[0,0]],[[4129344,818960,9124],[818960,29392,4],[9124,4]],[[0,0,0],[0,0,0],[0,0]],[[742176,305392,8780],[305392,27792,32],[8780,32]],[[0,0,0],[0,0,0],[0,0]],[[69336,66888,4964],[66888,15616,92],[4964,92]],[[0,0,0],[0,0,0],[0,0]],[[1944,6804,1488],[6804,4704,116],[1488,116]],[[0,0,0],[0,0,0],[0,0]],[[0,108,180],[108,576,64],[180,64]],[[0,0],[0,0,0],[0,0]],[[0,0],[0,0,12],[0,12]]]
theorem step247 : p247=NestedArithmetic.mul p246 p120 := by decide +kernel
#print axioms step247
theorem h247 : NestedArithmetic.compile e247=p247 := StagedExprCompile.compile_times e247 e246 e120 p246 p120 p247 rfl h246 h120 step247
#print axioms h247
end Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
