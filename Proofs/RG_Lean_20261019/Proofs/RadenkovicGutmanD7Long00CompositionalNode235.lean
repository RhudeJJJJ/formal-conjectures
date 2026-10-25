/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD7Long00CompositionalNode213
import Proofs.RadenkovicGutmanD7Long00CompositionalNode219
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree07Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e235 : NestedArithmetic.Expr 3 := .times e213 e219
noncomputable def p235 : NestedHorner.Poly 3 := [[[49],[0],[0]],[[0,0],[0,0],[0]],[[1519,0,0],[0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[21609,0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[186984,0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[1099854,0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[4655637,98,0],[98,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[14645365,2254,0],[2254,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[34860168,23128,0],[23128,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[63319956,139650,0],[139650,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[87822700,551250,0],[551250,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[92329475,1494843,49],[1494843,147,0],[49,0]],[[0,0,0],[0,0,0],[0,0]],[[72291660,2848321,735],[2848321,2254,0],[735,0]],[[0,0,0],[0,0,0],[0,0]],[[40727330,3832486,4606],[3832486,14455,0],[4606,0]],[[0,0,0],[0,0,0],[0,0]],[[15387421,3602039,15631],[3602039,50274,0],[15631,0]],[[0,0,0],[0,0,0],[0,0]],[[3237087,2292906,31164],[2292906,102900,0],[31164,0]],[[0,0,0],[0,0,0],[0,0]],[[68796,926051,37093],[926051,125930,49],[37093,49]],[[0,0,0],[0,0,0],[0,0]],[[-125685,204624,25578],[204624,89327,343],[25578,343]],[[0,0,0],[0,0,0],[0,0]],[[-19845,14553,9261],[14553,33222,784],[9261,784]],[[0,0,0],[0,0,0],[0,0]],[[0,-1323,1323],[-1323,4851,637],[1323,637]],[[0,0],[0,0,0],[0,0]],[[0,0],[0,0,147],[0,147]]]
theorem step235 : p235=NestedArithmetic.mul p213 p219 := by decide +kernel
#print axioms step235
theorem h235 : NestedArithmetic.compile e235=p235 := StagedExprCompile.compile_times e235 e213 e219 p213 p219 p235 rfl h213 h219 step235
#print axioms h235
end Gebendorfer.RadenkovicGutman.FixedDegree07Long00Compositional
