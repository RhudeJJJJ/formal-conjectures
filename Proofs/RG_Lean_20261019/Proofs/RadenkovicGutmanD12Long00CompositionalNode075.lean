/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD12Long00CompositionalNode033
import Proofs.RadenkovicGutmanD12Long00CompositionalNode053
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree12Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e075 : NestedArithmetic.Expr 3 := .times e033 e053
noncomputable def p075 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,144]],[[0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,2592],[0,2592]],[[0,0,0],[0,0,0],[0,0]],[[-11664,0,11664],[0,46656,6912],[11664,6912]],[[0,0,0],[0,0,0],[0,0]],[[-202176,209952,62208],[209952,248832,6336],[62208,6336]],[[0,0,0],[0,0,0],[0,0]],[[-618192,1679616,139968],[1679616,559872,2304],[139968,2304]],[[0,0,0],[0,0,0],[0,0]],[[2937600,6018624,172800],[6018624,691200,288],[172800,288]],[[0,0,0],[0,0],[0]],[[27996912,12752640,127584],[12752640,510336],[127584]],[[0,0,0],[0,0],[0]],[[103349376,17768160,57600],[17768160,230400],[57600]],[[0,0,0],[0,0],[0]],[[236098656,17127936,15552],[17127936,62208],[15552]],[[0,0,0],[0,0],[0]],[[375985728,11703168,2304],[11703168,9216],[2304]],[[0,0,0],[0,0],[0]],[[439806528,5709312,144],[5709312,576],[144]],[[0,0],[0]],[[388243008,1974240],[1974240]],[[0,0],[0]],[[262245888,472320],[472320]],[[0,0],[0]],[[136241280,74304],[74304]],[[0,0],[0]],[[54327024,6912],[6912]],[[0,0],[0]],[[16471296,288],[288]],[[0]],[[3726432]],[[0]],[[608832]],[[0]],[[67824]],[[0]],[[4608]],[[0]],[[144]]]
theorem step075 : p075=NestedArithmetic.mul p033 p053 := by decide +kernel
#print axioms step075
theorem h075 : NestedArithmetic.compile e075=p075 := StagedExprCompile.compile_times e075 e033 e053 p033 p053 p075 rfl h033 h053 step075
#print axioms h075
end Gebendorfer.RadenkovicGutman.FixedDegree12Long00Compositional
