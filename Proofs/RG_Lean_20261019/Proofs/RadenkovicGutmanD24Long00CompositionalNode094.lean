/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD24Long00CompositionalNode035
import Proofs.RadenkovicGutmanD24Long00CompositionalNode061
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree24Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e094 : NestedArithmetic.Expr 3 := .times e035 e061
noncomputable def p094 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0,0]],[[0,0,-5184],[0,-10368,3168],[-5184,3168]],[[0,0,0],[0,0,0],[0,0]],[[0,-142560,-16416],[-142560,24192,13728],[-16416,13728]],[[0,0,0],[0,0,0],[0,0]],[[-886464,-772416,46944],[-772416,493056,16896],[46944,16896]],[[0,0,0],[0,0,0],[0,0]],[[-6469632,364608,287424],[364608,1677312,7392],[287424,7392]],[[0,0,0],[0,0,0],[0,0]],[[-3473280,12869184,543648],[12869184,2686080,1056],[543648,1056]],[[0,0,0],[0,0],[0]],[[127343232,45422208,527616],[45422208,2398464],[527616]],[[0,0,0],[0,0],[0]],[[680559552,84689856,290208],[84689856,1254144],[290208]],[[0,0,0],[0,0],[0]],[[1888482048,99937344,91200],[99937344,380928],[91200]],[[0,0,0],[0,0],[0]],[[3432247680,79554528,15264],[79554528,62208],[15264]],[[0,0,0],[0,0],[0]],[[4429594176,43790688,1056],[43790688,4224],[1056]],[[0,0],[0]],[[4220774976,16706208],[16706208]],[[0,0],[0]],[[3030325056,4337280],[4337280]],[[0,0],[0]],[[1654453632,731232],[731232]],[[0,0],[0]],[[687393024,72192],[72192]],[[0,0],[0]],[[215723328,3168],[3168]],[[0]],[[50258304]],[[0]],[[8421504]],[[0]],[[959040]],[[0]],[[66432]],[[0]],[[2112]]]
theorem step094 : p094=NestedArithmetic.mul p035 p061 := by decide +kernel
#print axioms step094
theorem h094 : NestedArithmetic.compile e094=p094 := StagedExprCompile.compile_times e094 e035 e061 p035 p061 p094 rfl h035 h061 step094
#print axioms h094
end Gebendorfer.RadenkovicGutman.FixedDegree24Long00Compositional
