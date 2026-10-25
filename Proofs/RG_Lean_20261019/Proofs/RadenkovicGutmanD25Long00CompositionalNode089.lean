/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD25Long00CompositionalNode033
import Proofs.RadenkovicGutmanD25Long00CompositionalNode061
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree25Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e089 : NestedArithmetic.Expr 3 := .times e033 e061
noncomputable def p089 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,1875],[0,1875,-1150]],[[0,0,0],[0,0,0],[0,0]],[[0,-16875,16875],[-16875,61875,-12575],[16875,-12575]],[[0,0,0],[0,0,0],[0,0]],[[-159975,185625,24975],[185625,51150,-45200],[24975,-45200]],[[0,0,0],[0,0,0],[0,0]],[[11475,933300,-170550],[933300,-847825,-46225],[-170550,-46225]],[[0,0,0],[0,0,0],[0,0]],[[5814450,-1601725,-644675],[-1601725,-2864950,-17775],[-644675,-17775]],[[0,0,0],[0,0,0],[0,0]],[[17829375,-18819150,-982500],[-18819150,-4207500,-2300],[-982500,-2300]],[[0,0,0],[0,0],[0]],[[-27318325,-55899625,-819525],[-55899625,-3434350],[-819525]],[[0,0,0],[0,0],[0]],[[-305878350,-93014750,-401250],[-93014750,-1655625],[-401250]],[[0,0,0],[0,0],[0]],[[-963422600,-100454975,-114825],[-100454975,-468050],[-114825]],[[0,0,0],[0,0],[0]],[[-1824991925,-74395925,-17775],[-74395925,-71725],[-17775]],[[0,0,0],[0,0],[0]],[[-2392156300,-38563950,-1150],[-38563950,-4600],[-1150]],[[0,0],[0]],[[-2292899300,-13985250],[-13985250]],[[0,0],[0]],[[-1649679800,-3477000],[-3477000]],[[0,0],[0]],[[-901234875,-564650],[-564650]],[[0,0],[0]],[[-374478525,-53950],[-53950]],[[0,0],[0]],[[-117512850,-2300],[-2300]],[[0]],[[-27374700]],[[0]],[[-4586575]],[[0]],[[-522275]],[[0]],[[-36175]],[[0]],[[-1150]]]
theorem step089 : p089=NestedArithmetic.mul p033 p061 := by decide +kernel
#print axioms step089
theorem h089 : NestedArithmetic.compile e089=p089 := StagedExprCompile.compile_times e089 e033 e061 p033 p061 p089 rfl h033 h061 step089
#print axioms h089
end Gebendorfer.RadenkovicGutman.FixedDegree25Long00Compositional
