/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD38Long00CompositionalNode033
import Proofs.RadenkovicGutmanD38Long00CompositionalNode064
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree38Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e093 : NestedArithmetic.Expr 3 := .times e033 e064
noncomputable def p093 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,1444]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,34656],[0,34656,76]],[[0,0,0],[0,0,0],[0,0]],[[-116964,-77976,194940],[-77976,753768,108224],[194940,108224]],[[0,0,0],[0,0,0],[0,0]],[[-3203172,2963088,1175796],[2963088,4477920,113392],[1175796,113392]],[[0,0,0],[0,0,0],[0,0]],[[-13713516,29013912,2943936],[29013912,11010424,46664],[2943936,46664]],[[0,0,0],[0,0,0],[0,0]],[[33186084,115820200,3992888],[115820200,14648848,6992],[3992888,6992]],[[0,0,0],[0,0,0],[0,0]],[[473087156,266198208,3207352],[266198208,11547136,152],[3207352,152]],[[0,0,0],[0,0],[0]],[[1958056476,397205488,1566208],[397205488,5542832],[1566208]],[[0,0,0],[0,0],[0]],[[4822509320,407014808,457824],[407014808,1597368],[457824]],[[0,0,0],[0,0],[0]],[[8155690872,294273064,74632],[294273064,258096],[74632]],[[0,0,0],[0,0],[0]],[[10050505240,151532600,5548],[151532600,19304],[5548]],[[0,0,0],[0,0],[0]],[[9301497120,55300488,76],[55300488,304],[76]],[[0,0],[0]],[[6566650192,14009080],[14009080]],[[0,0],[0]],[[3559220448,2357520],[2357520]],[[0,0],[0]],[[1479864324,241376],[241376]],[[0,0],[0]],[[468240636,12312],[12312]],[[0,0],[0]],[[110885064,152],[152]],[[0]],[[19092568]],[[0]],[[2275060]],[[0]],[[171532]],[[0]],[[6764]],[[0]],[[76]]]
theorem step093 : p093=NestedArithmetic.mul p033 p064 := by decide +kernel
#print axioms step093
theorem h093 : NestedArithmetic.compile e093=p093 := StagedExprCompile.compile_times e093 e033 e064 p033 p064 p093 rfl h033 h064 step093
#print axioms h093
end Gebendorfer.RadenkovicGutman.FixedDegree38Long00Compositional
