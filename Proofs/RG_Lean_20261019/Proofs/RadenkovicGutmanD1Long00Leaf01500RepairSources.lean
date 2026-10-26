/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01500RepairPrepared
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01500_w_source00 : NestedInteger.Poly 3 := leaf01500_w_inner
noncomputable def leaf01500_w_segment00 : NestedInteger.Poly 3 := leaf01500_w_source00.take 3
noncomputable def leaf01500_w_source01 : NestedInteger.Poly 3 := leaf01500_w_source00.drop 3
noncomputable def leaf01500_w_segment01 : NestedInteger.Poly 3 := leaf01500_w_source01.take 3
noncomputable def leaf01500_w_source02 : NestedInteger.Poly 3 := leaf01500_w_source01.drop 3
noncomputable def leaf01500_w_segment02 : NestedInteger.Poly 3 := leaf01500_w_source02.take 3
noncomputable def leaf01500_w_source03 : NestedInteger.Poly 3 := leaf01500_w_source02.drop 3
noncomputable def leaf01500_w_segment03 : NestedInteger.Poly 3 := leaf01500_w_source03.take 3
noncomputable def leaf01500_w_source04 : NestedInteger.Poly 3 := leaf01500_w_source03.drop 3
noncomputable def leaf01500_w_segment04 : NestedInteger.Poly 3 := leaf01500_w_source04.take 3
noncomputable def leaf01500_w_source05 : NestedInteger.Poly 3 := leaf01500_w_source04.drop 3
noncomputable def leaf01500_w_segment05 : NestedInteger.Poly 3 := leaf01500_w_source05.take 3
noncomputable def leaf01500_w_source06 : NestedInteger.Poly 3 := leaf01500_w_source05.drop 3
noncomputable def leaf01500_w_segment06 : NestedInteger.Poly 3 := leaf01500_w_source06.take 3
noncomputable def leaf01500_w_source07 : NestedInteger.Poly 3 := leaf01500_w_source06.drop 3
noncomputable def leaf01500_w_segment07 : NestedInteger.Poly 3 := leaf01500_w_source07.take 3
noncomputable def leaf01500_w_source08 : NestedInteger.Poly 3 := leaf01500_w_source07.drop 3
noncomputable def leaf01500_w_segment08 : NestedInteger.Poly 3 := leaf01500_w_source08.take 3
noncomputable def leaf01500_w_source09 : NestedInteger.Poly 3 := leaf01500_w_source08.drop 3
noncomputable def leaf01500_w_segment09 : NestedInteger.Poly 3 := leaf01500_w_source09.take 3
noncomputable def leaf01500_w_source10 : NestedInteger.Poly 3 := leaf01500_w_source09.drop 3
noncomputable def leaf01500_w_segment10 : NestedInteger.Poly 3 := leaf01500_w_source10.take 3
noncomputable def leaf01500_w_source11 : NestedInteger.Poly 3 := leaf01500_w_source10.drop 3
noncomputable def leaf01500_w_segment11 : NestedInteger.Poly 3 := leaf01500_w_source11.take 3
noncomputable def leaf01500_w_source12 : NestedInteger.Poly 3 := leaf01500_w_source11.drop 3
noncomputable def leaf01500_w_segment12 : NestedInteger.Poly 3 := leaf01500_w_source12.take 3
noncomputable def leaf01500_w_source13 : NestedInteger.Poly 3 := leaf01500_w_source12.drop 3
noncomputable def leaf01500_w_segment13 : NestedInteger.Poly 3 := leaf01500_w_source13.take 3
noncomputable def leaf01500_w_source14 : NestedInteger.Poly 3 := leaf01500_w_source13.drop 3
noncomputable def leaf01500_w_segment14 : NestedInteger.Poly 3 := leaf01500_w_source14.take 3
noncomputable def leaf01500_w_source15 : NestedInteger.Poly 3 := leaf01500_w_source14.drop 3
noncomputable def leaf01500_w_segment15 : NestedInteger.Poly 3 := leaf01500_w_source15.take 3
noncomputable def leaf01500_w_source16 : NestedInteger.Poly 3 := leaf01500_w_source15.drop 3
noncomputable def leaf01500_w_segment16 : NestedInteger.Poly 3 := leaf01500_w_source16.take 3
noncomputable def leaf01500_w_source17 : NestedInteger.Poly 3 := leaf01500_w_source16.drop 3
noncomputable def leaf01500_w_segment17 : NestedInteger.Poly 3 := leaf01500_w_source17.take 3
noncomputable def leaf01500_w_source18 : NestedInteger.Poly 3 := leaf01500_w_source17.drop 3
noncomputable def leaf01500_w_segment18 : NestedInteger.Poly 3 := leaf01500_w_source18.take 3
noncomputable def leaf01500_w_source19 : NestedInteger.Poly 3 := leaf01500_w_source18.drop 3
noncomputable def leaf01500_w_segment19 : NestedInteger.Poly 3 := leaf01500_w_source19.take 3
noncomputable def leaf01500_w_source20 : NestedInteger.Poly 3 := leaf01500_w_source19.drop 3
noncomputable def leaf01500_w_segment20 : NestedInteger.Poly 3 := leaf01500_w_source20.take 3
noncomputable def leaf01500_w_source21 : NestedInteger.Poly 3 := leaf01500_w_source20.drop 3
noncomputable def leaf01500_w_segment21 : NestedInteger.Poly 3 := leaf01500_w_source21.take 3
noncomputable def leaf01500_w_source22 : NestedInteger.Poly 3 := leaf01500_w_source21.drop 3
noncomputable def leaf01500_w_segment22 : NestedInteger.Poly 3 := leaf01500_w_source22.take 3
noncomputable def leaf01500_w_source23 : NestedInteger.Poly 3 := leaf01500_w_source22.drop 3
noncomputable def leaf01500_w_segment23 : NestedInteger.Poly 3 := leaf01500_w_source23.take 3
noncomputable def leaf01500_w_source24 : NestedInteger.Poly 3 := leaf01500_w_source23.drop 3
noncomputable def leaf01500_w_segment24 : NestedInteger.Poly 3 := leaf01500_w_source24.take 3
noncomputable def leaf01500_w_source25 : NestedInteger.Poly 3 := leaf01500_w_source24.drop 3
noncomputable def leaf01500_w_segment25 : NestedInteger.Poly 3 := leaf01500_w_source25.take 3
noncomputable def leaf01500_w_source26 : NestedInteger.Poly 3 := leaf01500_w_source25.drop 3
noncomputable def leaf01500_w_segment26 : NestedInteger.Poly 3 := leaf01500_w_source26.take 3
noncomputable def leaf01500_w_source27 : NestedInteger.Poly 3 := leaf01500_w_source26.drop 3
noncomputable def leaf01500_w_segment27 : NestedInteger.Poly 3 := leaf01500_w_source27.take 3
noncomputable def leaf01500_w_source28 : NestedInteger.Poly 3 := leaf01500_w_source27.drop 3
noncomputable def leaf01500_w_segment28 : NestedInteger.Poly 3 := leaf01500_w_source28.take 3
noncomputable def leaf01500_w_source29 : NestedInteger.Poly 3 := leaf01500_w_source28.drop 3
noncomputable def leaf01500_w_segment29 : NestedInteger.Poly 3 := leaf01500_w_source29.take 3
#print axioms leaf01500_inner
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
