/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00225 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 1886751163872390715032834408448000000000000 987735764712497016781089875195416543232 2414270256325857447023476736000000000000))
theorem leaf00225_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 1886751163872390715032834408448000000000000 987735764712497016781089875195416543232 2414270256325857447023476736000000000000 raw00225=true := by decide +kernel
#print axioms leaf00225_raw
theorem leaf00225_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00225=true := by decide +kernel
#print axioms leaf00225_rectangular
def affine00225 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00225 (IntegerComputedClassCell.leftNumerator ![(151/32000),0,0] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(151/32000),0,0] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(151/32000),0,0] ![(3/32000),1,(1/16)]))
theorem leaf00225_transform : affine00225=(NestedInteger.clearedAll 3 raw00225 (IntegerComputedClassCell.leftNumerator ![(151/32000),0,0] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(151/32000),0,0] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(151/32000),0,0] ![(3/32000),1,(1/16)])) := by decide +kernel
#print axioms leaf00225_transform
theorem leaf00225_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00225=true := by decide +kernel
#print axioms leaf00225_sign
theorem leaf00225_log : RationalLog.accepts (1595647/4294967296) (-2120081789/536870912) 12 8=true := by decide +kernel
#print axioms leaf00225_log
def leaf00225 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (204561971081/500000000000) (1595647/4294967296) (-2120081789/536870912) 12 8 ![60,0,4] ![(151/32000),0,0] ![(3/32000),1,(1/16)] affine00225
theorem leaf00225_checked : FastNestedCellData.accepts 1 2 4 leaf00225=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (204561971081/500000000000) (1595647/4294967296) (-2120081789/536870912) 12 8 ![60,0,4] ![(151/32000),0,0] ![(3/32000),1,(1/16)] 1886751163872390715032834408448000000000000 987735764712497016781089875195416543232 2414270256325857447023476736000000000000 raw00225 affine00225
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00225_raw leaf00225_rectangular
    leaf00225_transform leaf00225_sign leaf00225_log
#print axioms leaf00225_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
