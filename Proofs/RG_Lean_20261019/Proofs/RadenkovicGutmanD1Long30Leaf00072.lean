/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00072 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 546961818219312340597068529664000000000000 510310424332020097087394935681412763746304 17210645208189635300130633547776000000000000))
theorem leaf00072_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 546961818219312340597068529664000000000000 510310424332020097087394935681412763746304 17210645208189635300130633547776000000000000 raw00072=true := by decide +kernel
#print axioms leaf00072_raw
theorem leaf00072_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00072=true := by decide +kernel
#print axioms leaf00072_rectangular
def affine00072 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00072 (IntegerComputedClassCell.leftNumerator ![(3/1600),0,(1/8)] ![(1/16000),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(3/1600),0,(1/8)] ![(1/16000),1,(1/8)]) (IntegerComputedClassCell.denominator ![(3/1600),0,(1/8)] ![(1/16000),1,(1/8)]))
theorem leaf00072_transform : affine00072=(NestedInteger.clearedAll 3 raw00072 (IntegerComputedClassCell.leftNumerator ![(3/1600),0,(1/8)] ![(1/16000),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(3/1600),0,(1/8)] ![(1/16000),1,(1/8)]) (IntegerComputedClassCell.denominator ![(3/1600),0,(1/8)] ![(1/16000),1,(1/8)])) := by decide +kernel
#print axioms leaf00072_transform
theorem leaf00072_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00072=true := by decide +kernel
#print axioms leaf00072_sign
theorem leaf00072_log : RationalLog.accepts (3891771239/4294967296) (-52924505/1073741824) 1 8=true := by decide +kernel
#print axioms leaf00072_log
def leaf00072 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (29650859579/1000000000000) (3891771239/4294967296) (-52924505/1073741824) 1 8 ![60,0,4] ![(3/1600),0,(1/8)] ![(1/16000),1,(1/8)] affine00072
theorem leaf00072_checked : FastNestedCellData.accepts 1 2 4 leaf00072=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (29650859579/1000000000000) (3891771239/4294967296) (-52924505/1073741824) 1 8 ![60,0,4] ![(3/1600),0,(1/8)] ![(1/16000),1,(1/8)] 546961818219312340597068529664000000000000 510310424332020097087394935681412763746304 17210645208189635300130633547776000000000000 raw00072 affine00072
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00072_raw leaf00072_rectangular
    leaf00072_transform leaf00072_sign leaf00072_log
#print axioms leaf00072_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
