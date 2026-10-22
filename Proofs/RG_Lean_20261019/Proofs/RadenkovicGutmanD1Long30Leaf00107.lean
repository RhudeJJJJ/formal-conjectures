/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00107 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 180340801274878594643314868224000000000000 164562833298970133457598642461030949584896 4208210854741132357241579503616000000000000))
theorem leaf00107_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 180340801274878594643314868224000000000000 164562833298970133457598642461030949584896 4208210854741132357241579503616000000000000 raw00107=true := by decide +kernel
#print axioms leaf00107_raw
theorem leaf00107_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00107=true := by decide +kernel
#print axioms leaf00107_rectangular
def affine00107 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00107 (IntegerComputedClassCell.leftNumerator ![(79/32000),0,(1/8)] ![(3/32000),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(79/32000),0,(1/8)] ![(3/32000),1,(1/8)]) (IntegerComputedClassCell.denominator ![(79/32000),0,(1/8)] ![(3/32000),1,(1/8)]))
theorem leaf00107_transform : affine00107=(NestedInteger.clearedAll 3 raw00107 (IntegerComputedClassCell.leftNumerator ![(79/32000),0,(1/8)] ![(3/32000),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(79/32000),0,(1/8)] ![(3/32000),1,(1/8)]) (IntegerComputedClassCell.denominator ![(79/32000),0,(1/8)] ![(3/32000),1,(1/8)])) := by decide +kernel
#print axioms leaf00107_transform
theorem leaf00107_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00107=true := by decide +kernel
#print axioms leaf00107_sign
theorem leaf00107_log : RationalLog.accepts (3771708439/4294967296) (-139496127/2147483648) 1 8=true := by decide +kernel
#print axioms leaf00107_log
def leaf00107 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (19552588853/500000000000) (3771708439/4294967296) (-139496127/2147483648) 1 8 ![60,0,4] ![(79/32000),0,(1/8)] ![(3/32000),1,(1/8)] affine00107
theorem leaf00107_checked : FastNestedCellData.accepts 1 2 4 leaf00107=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (19552588853/500000000000) (3771708439/4294967296) (-139496127/2147483648) 1 8 ![60,0,4] ![(79/32000),0,(1/8)] ![(3/32000),1,(1/8)] 180340801274878594643314868224000000000000 164562833298970133457598642461030949584896 4208210854741132357241579503616000000000000 raw00107 affine00107
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00107_raw leaf00107_rectangular
    leaf00107_transform leaf00107_sign leaf00107_log
#print axioms leaf00107_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
