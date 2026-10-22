/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00391 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 110973195272866527368521449472000000000000 58925484182682137151153033545354248716288 204062664912126572497750458368000000000000))
theorem leaf00391_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 110973195272866527368521449472000000000000 58925484182682137151153033545354248716288 204062664912126572497750458368000000000000 raw00391=true := by decide +kernel
#print axioms leaf00391_raw
theorem leaf00391_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00391=true := by decide +kernel
#print axioms leaf00391_rectangular
def affine00391 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00391 (IntegerComputedClassCell.leftNumerator ![(31/3200),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(31/3200),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(31/3200),0,(1/16)] ![(1/6400),1,(1/16)]))
theorem leaf00391_transform : affine00391=(NestedInteger.clearedAll 3 raw00391 (IntegerComputedClassCell.leftNumerator ![(31/3200),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(31/3200),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(31/3200),0,(1/16)] ![(1/6400),1,(1/16)])) := by decide +kernel
#print axioms leaf00391_transform
theorem leaf00391_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00391=true := by decide +kernel
#print axioms leaf00391_sign
theorem leaf00391_log : RationalLog.accepts (884794287/2147483648) (-952083545/2147483648) 2 8=true := by decide +kernel
#print axioms leaf00391_log
def leaf00391 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (144380855283/500000000000) (884794287/2147483648) (-952083545/2147483648) 2 8 ![60,0,4] ![(31/3200),0,(1/16)] ![(1/6400),1,(1/16)] affine00391
theorem leaf00391_checked : FastNestedCellData.accepts 1 2 4 leaf00391=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (144380855283/500000000000) (884794287/2147483648) (-952083545/2147483648) 2 8 ![60,0,4] ![(31/3200),0,(1/16)] ![(1/6400),1,(1/16)] 110973195272866527368521449472000000000000 58925484182682137151153033545354248716288 204062664912126572497750458368000000000000 raw00391 affine00391
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00391_raw leaf00391_rectangular
    leaf00391_transform leaf00391_sign leaf00391_log
#print axioms leaf00391_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
