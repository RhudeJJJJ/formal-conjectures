/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00812 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 573124968822000558025570516992000000000000 225846734894336836776743125388594125996032 454322480383491480780428804096000000000000))
theorem leaf00812_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 573124968822000558025570516992000000000000 225846734894336836776743125388594125996032 454322480383491480780428804096000000000000 raw00812=true := by decide +kernel
#print axioms leaf00812_raw
theorem leaf00812_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00812=true := by decide +kernel
#print axioms leaf00812_rectangular
def affine00812 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00812 (IntegerComputedClassCell.leftNumerator ![(71/1600),0,(1/8)] ![(3/3200),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(71/1600),0,(1/8)] ![(3/3200),1,(1/8)]) (IntegerComputedClassCell.denominator ![(71/1600),0,(1/8)] ![(3/3200),1,(1/8)]))
theorem leaf00812_transform : affine00812=(NestedInteger.clearedAll 3 raw00812 (IntegerComputedClassCell.leftNumerator ![(71/1600),0,(1/8)] ![(3/3200),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(71/1600),0,(1/8)] ![(3/3200),1,(1/8)]) (IntegerComputedClassCell.denominator ![(71/1600),0,(1/8)] ![(3/3200),1,(1/8)])) := by decide +kernel
#print axioms leaf00812_transform
theorem leaf00812_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00812=true := by decide +kernel
#print axioms leaf00812_sign
theorem leaf00812_log : RationalLog.accepts (565251349/2147483648) (-2866421605/4294967296) 2 8=true := by decide +kernel
#print axioms leaf00812_log
def leaf00812 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (248553334521/500000000000) (565251349/2147483648) (-2866421605/4294967296) 2 8 ![60,0,4] ![(71/1600),0,(1/8)] ![(3/3200),1,(1/8)] affine00812
theorem leaf00812_checked : FastNestedCellData.accepts 1 2 4 leaf00812=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (248553334521/500000000000) (565251349/2147483648) (-2866421605/4294967296) 2 8 ![60,0,4] ![(71/1600),0,(1/8)] ![(3/3200),1,(1/8)] 573124968822000558025570516992000000000000 225846734894336836776743125388594125996032 454322480383491480780428804096000000000000 raw00812 affine00812
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00812_raw leaf00812_rectangular
    leaf00812_transform leaf00812_sign leaf00812_log
#print axioms leaf00812_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
