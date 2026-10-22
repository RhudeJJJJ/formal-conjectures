/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00917 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 2717678927630440893847242276864000000000000 1077749446860188511041505576981598241292288 1828855500523221718265094995968000000000000))
theorem leaf00917_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 2717678927630440893847242276864000000000000 1077749446860188511041505576981598241292288 1828855500523221718265094995968000000000000 raw00917=true := by decide +kernel
#print axioms leaf00917_raw
theorem leaf00917_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00917=true := by decide +kernel
#print axioms leaf00917_rectangular
def affine00917 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00917 (IntegerComputedClassCell.leftNumerator ![(3/40),0,(1/8)] ![(1/320),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(3/40),0,(1/8)] ![(1/320),1,(1/8)]) (IntegerComputedClassCell.denominator ![(3/40),0,(1/8)] ![(1/320),1,(1/8)]))
theorem leaf00917_transform : affine00917=(NestedInteger.clearedAll 3 raw00917 (IntegerComputedClassCell.leftNumerator ![(3/40),0,(1/8)] ![(1/320),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(3/40),0,(1/8)] ![(1/320),1,(1/8)]) (IntegerComputedClassCell.denominator ![(3/40),0,(1/8)] ![(1/320),1,(1/8)])) := by decide +kernel
#print axioms leaf00917_transform
theorem leaf00917_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00917=true := by decide +kernel
#print axioms leaf00917_sign
theorem leaf00917_log : RationalLog.accepts (535849601/2147483648) (-2981133715/4294967296) 3 8=true := by decide +kernel
#print axioms leaf00917_log
def leaf00917 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (589302679491/1000000000000) (535849601/2147483648) (-2981133715/4294967296) 3 8 ![60,0,4] ![(3/40),0,(1/8)] ![(1/320),1,(1/8)] affine00917
theorem leaf00917_checked : FastNestedCellData.accepts 1 2 4 leaf00917=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (589302679491/1000000000000) (535849601/2147483648) (-2981133715/4294967296) 3 8 ![60,0,4] ![(3/40),0,(1/8)] ![(1/320),1,(1/8)] 2717678927630440893847242276864000000000000 1077749446860188511041505576981598241292288 1828855500523221718265094995968000000000000 raw00917 affine00917
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00917_raw leaf00917_rectangular
    leaf00917_transform leaf00917_sign leaf00917_log
#print axioms leaf00917_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
