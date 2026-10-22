/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00986 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 3002884160918362765522467028992000000000000 1484365706881496389231711785169833965912064 2279617930571443356082286624768000000000000))
theorem leaf00986_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 3002884160918362765522467028992000000000000 1484365706881496389231711785169833965912064 2279617930571443356082286624768000000000000 raw00986=true := by decide +kernel
#print axioms leaf00986_raw
theorem leaf00986_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00986=true := by decide +kernel
#print axioms leaf00986_rectangular
def affine00986 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00986 (IntegerComputedClassCell.leftNumerator ![(21/160),0,(1/16)] ![(1/160),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(21/160),0,(1/16)] ![(1/160),1,(1/16)]) (IntegerComputedClassCell.denominator ![(21/160),0,(1/16)] ![(1/160),1,(1/16)]))
theorem leaf00986_transform : affine00986=(NestedInteger.clearedAll 3 raw00986 (IntegerComputedClassCell.leftNumerator ![(21/160),0,(1/16)] ![(1/160),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(21/160),0,(1/16)] ![(1/160),1,(1/16)]) (IntegerComputedClassCell.denominator ![(21/160),0,(1/16)] ![(1/160),1,(1/16)])) := by decide +kernel
#print axioms leaf00986_transform
theorem leaf00986_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00986=true := by decide +kernel
#print axioms leaf00986_sign
theorem leaf00986_log : RationalLog.accepts (1285809209/4294967296) (-323748117/536870912) 2 8=true := by decide +kernel
#print axioms leaf00986_log
def leaf00986 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (325573353099/500000000000) (1285809209/4294967296) (-323748117/536870912) 2 8 ![60,0,4] ![(21/160),0,(1/16)] ![(1/160),1,(1/16)] affine00986
theorem leaf00986_checked : FastNestedCellData.accepts 1 2 4 leaf00986=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (325573353099/500000000000) (1285809209/4294967296) (-323748117/536870912) 2 8 ![60,0,4] ![(21/160),0,(1/16)] ![(1/160),1,(1/16)] 3002884160918362765522467028992000000000000 1484365706881496389231711785169833965912064 2279617930571443356082286624768000000000000 raw00986 affine00986
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00986_raw leaf00986_rectangular
    leaf00986_transform leaf00986_sign leaf00986_log
#print axioms leaf00986_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
