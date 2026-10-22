/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00097 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 90748462216640181398256222208000000000000 75792447741199964987007045477958028361728 962911555228503488221902012416000000000000))
theorem leaf00097_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 90748462216640181398256222208000000000000 75792447741199964987007045477958028361728 962911555228503488221902012416000000000000 raw00097=true := by decide +kernel
#print axioms leaf00097_raw
theorem leaf00097_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00097=true := by decide +kernel
#print axioms leaf00097_rectangular
def affine00097 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00097 (IntegerComputedClassCell.leftNumerator ![(33/3200),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(33/3200),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(33/3200),0,(1/4)] ![(1/3200),1,(1/4)]))
theorem leaf00097_transform : affine00097=(NestedInteger.clearedAll 3 raw00097 (IntegerComputedClassCell.leftNumerator ![(33/3200),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(33/3200),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(33/3200),0,(1/4)] ![(1/3200),1,(1/4)])) := by decide +kernel
#print axioms leaf00097_transform
theorem leaf00097_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00097=true := by decide +kernel
#print axioms leaf00097_sign
theorem leaf00097_log : RationalLog.accepts (3325378717/4294967296) (-137364001/1073741824) 1 8=true := by decide +kernel
#print axioms leaf00097_log
def leaf00097 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (19677935977/250000000000) (3325378717/4294967296) (-137364001/1073741824) 1 8 ![52,0,4] ![(33/3200),0,(1/4)] ![(1/3200),1,(1/4)] affine00097
theorem leaf00097_checked : FastNestedCellData.accepts 1 0 4 leaf00097=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (19677935977/250000000000) (3325378717/4294967296) (-137364001/1073741824) 1 8 ![52,0,4] ![(33/3200),0,(1/4)] ![(1/3200),1,(1/4)] 90748462216640181398256222208000000000000 75792447741199964987007045477958028361728 962911555228503488221902012416000000000000 raw00097 affine00097
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00097_raw leaf00097_rectangular
    leaf00097_transform leaf00097_sign leaf00097_log
#print axioms leaf00097_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
