/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00327 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 22739691678979387676317188096000000000 6500441383316327542358834626940633088 9374658803216649361819697152000000000))
theorem leaf00327_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 22739691678979387676317188096000000000 6500441383316327542358834626940633088 9374658803216649361819697152000000000 raw00327=true := by decide +kernel
#print axioms leaf00327_raw
theorem leaf00327_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00327=true := by decide +kernel
#print axioms leaf00327_rectangular
def affine00327 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00327 (IntegerComputedClassCell.leftNumerator ![(9/80),0,0] ![(1/160),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(9/80),0,0] ![(1/160),1,(1/4)]) (IntegerComputedClassCell.denominator ![(9/80),0,0] ![(1/160),1,(1/4)]))
theorem leaf00327_transform : affine00327=(NestedInteger.clearedAll 3 raw00327 (IntegerComputedClassCell.leftNumerator ![(9/80),0,0] ![(1/160),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(9/80),0,0] ![(1/160),1,(1/4)]) (IntegerComputedClassCell.denominator ![(9/80),0,0] ![(1/160),1,(1/4)])) := by decide +kernel
#print axioms leaf00327_transform
theorem leaf00327_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00327=true := by decide +kernel
#print axioms leaf00327_sign
theorem leaf00327_log : RationalLog.accepts (725031927/4294967296) (-119385567/134217728) 3 8=true := by decide +kernel
#print axioms leaf00327_log
def leaf00327 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (2773622601/4000000000) (725031927/4294967296) (-119385567/134217728) 3 8 ![52,0,4] ![(9/80),0,0] ![(1/160),1,(1/4)] affine00327
theorem leaf00327_checked : FastNestedCellData.accepts 1 0 4 leaf00327=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (2773622601/4000000000) (725031927/4294967296) (-119385567/134217728) 3 8 ![52,0,4] ![(9/80),0,0] ![(1/160),1,(1/4)] 22739691678979387676317188096000000000 6500441383316327542358834626940633088 9374658803216649361819697152000000000 raw00327 affine00327
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00327_raw leaf00327_rectangular
    leaf00327_transform leaf00327_sign leaf00327_log
#print axioms leaf00327_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
