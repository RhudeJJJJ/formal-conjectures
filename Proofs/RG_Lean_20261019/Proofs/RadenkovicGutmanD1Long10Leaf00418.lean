/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00418 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack true 190709237001426907148484345856000000000000 242316706138852575667534525125944017944576 5859645727194447579560106000384000000000000))
theorem leaf00418_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    true 190709237001426907148484345856000000000000 242316706138852575667534525125944017944576 5859645727194447579560106000384000000000000 raw00418=true := by decide +kernel
#print axioms leaf00418_raw
theorem leaf00418_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00418=true := by decide +kernel
#print axioms leaf00418_rectangular
def affine00418 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00418 (IntegerComputedClassCell.leftNumerator ![(1/2),0,(1/2)] ![(1/16),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(1/2),0,(1/2)] ![(1/16),1,(1/4)]) (IntegerComputedClassCell.denominator ![(1/2),0,(1/2)] ![(1/16),1,(1/4)]))
theorem leaf00418_transform : affine00418=(NestedInteger.clearedAll 3 raw00418 (IntegerComputedClassCell.leftNumerator ![(1/2),0,(1/2)] ![(1/16),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(1/2),0,(1/2)] ![(1/16),1,(1/4)]) (IntegerComputedClassCell.denominator ![(1/2),0,(1/2)] ![(1/16),1,(1/4)])) := by decide +kernel
#print axioms leaf00418_transform
theorem leaf00418_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00418=true := by decide +kernel
#print axioms leaf00418_sign
theorem leaf00418_log : RationalLog.accepts (5240507169/4294967296) (213647071/2147483648) 0 8=true := by decide +kernel
#print axioms leaf00418_log
def leaf00418 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack true (20676736907/500000000000) (5240507169/4294967296) (213647071/2147483648) 0 8 ![52,0,4] ![(1/2),0,(1/2)] ![(1/16),1,(1/4)] affine00418
theorem leaf00418_checked : FastNestedCellData.accepts 1 0 4 leaf00418=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack true (20676736907/500000000000) (5240507169/4294967296) (213647071/2147483648) 0 8 ![52,0,4] ![(1/2),0,(1/2)] ![(1/16),1,(1/4)] 190709237001426907148484345856000000000000 242316706138852575667534525125944017944576 5859645727194447579560106000384000000000000 raw00418 affine00418
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00418_raw leaf00418_rectangular
    leaf00418_transform leaf00418_sign leaf00418_log
#print axioms leaf00418_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
