/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00205 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 11123429685491836080110331494400000000000 6820240585580530039013153857676664373248 28276178337205020639464574156800000000000))
theorem leaf00205_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 11123429685491836080110331494400000000000 6820240585580530039013153857676664373248 28276178337205020639464574156800000000000 raw00205=true := by decide +kernel
#print axioms leaf00205_raw
theorem leaf00205_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00205=true := by decide +kernel
#print axioms leaf00205_rectangular
def affine00205 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00205 (IntegerComputedClassCell.leftNumerator ![(109/3200),0,(1/4)] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(109/3200),0,(1/4)] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(109/3200),0,(1/4)] ![(3/3200),1,(1/4)]))
theorem leaf00205_transform : affine00205=(NestedInteger.clearedAll 3 raw00205 (IntegerComputedClassCell.leftNumerator ![(109/3200),0,(1/4)] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(109/3200),0,(1/4)] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(109/3200),0,(1/4)] ![(3/3200),1,(1/4)])) := by decide +kernel
#print axioms leaf00205_transform
theorem leaf00205_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00205=true := by decide +kernel
#print axioms leaf00205_sign
theorem leaf00205_log : RationalLog.accepts (1060837231/2147483648) (-47327745/134217728) 2 8=true := by decide +kernel
#print axioms leaf00205_log
def leaf00205 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (24120093261/100000000000) (1060837231/2147483648) (-47327745/134217728) 2 8 ![52,0,4] ![(109/3200),0,(1/4)] ![(3/3200),1,(1/4)] affine00205
theorem leaf00205_checked : FastNestedCellData.accepts 1 0 4 leaf00205=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (24120093261/100000000000) (1060837231/2147483648) (-47327745/134217728) 2 8 ![52,0,4] ![(109/3200),0,(1/4)] ![(3/3200),1,(1/4)] 11123429685491836080110331494400000000000 6820240585580530039013153857676664373248 28276178337205020639464574156800000000000 raw00205 affine00205
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00205_raw leaf00205_rectangular
    leaf00205_transform leaf00205_sign leaf00205_log
#print axioms leaf00205_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
