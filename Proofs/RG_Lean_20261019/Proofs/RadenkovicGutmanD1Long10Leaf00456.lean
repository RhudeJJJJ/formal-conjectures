/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00456 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack true 12206604018013016510615781376000000000000 12852060338260043880702500006791267483648 4855541056503190299610596769792000000000000))
theorem leaf00456_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    true 12206604018013016510615781376000000000000 12852060338260043880702500006791267483648 4855541056503190299610596769792000000000000 raw00456=true := by decide +kernel
#print axioms leaf00456_raw
theorem leaf00456_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00456=true := by decide +kernel
#print axioms leaf00456_rectangular
def affine00456 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00456 (IntegerComputedClassCell.leftNumerator ![(11/64),0,0] ![(1/64),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(11/64),0,0] ![(1/64),1,(1/2)]) (IntegerComputedClassCell.denominator ![(11/64),0,0] ![(1/64),1,(1/2)]))
theorem leaf00456_transform : affine00456=(NestedInteger.clearedAll 3 raw00456 (IntegerComputedClassCell.leftNumerator ![(11/64),0,0] ![(1/64),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(11/64),0,0] ![(1/64),1,(1/2)]) (IntegerComputedClassCell.denominator ![(11/64),0,0] ![(1/64),1,(1/2)])) := by decide +kernel
#print axioms leaf00456_transform
theorem leaf00456_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00456=true := by decide +kernel
#print axioms leaf00456_sign
theorem leaf00456_log : RationalLog.accepts (2255068591/2147483648) (52488397/2147483648) 0 8=true := by decide +kernel
#print axioms leaf00456_log
def leaf00456 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack true (2646885319/1000000000000) (2255068591/2147483648) (52488397/2147483648) 0 8 ![52,0,4] ![(11/64),0,0] ![(1/64),1,(1/2)] affine00456
theorem leaf00456_checked : FastNestedCellData.accepts 1 0 4 leaf00456=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack true (2646885319/1000000000000) (2255068591/2147483648) (52488397/2147483648) 0 8 ![52,0,4] ![(11/64),0,0] ![(1/64),1,(1/2)] 12206604018013016510615781376000000000000 12852060338260043880702500006791267483648 4855541056503190299610596769792000000000000 raw00456 affine00456
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00456_raw leaf00456_rectangular
    leaf00456_transform leaf00456_sign leaf00456_log
#print axioms leaf00456_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
