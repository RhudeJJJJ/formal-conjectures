/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00447 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack true 5683909214664842853482496000000000000 6144701645894621837480386532858658816 1217176198528782869362376704000000000000))
theorem leaf00447_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    true 5683909214664842853482496000000000000 6144701645894621837480386532858658816 1217176198528782869362376704000000000000 raw00447=true := by decide +kernel
#print axioms leaf00447_raw
theorem leaf00447_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00447=true := by decide +kernel
#print axioms leaf00447_rectangular
def affine00447 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00447 (IntegerComputedClassCell.leftNumerator ![(7/32),0,0] ![(1/64),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(7/32),0,0] ![(1/64),1,(1/2)]) (IntegerComputedClassCell.denominator ![(7/32),0,0] ![(1/64),1,(1/2)]))
theorem leaf00447_transform : affine00447=(NestedInteger.clearedAll 3 raw00447 (IntegerComputedClassCell.leftNumerator ![(7/32),0,0] ![(1/64),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(7/32),0,0] ![(1/64),1,(1/2)]) (IntegerComputedClassCell.denominator ![(7/32),0,0] ![(1/64),1,(1/2)])) := by decide +kernel
#print axioms leaf00447_transform
theorem leaf00447_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00447=true := by decide +kernel
#print axioms leaf00447_sign
theorem leaf00447_log : RationalLog.accepts (4619836279/4294967296) (78292235/2147483648) 0 8=true := by decide +kernel
#print axioms leaf00447_log
def leaf00447 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack true (39440043/7812500000) (4619836279/4294967296) (78292235/2147483648) 0 8 ![52,0,4] ![(7/32),0,0] ![(1/64),1,(1/2)] affine00447
theorem leaf00447_checked : FastNestedCellData.accepts 1 0 4 leaf00447=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack true (39440043/7812500000) (4619836279/4294967296) (78292235/2147483648) 0 8 ![52,0,4] ![(7/32),0,0] ![(1/64),1,(1/2)] 5683909214664842853482496000000000000 6144701645894621837480386532858658816 1217176198528782869362376704000000000000 raw00447 affine00447
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00447_raw leaf00447_rectangular
    leaf00447_transform leaf00447_sign leaf00447_log
#print axioms leaf00447_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
