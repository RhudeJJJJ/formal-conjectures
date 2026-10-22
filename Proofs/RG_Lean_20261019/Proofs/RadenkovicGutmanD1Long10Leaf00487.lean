/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00487 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack true 153044293039560814613233664000000000000 153942772658507941966721465313744912384 1546253306166892749323772100608000000000000))
theorem leaf00487_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    true 153044293039560814613233664000000000000 153942772658507941966721465313744912384 1546253306166892749323772100608000000000000 raw00487=true := by decide +kernel
#print axioms leaf00487_raw
theorem leaf00487_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00487=true := by decide +kernel
#print axioms leaf00487_rectangular
def affine00487 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00487 (IntegerComputedClassCell.leftNumerator ![(7/128),0,0] ![(1/128),1,1]) (IntegerComputedClassCell.widthNumerator ![(7/128),0,0] ![(1/128),1,1]) (IntegerComputedClassCell.denominator ![(7/128),0,0] ![(1/128),1,1]))
theorem leaf00487_transform : affine00487=(NestedInteger.clearedAll 3 raw00487 (IntegerComputedClassCell.leftNumerator ![(7/128),0,0] ![(1/128),1,1]) (IntegerComputedClassCell.widthNumerator ![(7/128),0,0] ![(1/128),1,1]) (IntegerComputedClassCell.denominator ![(7/128),0,0] ![(1/128),1,1])) := by decide +kernel
#print axioms leaf00487_transform
theorem leaf00487_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00487=true := by decide +kernel
#print axioms leaf00487_sign
theorem leaf00487_log : RationalLog.accepts (2159875881/2147483648) (6178307/2147483648) 0 8=true := by decide +kernel
#print axioms leaf00487_log
def leaf00487 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack true (99558573/1000000000000) (2159875881/2147483648) (6178307/2147483648) 0 8 ![52,0,4] ![(7/128),0,0] ![(1/128),1,1] affine00487
theorem leaf00487_checked : FastNestedCellData.accepts 1 0 4 leaf00487=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack true (99558573/1000000000000) (2159875881/2147483648) (6178307/2147483648) 0 8 ![52,0,4] ![(7/128),0,0] ![(1/128),1,1] 153044293039560814613233664000000000000 153942772658507941966721465313744912384 1546253306166892749323772100608000000000000 raw00487 affine00487
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00487_raw leaf00487_rectangular
    leaf00487_transform leaf00487_sign leaf00487_log
#print axioms leaf00487_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
