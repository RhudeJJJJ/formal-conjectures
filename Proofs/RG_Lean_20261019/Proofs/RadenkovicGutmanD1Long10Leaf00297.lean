/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00297 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 652431224424112062798175299174400000000000 97977614296375845362149904177294682882048 138510229754346810674339905536000000000000))
theorem leaf00297_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 652431224424112062798175299174400000000000 97977614296375845362149904177294682882048 138510229754346810674339905536000000000000 raw00297=true := by decide +kernel
#print axioms leaf00297_raw
theorem leaf00297_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00297=true := by decide +kernel
#print axioms leaf00297_rectangular
def affine00297 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00297 (IntegerComputedClassCell.leftNumerator ![(5/64),0,0] ![(1/320),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(5/64),0,0] ![(1/320),1,(1/4)]) (IntegerComputedClassCell.denominator ![(5/64),0,0] ![(1/320),1,(1/4)]))
theorem leaf00297_transform : affine00297=(NestedInteger.clearedAll 3 raw00297 (IntegerComputedClassCell.leftNumerator ![(5/64),0,0] ![(1/320),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(5/64),0,0] ![(1/320),1,(1/4)]) (IntegerComputedClassCell.denominator ![(5/64),0,0] ![(1/320),1,(1/4)])) := by decide +kernel
#print axioms leaf00297_transform
theorem leaf00297_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00297=true := by decide +kernel
#print axioms leaf00297_sign
theorem leaf00297_log : RationalLog.accepts (377767865/4294967296) (-5220359645/4294967296) 4 8=true := by decide +kernel
#print axioms leaf00297_log
def leaf00297 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (353683675459/500000000000) (377767865/4294967296) (-5220359645/4294967296) 4 8 ![52,0,4] ![(5/64),0,0] ![(1/320),1,(1/4)] affine00297
theorem leaf00297_checked : FastNestedCellData.accepts 1 0 4 leaf00297=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (353683675459/500000000000) (377767865/4294967296) (-5220359645/4294967296) 4 8 ![52,0,4] ![(5/64),0,0] ![(1/320),1,(1/4)] 652431224424112062798175299174400000000000 97977614296375845362149904177294682882048 138510229754346810674339905536000000000000 raw00297 affine00297
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00297_raw leaf00297_rectangular
    leaf00297_transform leaf00297_sign leaf00297_log
#print axioms leaf00297_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
