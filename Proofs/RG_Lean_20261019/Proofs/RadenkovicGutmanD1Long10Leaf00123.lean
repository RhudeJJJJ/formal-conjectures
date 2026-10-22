/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00123 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 67396304739097861919290163200000000000 214740076041603374530068225103757312 675270624256673567473664000000000000))
theorem leaf00123_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 67396304739097861919290163200000000000 214740076041603374530068225103757312 675270624256673567473664000000000000 raw00123=true := by decide +kernel
#print axioms leaf00123_raw
theorem leaf00123_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00123=true := by decide +kernel
#print axioms leaf00123_rectangular
def affine00123 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00123 (IntegerComputedClassCell.leftNumerator ![(23/1600),0,0] ![(1/1600),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(23/1600),0,0] ![(1/1600),1,(1/4)]) (IntegerComputedClassCell.denominator ![(23/1600),0,0] ![(1/1600),1,(1/4)]))
theorem leaf00123_transform : affine00123=(NestedInteger.clearedAll 3 raw00123 (IntegerComputedClassCell.leftNumerator ![(23/1600),0,0] ![(1/1600),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(23/1600),0,0] ![(1/1600),1,(1/4)]) (IntegerComputedClassCell.denominator ![(23/1600),0,0] ![(1/1600),1,(1/4)])) := by decide +kernel
#print axioms leaf00123_transform
theorem leaf00123_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00123=true := by decide +kernel
#print axioms leaf00123_sign
theorem leaf00123_log : RationalLog.accepts (1297865/536870912) (-12938668907/4294967296) 9 8=true := by decide +kernel
#print axioms leaf00123_log
def leaf00123 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (79501487377/250000000000) (1297865/536870912) (-12938668907/4294967296) 9 8 ![52,0,4] ![(23/1600),0,0] ![(1/1600),1,(1/4)] affine00123
theorem leaf00123_checked : FastNestedCellData.accepts 1 0 4 leaf00123=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (79501487377/250000000000) (1297865/536870912) (-12938668907/4294967296) 9 8 ![52,0,4] ![(23/1600),0,0] ![(1/1600),1,(1/4)] 67396304739097861919290163200000000000 214740076041603374530068225103757312 675270624256673567473664000000000000 raw00123 affine00123
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00123_raw leaf00123_rectangular
    leaf00123_transform leaf00123_sign leaf00123_log
#print axioms leaf00123_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
