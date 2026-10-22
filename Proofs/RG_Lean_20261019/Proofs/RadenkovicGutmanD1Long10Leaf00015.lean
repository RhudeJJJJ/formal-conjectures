/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00015 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 61750693934479375209896869888000000000000 961382352644405887136650350456471552 17949569760128134130171904000000000000))
theorem leaf00015_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 61750693934479375209896869888000000000000 961382352644405887136650350456471552 17949569760128134130171904000000000000 raw00015=true := by decide +kernel
#print axioms leaf00015_raw
theorem leaf00015_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00015=true := by decide +kernel
#print axioms leaf00015_rectangular
def affine00015 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00015 (IntegerComputedClassCell.leftNumerator ![(7/3200),0,0] ![(3/16000),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(7/3200),0,0] ![(3/16000),1,(1/4)]) (IntegerComputedClassCell.denominator ![(7/3200),0,0] ![(3/16000),1,(1/4)]))
theorem leaf00015_transform : affine00015=(NestedInteger.clearedAll 3 raw00015 (IntegerComputedClassCell.leftNumerator ![(7/3200),0,0] ![(3/16000),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(7/3200),0,0] ![(3/16000),1,(1/4)]) (IntegerComputedClassCell.denominator ![(7/3200),0,0] ![(3/16000),1,(1/4)])) := by decide +kernel
#print axioms leaf00015_transform
theorem leaf00015_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00015=true := by decide +kernel
#print axioms leaf00015_sign
theorem leaf00015_log : RationalLog.accepts (15867/1073741824) (-23885212793/4294967296) 17 8=true := by decide +kernel
#print axioms leaf00015_log
def leaf00015 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (53560189213/1000000000000) (15867/1073741824) (-23885212793/4294967296) 17 8 ![52,0,4] ![(7/3200),0,0] ![(3/16000),1,(1/4)] affine00015
theorem leaf00015_checked : FastNestedCellData.accepts 1 0 4 leaf00015=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (53560189213/1000000000000) (15867/1073741824) (-23885212793/4294967296) 17 8 ![52,0,4] ![(7/3200),0,0] ![(3/16000),1,(1/4)] 61750693934479375209896869888000000000000 961382352644405887136650350456471552 17949569760128134130171904000000000000 raw00015 affine00015
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00015_raw leaf00015_rectangular
    leaf00015_transform leaf00015_sign leaf00015_log
#print axioms leaf00015_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
