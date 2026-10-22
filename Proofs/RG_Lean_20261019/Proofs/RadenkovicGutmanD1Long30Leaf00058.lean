/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00058 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 48301180585118365413245399859200000000000 46818973329663454336091047860227977248768 3576134613455922534104671715328000000000000))
theorem leaf00058_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 48301180585118365413245399859200000000000 46818973329663454336091047860227977248768 3576134613455922534104671715328000000000000 raw00058=true := by decide +kernel
#print axioms leaf00058_raw
theorem leaf00058_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00058=true := by decide +kernel
#print axioms leaf00058_rectangular
def affine00058 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00058 (IntegerComputedClassCell.leftNumerator ![(27/16000),0,(1/4)] ![(1/16000),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(27/16000),0,(1/4)] ![(1/16000),1,(1/4)]) (IntegerComputedClassCell.denominator ![(27/16000),0,(1/4)] ![(1/16000),1,(1/4)]))
theorem leaf00058_transform : affine00058=(NestedInteger.clearedAll 3 raw00058 (IntegerComputedClassCell.leftNumerator ![(27/16000),0,(1/4)] ![(1/16000),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(27/16000),0,(1/4)] ![(1/16000),1,(1/4)]) (IntegerComputedClassCell.denominator ![(27/16000),0,(1/4)] ![(1/16000),1,(1/4)])) := by decide +kernel
#print axioms leaf00058_transform
theorem leaf00058_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00058=true := by decide +kernel
#print axioms leaf00058_sign
theorem leaf00058_log : RationalLog.accepts (4109368515/4294967296) (-23716051/1073741824) 1 8=true := by decide +kernel
#print axioms leaf00058_log
def leaf00058 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (13092061231/1000000000000) (4109368515/4294967296) (-23716051/1073741824) 1 8 ![60,0,4] ![(27/16000),0,(1/4)] ![(1/16000),1,(1/4)] affine00058
theorem leaf00058_checked : FastNestedCellData.accepts 1 2 4 leaf00058=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (13092061231/1000000000000) (4109368515/4294967296) (-23716051/1073741824) 1 8 ![60,0,4] ![(27/16000),0,(1/4)] ![(1/16000),1,(1/4)] 48301180585118365413245399859200000000000 46818973329663454336091047860227977248768 3576134613455922534104671715328000000000000 raw00058 affine00058
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00058_raw leaf00058_rectangular
    leaf00058_transform leaf00058_sign leaf00058_log
#print axioms leaf00058_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
