/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00174 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 8811092373998837168880262053888000000000000 110442265218723623575514492736881823842304 231219934479694675064890851328000000000000))
theorem leaf00174_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 8811092373998837168880262053888000000000000 110442265218723623575514492736881823842304 231219934479694675064890851328000000000000 raw00174=true := by decide +kernel
#print axioms leaf00174_raw
theorem leaf00174_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00174=true := by decide +kernel
#print axioms leaf00174_rectangular
def affine00174 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00174 (IntegerComputedClassCell.leftNumerator ![(79/3200),0,0] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(79/3200),0,0] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(79/3200),0,0] ![(3/3200),1,(1/4)]))
theorem leaf00174_transform : affine00174=(NestedInteger.clearedAll 3 raw00174 (IntegerComputedClassCell.leftNumerator ![(79/3200),0,0] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(79/3200),0,0] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(79/3200),0,0] ![(3/3200),1,(1/4)])) := by decide +kernel
#print axioms leaf00174_transform
theorem leaf00174_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00174=true := by decide +kernel
#print axioms leaf00174_sign
theorem leaf00174_log : RationalLog.accepts (36432901/4294967296) (-5121455471/2147483648) 7 8=true := by decide +kernel
#print axioms leaf00174_log
def leaf00174 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (477650274693/1000000000000) (36432901/4294967296) (-5121455471/2147483648) 7 8 ![52,0,4] ![(79/3200),0,0] ![(3/3200),1,(1/4)] affine00174
theorem leaf00174_checked : FastNestedCellData.accepts 1 0 4 leaf00174=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (477650274693/1000000000000) (36432901/4294967296) (-5121455471/2147483648) 7 8 ![52,0,4] ![(79/3200),0,0] ![(3/3200),1,(1/4)] 8811092373998837168880262053888000000000000 110442265218723623575514492736881823842304 231219934479694675064890851328000000000000 raw00174 affine00174
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00174_raw leaf00174_rectangular
    leaf00174_transform leaf00174_sign leaf00174_log
#print axioms leaf00174_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
