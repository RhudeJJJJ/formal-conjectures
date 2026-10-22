/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00447 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 50028363707438696769093894144000000000000 34214785917007066624646384341113548832768 197122989520100940352709459968000000000000))
theorem leaf00447_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 50028363707438696769093894144000000000000 34214785917007066624646384341113548832768 197122989520100940352709459968000000000000 raw00447=true := by decide +kernel
#print axioms leaf00447_raw
theorem leaf00447_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00447=true := by decide +kernel
#print axioms leaf00447_rectangular
def affine00447 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00447 (IntegerComputedClassCell.leftNumerator ![(73/6400),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(73/6400),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.denominator ![(73/6400),0,(1/8)] ![(1/6400),1,(1/8)]))
theorem leaf00447_transform : affine00447=(NestedInteger.clearedAll 3 raw00447 (IntegerComputedClassCell.leftNumerator ![(73/6400),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(73/6400),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.denominator ![(73/6400),0,(1/8)] ![(1/6400),1,(1/8)])) := by decide +kernel
#print axioms leaf00447_transform
theorem leaf00447_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00447=true := by decide +kernel
#print axioms leaf00447_sign
theorem leaf00447_log : RationalLog.accepts (2502926587/4294967296) (-1159605255/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00447_log
def leaf00447 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (21696344247/125000000000) (2502926587/4294967296) (-1159605255/4294967296) 1 8 ![60,0,4] ![(73/6400),0,(1/8)] ![(1/6400),1,(1/8)] affine00447
theorem leaf00447_checked : FastNestedCellData.accepts 1 2 4 leaf00447=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (21696344247/125000000000) (2502926587/4294967296) (-1159605255/4294967296) 1 8 ![60,0,4] ![(73/6400),0,(1/8)] ![(1/6400),1,(1/8)] 50028363707438696769093894144000000000000 34214785917007066624646384341113548832768 197122989520100940352709459968000000000000 raw00447 affine00447
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00447_raw leaf00447_rectangular
    leaf00447_transform leaf00447_sign leaf00447_log
#print axioms leaf00447_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
