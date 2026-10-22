/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00773 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 4505208386006635151097856000000000000 2713363385209120863059699088788291584 10595290914171478211559424000000000000))
theorem leaf00773_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 4505208386006635151097856000000000000 2713363385209120863059699088788291584 10595290914171478211559424000000000000 raw00773=true := by decide +kernel
#print axioms leaf00773_raw
theorem leaf00773_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00773=true := by decide +kernel
#print axioms leaf00773_rectangular
def affine00773 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00773 (IntegerComputedClassCell.leftNumerator ![(59/1600),0,(1/4)] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(59/1600),0,(1/4)] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(59/1600),0,(1/4)] ![(3/3200),1,(1/4)]))
theorem leaf00773_transform : affine00773=(NestedInteger.clearedAll 3 raw00773 (IntegerComputedClassCell.leftNumerator ![(59/1600),0,(1/4)] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(59/1600),0,(1/4)] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(59/1600),0,(1/4)] ![(3/3200),1,(1/4)])) := by decide +kernel
#print axioms leaf00773_transform
theorem leaf00773_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00773=true := by decide +kernel
#print axioms leaf00773_sign
theorem leaf00773_log : RationalLog.accepts (2011091/4194304) (-789254021/2147483648) 2 8=true := by decide +kernel
#print axioms leaf00773_log
def leaf00773 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (256091447341/1000000000000) (2011091/4194304) (-789254021/2147483648) 2 8 ![60,0,4] ![(59/1600),0,(1/4)] ![(3/3200),1,(1/4)] affine00773
theorem leaf00773_checked : FastNestedCellData.accepts 1 2 4 leaf00773=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (256091447341/1000000000000) (2011091/4194304) (-789254021/2147483648) 2 8 ![60,0,4] ![(59/1600),0,(1/4)] ![(3/3200),1,(1/4)] 4505208386006635151097856000000000000 2713363385209120863059699088788291584 10595290914171478211559424000000000000 raw00773 affine00773
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00773_raw leaf00773_rectangular
    leaf00773_transform leaf00773_sign leaf00773_log
#print axioms leaf00773_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
