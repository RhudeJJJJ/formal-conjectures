/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01094 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 151403764029081193575088128000000000000 168288397552728298391686240064715620352 715120515539088247516823552000000000000))
theorem leaf01094_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 151403764029081193575088128000000000000 168288397552728298391686240064715620352 715120515539088247516823552000000000000 raw01094=true := by decide +kernel
#print axioms leaf01094_raw
theorem leaf01094_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01094=true := by decide +kernel
#print axioms leaf01094_rectangular
def affine01094 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01094 (IntegerComputedClassCell.leftNumerator ![(37/80),0,(1/2)] ![(3/80),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(37/80),0,(1/2)] ![(3/80),1,(1/2)]) (IntegerComputedClassCell.denominator ![(37/80),0,(1/2)] ![(3/80),1,(1/2)]))
theorem leaf01094_transform : affine01094=(NestedInteger.clearedAll 3 raw01094 (IntegerComputedClassCell.leftNumerator ![(37/80),0,(1/2)] ![(3/80),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(37/80),0,(1/2)] ![(3/80),1,(1/2)]) (IntegerComputedClassCell.denominator ![(37/80),0,(1/2)] ![(3/80),1,(1/2)])) := by decide +kernel
#print axioms leaf01094_transform
theorem leaf01094_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01094=true := by decide +kernel
#print axioms leaf01094_sign
theorem leaf01094_log : RationalLog.accepts (483064183/536870912) (-113395905/2147483648) 1 8=true := by decide +kernel
#print axioms leaf01094_log
def leaf01094 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (29416090347/125000000000) (483064183/536870912) (-113395905/2147483648) 1 8 ![60,0,4] ![(37/80),0,(1/2)] ![(3/80),1,(1/2)] affine01094
theorem leaf01094_checked : FastNestedCellData.accepts 1 2 4 leaf01094=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (29416090347/125000000000) (483064183/536870912) (-113395905/2147483648) 1 8 ![60,0,4] ![(37/80),0,(1/2)] ![(3/80),1,(1/2)] 151403764029081193575088128000000000000 168288397552728298391686240064715620352 715120515539088247516823552000000000000 raw01094 affine01094
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01094_raw leaf01094_rectangular
    leaf01094_transform leaf01094_sign leaf01094_log
#print axioms leaf01094_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
