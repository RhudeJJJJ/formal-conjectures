/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00603 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 42224659711113122992156049408000000000000 30804000324670953200016799061161612935168 210271643662780896035601383424000000000000))
theorem leaf00603_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 42224659711113122992156049408000000000000 30804000324670953200016799061161612935168 210271643662780896035601383424000000000000 raw00603=true := by decide +kernel
#print axioms leaf00603_raw
theorem leaf00603_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00603=true := by decide +kernel
#print axioms leaf00603_rectangular
def affine00603 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00603 (IntegerComputedClassCell.leftNumerator ![(63/3200),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(63/3200),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(63/3200),0,(1/4)] ![(1/3200),1,(1/4)]))
theorem leaf00603_transform : affine00603=(NestedInteger.clearedAll 3 raw00603 (IntegerComputedClassCell.leftNumerator ![(63/3200),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(63/3200),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(63/3200),0,(1/4)] ![(1/3200),1,(1/4)])) := by decide +kernel
#print axioms leaf00603_transform
theorem leaf00603_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00603=true := by decide +kernel
#print axioms leaf00603_sign
theorem leaf00603_log : RationalLog.accepts (1366464019/2147483648) (-970813753/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00603_log
def leaf00603 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (36624054233/250000000000) (1366464019/2147483648) (-970813753/4294967296) 1 8 ![60,0,4] ![(63/3200),0,(1/4)] ![(1/3200),1,(1/4)] affine00603
theorem leaf00603_checked : FastNestedCellData.accepts 1 2 4 leaf00603=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (36624054233/250000000000) (1366464019/2147483648) (-970813753/4294967296) 1 8 ![60,0,4] ![(63/3200),0,(1/4)] ![(1/3200),1,(1/4)] 42224659711113122992156049408000000000000 30804000324670953200016799061161612935168 210271643662780896035601383424000000000000 raw00603 affine00603
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00603_raw leaf00603_rectangular
    leaf00603_transform leaf00603_sign leaf00603_log
#print axioms leaf00603_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
