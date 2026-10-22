/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00237 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 88401019368028819191521869824000000000000 74265758672258817707640334189295686385664 968570168548938274389817819136000000000000))
theorem leaf00237_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 88401019368028819191521869824000000000000 74265758672258817707640334189295686385664 968570168548938274389817819136000000000000 raw00237=true := by decide +kernel
#print axioms leaf00237_raw
theorem leaf00237_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00237=true := by decide +kernel
#print axioms leaf00237_rectangular
def affine00237 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00237 (IntegerComputedClassCell.leftNumerator ![(157/32000),0,(1/8)] ![(3/32000),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(157/32000),0,(1/8)] ![(3/32000),1,(1/8)]) (IntegerComputedClassCell.denominator ![(157/32000),0,(1/8)] ![(3/32000),1,(1/8)]))
theorem leaf00237_transform : affine00237=(NestedInteger.clearedAll 3 raw00237 (IntegerComputedClassCell.leftNumerator ![(157/32000),0,(1/8)] ![(3/32000),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(157/32000),0,(1/8)] ![(3/32000),1,(1/8)]) (IntegerComputedClassCell.denominator ![(157/32000),0,(1/8)] ![(3/32000),1,(1/8)])) := by decide +kernel
#print axioms leaf00237_transform
theorem leaf00237_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00237=true := by decide +kernel
#print axioms leaf00237_sign
theorem leaf00237_log : RationalLog.accepts (837811511/1073741824) (-266407939/2147483648) 1 8=true := by decide +kernel
#print axioms leaf00237_log
def leaf00237 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (76675661799/1000000000000) (837811511/1073741824) (-266407939/2147483648) 1 8 ![60,0,4] ![(157/32000),0,(1/8)] ![(3/32000),1,(1/8)] affine00237
theorem leaf00237_checked : FastNestedCellData.accepts 1 2 4 leaf00237=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (76675661799/1000000000000) (837811511/1073741824) (-266407939/2147483648) 1 8 ![60,0,4] ![(157/32000),0,(1/8)] ![(3/32000),1,(1/8)] 88401019368028819191521869824000000000000 74265758672258817707640334189295686385664 968570168548938274389817819136000000000000 raw00237 affine00237
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00237_raw leaf00237_rectangular
    leaf00237_transform leaf00237_sign leaf00237_log
#print axioms leaf00237_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
