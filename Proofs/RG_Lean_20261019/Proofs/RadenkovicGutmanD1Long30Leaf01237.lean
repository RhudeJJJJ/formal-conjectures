/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01237 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 125200297163041193933609631744000000000000 137232313740943487949428225683480362614784 20219515668765427755706719666176000000000000))
theorem leaf01237_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 125200297163041193933609631744000000000000 137232313740943487949428225683480362614784 20219515668765427755706719666176000000000000 raw01237=true := by decide +kernel
#print axioms leaf01237_raw
theorem leaf01237_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01237=true := by decide +kernel
#print axioms leaf01237_rectangular
def affine01237 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01237 (IntegerComputedClassCell.leftNumerator ![(1/4),0,(3/4)] ![(1/64),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(1/4),0,(3/4)] ![(1/64),1,(1/8)]) (IntegerComputedClassCell.denominator ![(1/4),0,(3/4)] ![(1/64),1,(1/8)]))
theorem leaf01237_transform : affine01237=(NestedInteger.clearedAll 3 raw01237 (IntegerComputedClassCell.leftNumerator ![(1/4),0,(3/4)] ![(1/64),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(1/4),0,(3/4)] ![(1/64),1,(1/8)]) (IntegerComputedClassCell.denominator ![(1/4),0,(3/4)] ![(1/64),1,(1/8)])) := by decide +kernel
#print axioms leaf01237_transform
theorem leaf01237_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01237=true := by decide +kernel
#print axioms leaf01237_sign
theorem leaf01237_log : RationalLog.accepts (4675986359/4294967296) (91263959/2147483648) 0 8=true := by decide +kernel
#print axioms leaf01237_log
def leaf01237 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (6787121709/1000000000000) (4675986359/4294967296) (91263959/2147483648) 0 8 ![60,0,4] ![(1/4),0,(3/4)] ![(1/64),1,(1/8)] affine01237
theorem leaf01237_checked : FastNestedCellData.accepts 1 2 4 leaf01237=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (6787121709/1000000000000) (4675986359/4294967296) (91263959/2147483648) 0 8 ![60,0,4] ![(1/4),0,(3/4)] ![(1/64),1,(1/8)] 125200297163041193933609631744000000000000 137232313740943487949428225683480362614784 20219515668765427755706719666176000000000000 raw01237 affine01237
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01237_raw leaf01237_rectangular
    leaf01237_transform leaf01237_sign leaf01237_log
#print axioms leaf01237_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
