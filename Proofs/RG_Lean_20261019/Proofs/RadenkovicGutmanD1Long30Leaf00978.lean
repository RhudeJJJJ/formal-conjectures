/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00978 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 8513561604197402485895922188288000000000000 4887394891406233552412663763694072199380992 10589753964366313711336993849344000000000000))
theorem leaf00978_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 8513561604197402485895922188288000000000000 4887394891406233552412663763694072199380992 10589753964366313711336993849344000000000000 raw00978=true := by decide +kernel
#print axioms leaf00978_raw
theorem leaf00978_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00978=true := by decide +kernel
#print axioms leaf00978_rectangular
def affine00978 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00978 (IntegerComputedClassCell.leftNumerator ![(19/160),0,(1/4)] ![(1/160),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(19/160),0,(1/4)] ![(1/160),1,(1/4)]) (IntegerComputedClassCell.denominator ![(19/160),0,(1/4)] ![(1/160),1,(1/4)]))
theorem leaf00978_transform : affine00978=(NestedInteger.clearedAll 3 raw00978 (IntegerComputedClassCell.leftNumerator ![(19/160),0,(1/4)] ![(1/160),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(19/160),0,(1/4)] ![(1/160),1,(1/4)]) (IntegerComputedClassCell.denominator ![(19/160),0,(1/4)] ![(1/160),1,(1/4)])) := by decide +kernel
#print axioms leaf00978_transform
theorem leaf00978_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00978=true := by decide +kernel
#print axioms leaf00978_sign
theorem leaf00978_log : RationalLog.accepts (1687022673/4294967296) (-1003388897/2147483648) 2 8=true := by decide +kernel
#print axioms leaf00978_log
def leaf00978 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (461521099343/1000000000000) (1687022673/4294967296) (-1003388897/2147483648) 2 8 ![60,0,4] ![(19/160),0,(1/4)] ![(1/160),1,(1/4)] affine00978
theorem leaf00978_checked : FastNestedCellData.accepts 1 2 4 leaf00978=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (461521099343/1000000000000) (1687022673/4294967296) (-1003388897/2147483648) 2 8 ![60,0,4] ![(19/160),0,(1/4)] ![(1/160),1,(1/4)] 8513561604197402485895922188288000000000000 4887394891406233552412663763694072199380992 10589753964366313711336993849344000000000000 raw00978 affine00978
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00978_raw leaf00978_rectangular
    leaf00978_transform leaf00978_sign leaf00978_log
#print axioms leaf00978_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
