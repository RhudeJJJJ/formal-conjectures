/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00842 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 9693484548224803105129849946112000000000000 3728487242322855150528534017504401164337152 7095327753301716558079470862336000000000000))
theorem leaf00842_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 9693484548224803105129849946112000000000000 3728487242322855150528534017504401164337152 7095327753301716558079470862336000000000000 raw00842=true := by decide +kernel
#print axioms leaf00842_raw
theorem leaf00842_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00842=true := by decide +kernel
#print axioms leaf00842_rectangular
def affine00842 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00842 (IntegerComputedClassCell.leftNumerator ![(1/20),0,(1/8)] ![(1/640),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(1/20),0,(1/8)] ![(1/640),1,(1/8)]) (IntegerComputedClassCell.denominator ![(1/20),0,(1/8)] ![(1/640),1,(1/8)]))
theorem leaf00842_transform : affine00842=(NestedInteger.clearedAll 3 raw00842 (IntegerComputedClassCell.leftNumerator ![(1/20),0,(1/8)] ![(1/640),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(1/20),0,(1/8)] ![(1/640),1,(1/8)]) (IntegerComputedClassCell.denominator ![(1/20),0,(1/8)] ![(1/640),1,(1/8)])) := by decide +kernel
#print axioms leaf00842_transform
theorem leaf00842_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00842=true := by decide +kernel
#print axioms leaf00842_sign
theorem leaf00842_log : RationalLog.accepts (1082940763/4294967296) (-2958725027/4294967296) 2 8=true := by decide +kernel
#print axioms leaf00842_log
def leaf00842 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (525484850307/1000000000000) (1082940763/4294967296) (-2958725027/4294967296) 2 8 ![60,0,4] ![(1/20),0,(1/8)] ![(1/640),1,(1/8)] affine00842
theorem leaf00842_checked : FastNestedCellData.accepts 1 2 4 leaf00842=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (525484850307/1000000000000) (1082940763/4294967296) (-2958725027/4294967296) 2 8 ![60,0,4] ![(1/20),0,(1/8)] ![(1/640),1,(1/8)] 9693484548224803105129849946112000000000000 3728487242322855150528534017504401164337152 7095327753301716558079470862336000000000000 raw00842 affine00842
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00842_raw leaf00842_rectangular
    leaf00842_transform leaf00842_sign leaf00842_log
#print axioms leaf00842_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
