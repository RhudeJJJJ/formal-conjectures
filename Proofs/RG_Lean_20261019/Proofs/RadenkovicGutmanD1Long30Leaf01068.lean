/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01068 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 6103696114064442653401780584448000000000000 6025582599887091879152090346962181064491008 18210667444434482331062827483136000000000000))
theorem leaf01068_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 6103696114064442653401780584448000000000000 6025582599887091879152090346962181064491008 18210667444434482331062827483136000000000000 raw01068=true := by decide +kernel
#print axioms leaf01068_raw
theorem leaf01068_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01068=true := by decide +kernel
#print axioms leaf01068_rectangular
def affine01068 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01068 (IntegerComputedClassCell.leftNumerator ![(53/160),0,(1/4)] ![(3/160),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(53/160),0,(1/4)] ![(3/160),1,(1/4)]) (IntegerComputedClassCell.denominator ![(53/160),0,(1/4)] ![(3/160),1,(1/4)]))
theorem leaf01068_transform : affine01068=(NestedInteger.clearedAll 3 raw01068 (IntegerComputedClassCell.leftNumerator ![(53/160),0,(1/4)] ![(3/160),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(53/160),0,(1/4)] ![(3/160),1,(1/4)]) (IntegerComputedClassCell.denominator ![(53/160),0,(1/4)] ![(3/160),1,(1/4)])) := by decide +kernel
#print axioms leaf01068_transform
theorem leaf01068_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01068=true := by decide +kernel
#print axioms leaf01068_sign
theorem leaf01068_log : RationalLog.accepts (3185858197/4294967296) (-641501159/4294967296) 1 8=true := by decide +kernel
#print axioms leaf01068_log
def leaf01068 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (330882029353/1000000000000) (3185858197/4294967296) (-641501159/4294967296) 1 8 ![60,0,4] ![(53/160),0,(1/4)] ![(3/160),1,(1/4)] affine01068
theorem leaf01068_checked : FastNestedCellData.accepts 1 2 4 leaf01068=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (330882029353/1000000000000) (3185858197/4294967296) (-641501159/4294967296) 1 8 ![60,0,4] ![(53/160),0,(1/4)] ![(3/160),1,(1/4)] 6103696114064442653401780584448000000000000 6025582599887091879152090346962181064491008 18210667444434482331062827483136000000000000 raw01068 affine01068
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01068_raw leaf01068_rectangular
    leaf01068_transform leaf01068_sign leaf01068_log
#print axioms leaf01068_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
