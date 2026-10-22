/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00604 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 1334867453790634845151747375104000000000000 1137260745758473359250425266160694280060928 15715985780093042350622467162112000000000000))
theorem leaf00604_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 1334867453790634845151747375104000000000000 1137260745758473359250425266160694280060928 15715985780093042350622467162112000000000000 raw00604=true := by decide +kernel
#print axioms leaf00604_raw
theorem leaf00604_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00604=true := by decide +kernel
#print axioms leaf00604_rectangular
def affine00604 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00604 (IntegerComputedClassCell.leftNumerator ![(63/3200),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(63/3200),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(63/3200),0,(1/2)] ![(1/3200),1,(1/2)]))
theorem leaf00604_transform : affine00604=(NestedInteger.clearedAll 3 raw00604 (IntegerComputedClassCell.leftNumerator ![(63/3200),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(63/3200),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(63/3200),0,(1/2)] ![(1/3200),1,(1/2)])) := by decide +kernel
#print axioms leaf00604_transform
theorem leaf00604_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00604=true := by decide +kernel
#print axioms leaf00604_sign
theorem leaf00604_log : RationalLog.accepts (3412241963/4294967296) (-123520261/1073741824) 1 8=true := by decide +kernel
#print axioms leaf00604_log
def leaf00604 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (72363309669/1000000000000) (3412241963/4294967296) (-123520261/1073741824) 1 8 ![60,0,4] ![(63/3200),0,(1/2)] ![(1/3200),1,(1/2)] affine00604
theorem leaf00604_checked : FastNestedCellData.accepts 1 2 4 leaf00604=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (72363309669/1000000000000) (3412241963/4294967296) (-123520261/1073741824) 1 8 ![60,0,4] ![(63/3200),0,(1/2)] ![(1/3200),1,(1/2)] 1334867453790634845151747375104000000000000 1137260745758473359250425266160694280060928 15715985780093042350622467162112000000000000 raw00604 affine00604
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00604_raw leaf00604_rectangular
    leaf00604_transform leaf00604_sign leaf00604_log
#print axioms leaf00604_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
