/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00981 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 762900706486832535411324092416000000000000 359884232900417172974590500730756659150848 543869297474547937719539990528000000000000))
theorem leaf00981_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 762900706486832535411324092416000000000000 359884232900417172974590500730756659150848 543869297474547937719539990528000000000000 raw00981=true := by decide +kernel
#print axioms leaf00981_raw
theorem leaf00981_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00981=true := by decide +kernel
#print axioms leaf00981_rectangular
def affine00981 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00981 (IntegerComputedClassCell.leftNumerator ![(1/8),0,(1/16)] ![(1/160),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(1/8),0,(1/16)] ![(1/160),1,(1/16)]) (IntegerComputedClassCell.denominator ![(1/8),0,(1/16)] ![(1/160),1,(1/16)]))
theorem leaf00981_transform : affine00981=(NestedInteger.clearedAll 3 raw00981 (IntegerComputedClassCell.leftNumerator ![(1/8),0,(1/16)] ![(1/160),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(1/8),0,(1/16)] ![(1/160),1,(1/16)]) (IntegerComputedClassCell.denominator ![(1/8),0,(1/16)] ![(1/160),1,(1/16)])) := by decide +kernel
#print axioms leaf00981_transform
theorem leaf00981_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00981=true := by decide +kernel
#print axioms leaf00981_sign
theorem leaf00981_log : RationalLog.accepts (304817017/1073741824) (-676024223/1073741824) 2 8=true := by decide +kernel
#print axioms leaf00981_log
def leaf00981 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (661710882691/1000000000000) (304817017/1073741824) (-676024223/1073741824) 2 8 ![60,0,4] ![(1/8),0,(1/16)] ![(1/160),1,(1/16)] affine00981
theorem leaf00981_checked : FastNestedCellData.accepts 1 2 4 leaf00981=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (661710882691/1000000000000) (304817017/1073741824) (-676024223/1073741824) 2 8 ![60,0,4] ![(1/8),0,(1/16)] ![(1/160),1,(1/16)] 762900706486832535411324092416000000000000 359884232900417172974590500730756659150848 543869297474547937719539990528000000000000 raw00981 affine00981
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00981_raw leaf00981_rectangular
    leaf00981_transform leaf00981_sign leaf00981_log
#print axioms leaf00981_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
