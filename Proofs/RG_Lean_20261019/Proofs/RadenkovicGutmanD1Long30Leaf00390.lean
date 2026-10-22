/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00390 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 593853772447749588463806054400000000000 1790835689615694812744445857756086272 2716226559003512323178496000000000000))
theorem leaf00390_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 593853772447749588463806054400000000000 1790835689615694812744445857756086272 2716226559003512323178496000000000000 raw00390=true := by decide +kernel
#print axioms leaf00390_raw
theorem leaf00390_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00390=true := by decide +kernel
#print axioms leaf00390_rectangular
def affine00390 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00390 (IntegerComputedClassCell.leftNumerator ![(31/3200),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(31/3200),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(31/3200),0,0] ![(1/6400),1,(1/16)]))
theorem leaf00390_transform : affine00390=(NestedInteger.clearedAll 3 raw00390 (IntegerComputedClassCell.leftNumerator ![(31/3200),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(31/3200),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(31/3200),0,0] ![(1/6400),1,(1/16)])) := by decide +kernel
#print axioms leaf00390_transform
theorem leaf00390_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00390=true := by decide +kernel
#print axioms leaf00390_sign
theorem leaf00390_log : RationalLog.accepts (975705/536870912) (-13551379527/4294967296) 10 8=true := by decide +kernel
#print axioms leaf00390_log
def leaf00390 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (82413766429/125000000000) (975705/536870912) (-13551379527/4294967296) 10 8 ![60,0,4] ![(31/3200),0,0] ![(1/6400),1,(1/16)] affine00390
theorem leaf00390_checked : FastNestedCellData.accepts 1 2 4 leaf00390=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (82413766429/125000000000) (975705/536870912) (-13551379527/4294967296) 10 8 ![60,0,4] ![(31/3200),0,0] ![(1/6400),1,(1/16)] 593853772447749588463806054400000000000 1790835689615694812744445857756086272 2716226559003512323178496000000000000 raw00390 affine00390
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00390_raw leaf00390_rectangular
    leaf00390_transform leaf00390_sign leaf00390_log
#print axioms leaf00390_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
