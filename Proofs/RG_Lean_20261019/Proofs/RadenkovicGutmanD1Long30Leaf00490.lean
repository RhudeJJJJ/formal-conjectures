/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00490 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 857878112571237657056380977152000000000000 4852073182933851711200148279395906224128 6520809229838116675506929664000000000000))
theorem leaf00490_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 857878112571237657056380977152000000000000 4852073182933851711200148279395906224128 6520809229838116675506929664000000000000 raw00490=true := by decide +kernel
#print axioms leaf00490_raw
theorem leaf00490_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00490=true := by decide +kernel
#print axioms leaf00490_rectangular
def affine00490 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00490 (IntegerComputedClassCell.leftNumerator ![(41/3200),0,0] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(41/3200),0,0] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.denominator ![(41/3200),0,0] ![(1/3200),1,(1/16)]))
theorem leaf00490_transform : affine00490=(NestedInteger.clearedAll 3 raw00490 (IntegerComputedClassCell.leftNumerator ![(41/3200),0,0] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(41/3200),0,0] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.denominator ![(41/3200),0,0] ![(1/3200),1,(1/16)])) := by decide +kernel
#print axioms leaf00490_transform
theorem leaf00490_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00490=true := by decide +kernel
#print axioms leaf00490_sign
theorem leaf00490_log : RationalLog.accepts (6964061/2147483648) (-6153925141/2147483648) 9 8=true := by decide +kernel
#print axioms leaf00490_log
def leaf00490 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (372045325351/500000000000) (6964061/2147483648) (-6153925141/2147483648) 9 8 ![60,0,4] ![(41/3200),0,0] ![(1/3200),1,(1/16)] affine00490
theorem leaf00490_checked : FastNestedCellData.accepts 1 2 4 leaf00490=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (372045325351/500000000000) (6964061/2147483648) (-6153925141/2147483648) 9 8 ![60,0,4] ![(41/3200),0,0] ![(1/3200),1,(1/16)] 857878112571237657056380977152000000000000 4852073182933851711200148279395906224128 6520809229838116675506929664000000000000 raw00490 affine00490
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00490_raw leaf00490_rectangular
    leaf00490_transform leaf00490_sign leaf00490_log
#print axioms leaf00490_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
