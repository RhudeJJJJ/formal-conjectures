/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00690 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 2508073431040700062730970726400000000000 72795553728935867738021266217886547968 83657398438916924650605772800000000000))
theorem leaf00690_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 2508073431040700062730970726400000000000 72795553728935867738021266217886547968 83657398438916924650605772800000000000 raw00690=true := by decide +kernel
#print axioms leaf00690_raw
theorem leaf00690_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00690=true := by decide +kernel
#print axioms leaf00690_rectangular
def affine00690 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00690 (IntegerComputedClassCell.leftNumerator ![(179/6400),0,0] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(179/6400),0,0] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(179/6400),0,0] ![(3/6400),1,(1/16)]))
theorem leaf00690_transform : affine00690=(NestedInteger.clearedAll 3 raw00690 (IntegerComputedClassCell.leftNumerator ![(179/6400),0,0] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(179/6400),0,0] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(179/6400),0,0] ![(3/6400),1,(1/16)])) := by decide +kernel
#print axioms leaf00690_transform
theorem leaf00690_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00690=true := by decide +kernel
#print axioms leaf00690_sign
theorem leaf00690_log : RationalLog.accepts (16664223/1073741824) (-2236411423/1073741824) 7 8=true := by decide +kernel
#print axioms leaf00690_log
def leaf00690 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (43508138603/50000000000) (16664223/1073741824) (-2236411423/1073741824) 7 8 ![60,0,4] ![(179/6400),0,0] ![(3/6400),1,(1/16)] affine00690
theorem leaf00690_checked : FastNestedCellData.accepts 1 2 4 leaf00690=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (43508138603/50000000000) (16664223/1073741824) (-2236411423/1073741824) 7 8 ![60,0,4] ![(179/6400),0,0] ![(3/6400),1,(1/16)] 2508073431040700062730970726400000000000 72795553728935867738021266217886547968 83657398438916924650605772800000000000 raw00690 affine00690
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00690_raw leaf00690_rectangular
    leaf00690_transform leaf00690_sign leaf00690_log
#print axioms leaf00690_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
