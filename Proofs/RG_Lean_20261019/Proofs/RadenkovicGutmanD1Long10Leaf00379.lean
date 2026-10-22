/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00379 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 2109961473343741234551516561408000000000000 2315316947788582751161482323523424135151616 6747367937749430247413140946944000000000000))
theorem leaf00379_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 2109961473343741234551516561408000000000000 2315316947788582751161482323523424135151616 6747367937749430247413140946944000000000000 raw00379=true := by decide +kernel
#print axioms leaf00379_raw
theorem leaf00379_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00379=true := by decide +kernel
#print axioms leaf00379_rectangular
def affine00379 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00379 (IntegerComputedClassCell.leftNumerator ![(31/80),0,(1/4)] ![(3/80),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(31/80),0,(1/4)] ![(3/80),1,(1/4)]) (IntegerComputedClassCell.denominator ![(31/80),0,(1/4)] ![(3/80),1,(1/4)]))
theorem leaf00379_transform : affine00379=(NestedInteger.clearedAll 3 raw00379 (IntegerComputedClassCell.leftNumerator ![(31/80),0,(1/4)] ![(3/80),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(31/80),0,(1/4)] ![(3/80),1,(1/4)]) (IntegerComputedClassCell.denominator ![(31/80),0,(1/4)] ![(3/80),1,(1/4)])) := by decide +kernel
#print axioms leaf00379_transform
theorem leaf00379_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00379=true := by decide +kernel
#print axioms leaf00379_sign
theorem leaf00379_log : RationalLog.accepts (3508918653/4294967296) (-54260481/536870912) 1 8=true := by decide +kernel
#print axioms leaf00379_log
def leaf00379 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (343143721989/1000000000000) (3508918653/4294967296) (-54260481/536870912) 1 8 ![52,0,4] ![(31/80),0,(1/4)] ![(3/80),1,(1/4)] affine00379
theorem leaf00379_checked : FastNestedCellData.accepts 1 0 4 leaf00379=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (343143721989/1000000000000) (3508918653/4294967296) (-54260481/536870912) 1 8 ![52,0,4] ![(31/80),0,(1/4)] ![(3/80),1,(1/4)] 2109961473343741234551516561408000000000000 2315316947788582751161482323523424135151616 6747367937749430247413140946944000000000000 raw00379 affine00379
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00379_raw leaf00379_rectangular
    leaf00379_transform leaf00379_sign leaf00379_log
#print axioms leaf00379_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
