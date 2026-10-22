/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00231 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 2890059538961948583228294037504000000000000 126038707947082219922080412447086399717376 201120751799108491055753854976000000000000))
theorem leaf00231_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 2890059538961948583228294037504000000000000 126038707947082219922080412447086399717376 201120751799108491055753854976000000000000 raw00231=true := by decide +kernel
#print axioms leaf00231_raw
theorem leaf00231_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00231=true := by decide +kernel
#print axioms leaf00231_rectangular
def affine00231 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00231 (IntegerComputedClassCell.leftNumerator ![(17/400),0,0] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(17/400),0,0] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(17/400),0,0] ![(3/3200),1,(1/4)]))
theorem leaf00231_transform : affine00231=(NestedInteger.clearedAll 3 raw00231 (IntegerComputedClassCell.leftNumerator ![(17/400),0,0] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(17/400),0,0] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(17/400),0,0] ![(3/3200),1,(1/4)])) := by decide +kernel
#print axioms leaf00231_transform
theorem leaf00231_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00231=true := by decide +kernel
#print axioms leaf00231_sign
theorem leaf00231_log : RationalLog.accepts (57573737/2147483648) (-7771712461/4294967296) 6 8=true := by decide +kernel
#print axioms leaf00231_log
def leaf00231 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (626681766151/1000000000000) (57573737/2147483648) (-7771712461/4294967296) 6 8 ![52,0,4] ![(17/400),0,0] ![(3/3200),1,(1/4)] affine00231
theorem leaf00231_checked : FastNestedCellData.accepts 1 0 4 leaf00231=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (626681766151/1000000000000) (57573737/2147483648) (-7771712461/4294967296) 6 8 ![52,0,4] ![(17/400),0,0] ![(3/3200),1,(1/4)] 2890059538961948583228294037504000000000000 126038707947082219922080412447086399717376 201120751799108491055753854976000000000000 raw00231 affine00231
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00231_raw leaf00231_rectangular
    leaf00231_transform leaf00231_sign leaf00231_log
#print axioms leaf00231_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
