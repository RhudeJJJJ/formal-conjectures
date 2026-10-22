/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00250 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 58749045653523259904987706163200000000000 32214038776727972084334790317636159799296 101149579926702824102082432204800000000000))
theorem leaf00250_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 58749045653523259904987706163200000000000 32214038776727972084334790317636159799296 101149579926702824102082432204800000000000 raw00250=true := by decide +kernel
#print axioms leaf00250_raw
theorem leaf00250_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00250=true := by decide +kernel
#print axioms leaf00250_rectangular
def affine00250 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00250 (IntegerComputedClassCell.leftNumerator ![(77/1600),0,(1/4)] ![(3/1600),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(77/1600),0,(1/4)] ![(3/1600),1,(1/4)]) (IntegerComputedClassCell.denominator ![(77/1600),0,(1/4)] ![(3/1600),1,(1/4)]))
theorem leaf00250_transform : affine00250=(NestedInteger.clearedAll 3 raw00250 (IntegerComputedClassCell.leftNumerator ![(77/1600),0,(1/4)] ![(3/1600),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(77/1600),0,(1/4)] ![(3/1600),1,(1/4)]) (IntegerComputedClassCell.denominator ![(77/1600),0,(1/4)] ![(3/1600),1,(1/4)])) := by decide +kernel
#print axioms leaf00250_transform
theorem leaf00250_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00250=true := by decide +kernel
#print axioms leaf00250_sign
theorem leaf00250_log : RationalLog.accepts (893101747/2147483648) (-117756133/268435456) 2 8=true := by decide +kernel
#print axioms leaf00250_log
def leaf00250 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (63695842929/200000000000) (893101747/2147483648) (-117756133/268435456) 2 8 ![52,0,4] ![(77/1600),0,(1/4)] ![(3/1600),1,(1/4)] affine00250
theorem leaf00250_checked : FastNestedCellData.accepts 1 0 4 leaf00250=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (63695842929/200000000000) (893101747/2147483648) (-117756133/268435456) 2 8 ![52,0,4] ![(77/1600),0,(1/4)] ![(3/1600),1,(1/4)] 58749045653523259904987706163200000000000 32214038776727972084334790317636159799296 101149579926702824102082432204800000000000 raw00250 affine00250
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00250_raw leaf00250_rectangular
    leaf00250_transform leaf00250_sign leaf00250_log
#print axioms leaf00250_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
