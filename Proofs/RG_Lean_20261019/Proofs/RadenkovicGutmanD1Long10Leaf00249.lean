/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00249 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 3017034677394297164874913939456000000000000 172052604345684263869334585215711877005312 262990875060238760342777233408000000000000))
theorem leaf00249_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 3017034677394297164874913939456000000000000 172052604345684263869334585215711877005312 262990875060238760342777233408000000000000 raw00249=true := by decide +kernel
#print axioms leaf00249_raw
theorem leaf00249_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00249=true := by decide +kernel
#print axioms leaf00249_rectangular
def affine00249 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00249 (IntegerComputedClassCell.leftNumerator ![(77/1600),0,0] ![(3/1600),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(77/1600),0,0] ![(3/1600),1,(1/4)]) (IntegerComputedClassCell.denominator ![(77/1600),0,0] ![(3/1600),1,(1/4)]))
theorem leaf00249_transform : affine00249=(NestedInteger.clearedAll 3 raw00249 (IntegerComputedClassCell.leftNumerator ![(77/1600),0,0] ![(3/1600),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(77/1600),0,0] ![(3/1600),1,(1/4)]) (IntegerComputedClassCell.denominator ![(77/1600),0,0] ![(3/1600),1,(1/4)])) := by decide +kernel
#print axioms leaf00249_transform
theorem leaf00249_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00249=true := by decide +kernel
#print axioms leaf00249_sign
theorem leaf00249_log : RationalLog.accepts (74031889/2147483648) (-7231771849/4294967296) 5 8=true := by decide +kernel
#print axioms leaf00249_log
def leaf00249 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (654215110339/1000000000000) (74031889/2147483648) (-7231771849/4294967296) 5 8 ![52,0,4] ![(77/1600),0,0] ![(3/1600),1,(1/4)] affine00249
theorem leaf00249_checked : FastNestedCellData.accepts 1 0 4 leaf00249=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (654215110339/1000000000000) (74031889/2147483648) (-7231771849/4294967296) 5 8 ![52,0,4] ![(77/1600),0,0] ![(3/1600),1,(1/4)] 3017034677394297164874913939456000000000000 172052604345684263869334585215711877005312 262990875060238760342777233408000000000000 raw00249 affine00249
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00249_raw leaf00249_rectangular
    leaf00249_transform leaf00249_sign leaf00249_log
#print axioms leaf00249_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
