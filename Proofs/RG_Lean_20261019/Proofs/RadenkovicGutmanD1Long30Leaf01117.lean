/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01117 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 200701375236738220084630126592000000000000 240959136918334685330301079771422815944704 1384180703081706332314782400512000000000000))
theorem leaf01117_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 200701375236738220084630126592000000000000 240959136918334685330301079771422815944704 1384180703081706332314782400512000000000000 raw01117=true := by decide +kernel
#print axioms leaf01117_raw
theorem leaf01117_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01117=true := by decide +kernel
#print axioms leaf01117_rectangular
def affine01117 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01117 (IntegerComputedClassCell.leftNumerator ![(5/8),0,(3/4)] ![(1/16),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(5/8),0,(3/4)] ![(1/16),1,(1/8)]) (IntegerComputedClassCell.denominator ![(5/8),0,(3/4)] ![(1/16),1,(1/8)]))
theorem leaf01117_transform : affine01117=(NestedInteger.clearedAll 3 raw01117 (IntegerComputedClassCell.leftNumerator ![(5/8),0,(3/4)] ![(1/16),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(5/8),0,(3/4)] ![(1/16),1,(1/8)]) (IntegerComputedClassCell.denominator ![(5/8),0,(3/4)] ![(1/16),1,(1/8)])) := by decide +kernel
#print axioms leaf01117_transform
theorem leaf01117_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01117=true := by decide +kernel
#print axioms leaf01117_sign
theorem leaf01117_log : RationalLog.accepts (2195962753/2147483648) (47939999/4294967296) 0 8=true := by decide +kernel
#print axioms leaf01117_log
def leaf01117 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (87040346821/500000000000) (2195962753/2147483648) (47939999/4294967296) 0 8 ![60,0,4] ![(5/8),0,(3/4)] ![(1/16),1,(1/8)] affine01117
theorem leaf01117_checked : FastNestedCellData.accepts 1 2 4 leaf01117=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (87040346821/500000000000) (2195962753/2147483648) (47939999/4294967296) 0 8 ![60,0,4] ![(5/8),0,(3/4)] ![(1/16),1,(1/8)] 200701375236738220084630126592000000000000 240959136918334685330301079771422815944704 1384180703081706332314782400512000000000000 raw01117 affine01117
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01117_raw leaf01117_rectangular
    leaf01117_transform leaf01117_sign leaf01117_log
#print axioms leaf01117_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
