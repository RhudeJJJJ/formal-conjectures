/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00389 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 47768885152360674712738091499520000000000 57627670510812249281049749708145726324736 222538768925922564499610533888000000000000))
theorem leaf00389_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 47768885152360674712738091499520000000000 57627670510812249281049749708145726324736 222538768925922564499610533888000000000000 raw00389=true := by decide +kernel
#print axioms leaf00389_raw
theorem leaf00389_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00389=true := by decide +kernel
#print axioms leaf00389_rectangular
def affine00389 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00389 (IntegerComputedClassCell.leftNumerator ![(1/2),0,(3/4)] ![(1/16),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(1/2),0,(3/4)] ![(1/16),1,(1/4)]) (IntegerComputedClassCell.denominator ![(1/2),0,(3/4)] ![(1/16),1,(1/4)]))
theorem leaf00389_transform : affine00389=(NestedInteger.clearedAll 3 raw00389 (IntegerComputedClassCell.leftNumerator ![(1/2),0,(3/4)] ![(1/16),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(1/2),0,(3/4)] ![(1/16),1,(1/4)]) (IntegerComputedClassCell.denominator ![(1/2),0,(3/4)] ![(1/16),1,(1/4)])) := by decide +kernel
#print axioms leaf00389_transform
theorem leaf00389_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00389=true := by decide +kernel
#print axioms leaf00389_sign
theorem leaf00389_log : RationalLog.accepts (2057810575/2147483648) (-45799585/2147483648) 1 8=true := by decide +kernel
#print axioms leaf00389_log
def leaf00389 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (258955645297/1000000000000) (2057810575/2147483648) (-45799585/2147483648) 1 8 ![52,0,4] ![(1/2),0,(3/4)] ![(1/16),1,(1/4)] affine00389
theorem leaf00389_checked : FastNestedCellData.accepts 1 0 4 leaf00389=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (258955645297/1000000000000) (2057810575/2147483648) (-45799585/2147483648) 1 8 ![52,0,4] ![(1/2),0,(3/4)] ![(1/16),1,(1/4)] 47768885152360674712738091499520000000000 57627670510812249281049749708145726324736 222538768925922564499610533888000000000000 raw00389 affine00389
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00389_raw leaf00389_rectangular
    leaf00389_transform leaf00389_sign leaf00389_log
#print axioms leaf00389_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
