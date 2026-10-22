/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00908 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 72493201278888629033022101913600000000000 38190967373761117128918416060162557083648 97181389239645285421383732428800000000000))
theorem leaf00908_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 72493201278888629033022101913600000000000 38190967373761117128918416060162557083648 97181389239645285421383732428800000000000 raw00908=true := by decide +kernel
#print axioms leaf00908_raw
theorem leaf00908_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00908=true := by decide +kernel
#print axioms leaf00908_rectangular
def affine00908 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00908 (IntegerComputedClassCell.leftNumerator ![(9/128),0,(1/4)] ![(1/640),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(9/128),0,(1/4)] ![(1/640),1,(1/4)]) (IntegerComputedClassCell.denominator ![(9/128),0,(1/4)] ![(1/640),1,(1/4)]))
theorem leaf00908_transform : affine00908=(NestedInteger.clearedAll 3 raw00908 (IntegerComputedClassCell.leftNumerator ![(9/128),0,(1/4)] ![(1/640),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(9/128),0,(1/4)] ![(1/640),1,(1/4)]) (IntegerComputedClassCell.denominator ![(9/128),0,(1/4)] ![(1/640),1,(1/4)])) := by decide +kernel
#print axioms leaf00908_transform
theorem leaf00908_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00908=true := by decide +kernel
#print axioms leaf00908_sign
theorem leaf00908_log : RationalLog.accepts (812168909/2147483648) (-2088092277/4294967296) 2 8=true := by decide +kernel
#print axioms leaf00908_log
def leaf00908 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (78597286317/200000000000) (812168909/2147483648) (-2088092277/4294967296) 2 8 ![60,0,4] ![(9/128),0,(1/4)] ![(1/640),1,(1/4)] affine00908
theorem leaf00908_checked : FastNestedCellData.accepts 1 2 4 leaf00908=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (78597286317/200000000000) (812168909/2147483648) (-2088092277/4294967296) 2 8 ![60,0,4] ![(9/128),0,(1/4)] ![(1/640),1,(1/4)] 72493201278888629033022101913600000000000 38190967373761117128918416060162557083648 97181389239645285421383732428800000000000 raw00908 affine00908
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00908_raw leaf00908_rectangular
    leaf00908_transform leaf00908_sign leaf00908_log
#print axioms leaf00908_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
