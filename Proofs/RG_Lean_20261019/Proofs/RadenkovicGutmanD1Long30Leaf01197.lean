/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01197 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 2460375583720447245866657382400000000000 2877304014589002492669614598132011630592 154090558747481877453421412352000000000000))
theorem leaf01197_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 2460375583720447245866657382400000000000 2877304014589002492669614598132011630592 154090558747481877453421412352000000000000 raw01197=true := by decide +kernel
#print axioms leaf01197_raw
theorem leaf01197_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01197=true := by decide +kernel
#print axioms leaf01197_rectangular
def affine01197 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01197 (IntegerComputedClassCell.leftNumerator ![(3/8),0,(3/4)] ![(1/32),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(3/8),0,(3/4)] ![(1/32),1,(1/8)]) (IntegerComputedClassCell.denominator ![(3/8),0,(3/4)] ![(1/32),1,(1/8)]))
theorem leaf01197_transform : affine01197=(NestedInteger.clearedAll 3 raw01197 (IntegerComputedClassCell.leftNumerator ![(3/8),0,(3/4)] ![(1/32),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(3/8),0,(3/4)] ![(1/32),1,(1/8)]) (IntegerComputedClassCell.denominator ![(3/8),0,(3/4)] ![(1/32),1,(1/8)])) := by decide +kernel
#print axioms leaf01197_transform
theorem leaf01197_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01197=true := by decide +kernel
#print axioms leaf01197_sign
theorem leaf01197_log : RationalLog.accepts (2465355165/2147483648) (18527297/268435456) 0 8=true := by decide +kernel
#print axioms leaf01197_log
def leaf01197 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (18672811871/1000000000000) (2465355165/2147483648) (18527297/268435456) 0 8 ![60,0,4] ![(3/8),0,(3/4)] ![(1/32),1,(1/8)] affine01197
theorem leaf01197_checked : FastNestedCellData.accepts 1 2 4 leaf01197=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (18672811871/1000000000000) (2465355165/2147483648) (18527297/268435456) 0 8 ![60,0,4] ![(3/8),0,(3/4)] ![(1/32),1,(1/8)] 2460375583720447245866657382400000000000 2877304014589002492669614598132011630592 154090558747481877453421412352000000000000 raw01197 affine01197
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01197_raw leaf01197_rectangular
    leaf01197_transform leaf01197_sign leaf01197_log
#print axioms leaf01197_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
