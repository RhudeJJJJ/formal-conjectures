/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00474 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 8314418810224734360189901209600000000000 7504726977496612349961029000082996854784 166503253031587338568027498086400000000000))
theorem leaf00474_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 8314418810224734360189901209600000000000 7504726977496612349961029000082996854784 166503253031587338568027498086400000000000 raw00474=true := by decide +kernel
#print axioms leaf00474_raw
theorem leaf00474_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00474=true := by decide +kernel
#print axioms leaf00474_rectangular
def affine00474 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00474 (IntegerComputedClassCell.leftNumerator ![(39/3200),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(39/3200),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.denominator ![(39/3200),0,(1/2)] ![(1/6400),1,(1/2)]))
theorem leaf00474_transform : affine00474=(NestedInteger.clearedAll 3 raw00474 (IntegerComputedClassCell.leftNumerator ![(39/3200),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(39/3200),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.denominator ![(39/3200),0,(1/2)] ![(1/6400),1,(1/2)])) := by decide +kernel
#print axioms leaf00474_transform
theorem leaf00474_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00474=true := by decide +kernel
#print axioms leaf00474_sign
theorem leaf00474_log : RationalLog.accepts (1854754457/2147483648) (-314701827/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00474_log
def leaf00474 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (9014510937/200000000000) (1854754457/2147483648) (-314701827/4294967296) 1 8 ![60,0,4] ![(39/3200),0,(1/2)] ![(1/6400),1,(1/2)] affine00474
theorem leaf00474_checked : FastNestedCellData.accepts 1 2 4 leaf00474=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (9014510937/200000000000) (1854754457/2147483648) (-314701827/4294967296) 1 8 ![60,0,4] ![(39/3200),0,(1/2)] ![(1/6400),1,(1/2)] 8314418810224734360189901209600000000000 7504726977496612349961029000082996854784 166503253031587338568027498086400000000000 raw00474 affine00474
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00474_raw leaf00474_rectangular
    leaf00474_transform leaf00474_sign leaf00474_log
#print axioms leaf00474_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
