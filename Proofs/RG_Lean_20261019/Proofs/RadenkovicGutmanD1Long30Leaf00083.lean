/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00083 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 17973899839248423800094588928000000000000 17314073035628120509137359681985458470912 1110597439266909242386813026304000000000000))
theorem leaf00083_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 17973899839248423800094588928000000000000 17314073035628120509137359681985458470912 1110597439266909242386813026304000000000000 raw00083=true := by decide +kernel
#print axioms leaf00083_raw
theorem leaf00083_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00083=true := by decide +kernel
#print axioms leaf00083_rectangular
def affine00083 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00083 (IntegerComputedClassCell.leftNumerator ![(1/500),0,(1/4)] ![(3/32000),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(1/500),0,(1/4)] ![(3/32000),1,(1/4)]) (IntegerComputedClassCell.denominator ![(1/500),0,(1/4)] ![(3/32000),1,(1/4)]))
theorem leaf00083_transform : affine00083=(NestedInteger.clearedAll 3 raw00083 (IntegerComputedClassCell.leftNumerator ![(1/500),0,(1/4)] ![(3/32000),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(1/500),0,(1/4)] ![(3/32000),1,(1/4)]) (IntegerComputedClassCell.denominator ![(1/500),0,(1/4)] ![(3/32000),1,(1/4)])) := by decide +kernel
#print axioms leaf00083_transform
theorem leaf00083_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00083=true := by decide +kernel
#print axioms leaf00083_sign
theorem leaf00083_log : RationalLog.accepts (1018447007/1073741824) (-113538903/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00083_log
def leaf00083 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (15589873003/1000000000000) (1018447007/1073741824) (-113538903/4294967296) 1 8 ![60,0,4] ![(1/500),0,(1/4)] ![(3/32000),1,(1/4)] affine00083
theorem leaf00083_checked : FastNestedCellData.accepts 1 2 4 leaf00083=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (15589873003/1000000000000) (1018447007/1073741824) (-113538903/4294967296) 1 8 ![60,0,4] ![(1/500),0,(1/4)] ![(3/32000),1,(1/4)] 17973899839248423800094588928000000000000 17314073035628120509137359681985458470912 1110597439266909242386813026304000000000000 raw00083 affine00083
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00083_raw leaf00083_rectangular
    leaf00083_transform leaf00083_sign leaf00083_log
#print axioms leaf00083_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
