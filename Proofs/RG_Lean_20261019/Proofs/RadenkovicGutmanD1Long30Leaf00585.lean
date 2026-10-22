/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00585 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 55943087184748217899474223104000000000000 715192051493163905095670752451758129152 867015913309625407676350464000000000000))
theorem leaf00585_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 55943087184748217899474223104000000000000 715192051493163905095670752451758129152 867015913309625407676350464000000000000 raw00585=true := by decide +kernel
#print axioms leaf00585_raw
theorem leaf00585_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00585=true := by decide +kernel
#print axioms leaf00585_rectangular
def affine00585 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00585 (IntegerComputedClassCell.leftNumerator ![(3/160),0,0] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(3/160),0,0] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.denominator ![(3/160),0,0] ![(1/3200),1,(1/16)]))
theorem leaf00585_transform : affine00585=(NestedInteger.clearedAll 3 raw00585 (IntegerComputedClassCell.leftNumerator ![(3/160),0,0] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(3/160),0,0] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.denominator ![(3/160),0,0] ![(1/3200),1,(1/16)])) := by decide +kernel
#print axioms leaf00585_transform
theorem leaf00585_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00585=true := by decide +kernel
#print axioms leaf00585_sign
theorem leaf00585_log : RationalLog.accepts (7522109/1073741824) (-2663447969/1073741824) 8 8=true := by decide +kernel
#print axioms leaf00585_log
def leaf00585 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (824889186593/1000000000000) (7522109/1073741824) (-2663447969/1073741824) 8 8 ![60,0,4] ![(3/160),0,0] ![(1/3200),1,(1/16)] affine00585
theorem leaf00585_checked : FastNestedCellData.accepts 1 2 4 leaf00585=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (824889186593/1000000000000) (7522109/1073741824) (-2663447969/1073741824) 8 8 ![60,0,4] ![(3/160),0,0] ![(1/3200),1,(1/16)] 55943087184748217899474223104000000000000 715192051493163905095670752451758129152 867015913309625407676350464000000000000 raw00585 affine00585
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00585_raw leaf00585_rectangular
    leaf00585_transform leaf00585_sign leaf00585_log
#print axioms leaf00585_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
