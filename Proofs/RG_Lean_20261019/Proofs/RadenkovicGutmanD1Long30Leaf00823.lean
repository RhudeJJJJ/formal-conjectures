/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00823 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 350425581265453161724512305152000000000000 198128019358197167573181887365892011982848 651853250434335946116928897024000000000000))
theorem leaf00823_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 350425581265453161724512305152000000000000 198128019358197167573181887365892011982848 651853250434335946116928897024000000000000 raw00823=true := by decide +kernel
#print axioms leaf00823_raw
theorem leaf00823_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00823=true := by decide +kernel
#print axioms leaf00823_rectangular
def affine00823 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00823 (IntegerComputedClassCell.leftNumerator ![(37/800),0,(1/4)] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(37/800),0,(1/4)] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(37/800),0,(1/4)] ![(3/3200),1,(1/4)]))
theorem leaf00823_transform : affine00823=(NestedInteger.clearedAll 3 raw00823 (IntegerComputedClassCell.leftNumerator ![(37/800),0,(1/4)] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(37/800),0,(1/4)] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(37/800),0,(1/4)] ![(3/3200),1,(1/4)])) := by decide +kernel
#print axioms leaf00823_transform
theorem leaf00823_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00823=true := by decide +kernel
#print axioms leaf00823_sign
theorem leaf00823_log : RationalLog.accepts (931151701/2147483648) (-1794501469/4294967296) 2 8=true := by decide +kernel
#print axioms leaf00823_log
def leaf00823 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (151972870601/500000000000) (931151701/2147483648) (-1794501469/4294967296) 2 8 ![60,0,4] ![(37/800),0,(1/4)] ![(3/3200),1,(1/4)] affine00823
theorem leaf00823_checked : FastNestedCellData.accepts 1 2 4 leaf00823=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (151972870601/500000000000) (931151701/2147483648) (-1794501469/4294967296) 2 8 ![60,0,4] ![(37/800),0,(1/4)] ![(3/3200),1,(1/4)] 350425581265453161724512305152000000000000 198128019358197167573181887365892011982848 651853250434335946116928897024000000000000 raw00823 affine00823
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00823_raw leaf00823_rectangular
    leaf00823_transform leaf00823_sign leaf00823_log
#print axioms leaf00823_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
