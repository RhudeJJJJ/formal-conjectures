/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00880 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 15462007210808686187078746112000000000000 2095088958280523173033375938800397582336 2440935830174591421568253952000000000000))
theorem leaf00880_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 15462007210808686187078746112000000000000 2095088958280523173033375938800397582336 2440935830174591421568253952000000000000 raw00880=true := by decide +kernel
#print axioms leaf00880_raw
theorem leaf00880_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00880=true := by decide +kernel
#print axioms leaf00880_rectangular
def affine00880 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00880 (IntegerComputedClassCell.leftNumerator ![(1/16),0,0] ![(1/640),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(1/16),0,0] ![(1/640),1,(1/16)]) (IntegerComputedClassCell.denominator ![(1/16),0,0] ![(1/640),1,(1/16)]))
theorem leaf00880_transform : affine00880=(NestedInteger.clearedAll 3 raw00880 (IntegerComputedClassCell.leftNumerator ![(1/16),0,0] ![(1/640),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(1/16),0,0] ![(1/640),1,(1/16)]) (IntegerComputedClassCell.denominator ![(1/16),0,0] ![(1/640),1,(1/16)])) := by decide +kernel
#print axioms leaf00880_transform
theorem leaf00880_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00880=true := by decide +kernel
#print axioms leaf00880_sign
theorem leaf00880_log : RationalLog.accepts (19573001/268435456) (-5623098845/4294967296) 4 8=true := by decide +kernel
#print axioms leaf00880_log
def leaf00880 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (429156910309/500000000000) (19573001/268435456) (-5623098845/4294967296) 4 8 ![60,0,4] ![(1/16),0,0] ![(1/640),1,(1/16)] affine00880
theorem leaf00880_checked : FastNestedCellData.accepts 1 2 4 leaf00880=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (429156910309/500000000000) (19573001/268435456) (-5623098845/4294967296) 4 8 ![60,0,4] ![(1/16),0,0] ![(1/640),1,(1/16)] 15462007210808686187078746112000000000000 2095088958280523173033375938800397582336 2440935830174591421568253952000000000000 raw00880 affine00880
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00880_raw leaf00880_rectangular
    leaf00880_transform leaf00880_sign leaf00880_log
#print axioms leaf00880_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
