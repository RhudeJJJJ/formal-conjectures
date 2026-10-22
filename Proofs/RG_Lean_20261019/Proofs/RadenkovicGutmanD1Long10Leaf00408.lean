/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00408 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack true 26718945430135915206104055808000000000000 36597078650950323722147292591789533298688 394790646704185178579569475584000000000000))
theorem leaf00408_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    true 26718945430135915206104055808000000000000 36597078650950323722147292591789533298688 394790646704185178579569475584000000000000 raw00408=true := by decide +kernel
#print axioms leaf00408_raw
theorem leaf00408_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00408=true := by decide +kernel
#print axioms leaf00408_rectangular
def affine00408 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00408 (IntegerComputedClassCell.leftNumerator ![(3/4),0,0] ![(1/8),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(3/4),0,0] ![(1/8),1,(1/2)]) (IntegerComputedClassCell.denominator ![(3/4),0,0] ![(1/8),1,(1/2)]))
theorem leaf00408_transform : affine00408=(NestedInteger.clearedAll 3 raw00408 (IntegerComputedClassCell.leftNumerator ![(3/4),0,0] ![(1/8),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(3/4),0,0] ![(1/8),1,(1/2)]) (IntegerComputedClassCell.denominator ![(3/4),0,0] ![(1/8),1,(1/2)])) := by decide +kernel
#print axioms leaf00408_transform
theorem leaf00408_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00408=true := by decide +kernel
#print axioms leaf00408_sign
theorem leaf00408_log : RationalLog.accepts (1345941077/1073741824) (242605387/2147483648) 0 8=true := by decide +kernel
#print axioms leaf00408_log
def leaf00408 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack true (46349981891/500000000000) (1345941077/1073741824) (242605387/2147483648) 0 8 ![52,0,4] ![(3/4),0,0] ![(1/8),1,(1/2)] affine00408
theorem leaf00408_checked : FastNestedCellData.accepts 1 0 4 leaf00408=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack true (46349981891/500000000000) (1345941077/1073741824) (242605387/2147483648) 0 8 ![52,0,4] ![(3/4),0,0] ![(1/8),1,(1/2)] 26718945430135915206104055808000000000000 36597078650950323722147292591789533298688 394790646704185178579569475584000000000000 raw00408 affine00408
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00408_raw leaf00408_rectangular
    leaf00408_transform leaf00408_sign leaf00408_log
#print axioms leaf00408_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
