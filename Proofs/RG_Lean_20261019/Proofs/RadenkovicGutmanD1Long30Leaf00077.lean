/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00077 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 141215880303954107887698051072000000000000 131466870716168981105929112456561241882624 4293312680296206498801456775168000000000000))
theorem leaf00077_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 141215880303954107887698051072000000000000 131466870716168981105929112456561241882624 4293312680296206498801456775168000000000000 raw00077=true := by decide +kernel
#print axioms leaf00077_raw
theorem leaf00077_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00077=true := by decide +kernel
#print axioms leaf00077_rectangular
def affine00077 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00077 (IntegerComputedClassCell.leftNumerator ![(31/16000),0,(1/8)] ![(1/16000),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(31/16000),0,(1/8)] ![(1/16000),1,(1/8)]) (IntegerComputedClassCell.denominator ![(31/16000),0,(1/8)] ![(1/16000),1,(1/8)]))
theorem leaf00077_transform : affine00077=(NestedInteger.clearedAll 3 raw00077 (IntegerComputedClassCell.leftNumerator ![(31/16000),0,(1/8)] ![(1/16000),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(31/16000),0,(1/8)] ![(1/16000),1,(1/8)]) (IntegerComputedClassCell.denominator ![(31/16000),0,(1/8)] ![(1/16000),1,(1/8)])) := by decide +kernel
#print axioms leaf00077_transform
theorem leaf00077_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00077=true := by decide +kernel
#print axioms leaf00077_sign
theorem leaf00077_log : RationalLog.accepts (1939829387/2147483648) (-109196057/2147483648) 1 8=true := by decide +kernel
#print axioms leaf00077_log
def leaf00077 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (30621312843/1000000000000) (1939829387/2147483648) (-109196057/2147483648) 1 8 ![60,0,4] ![(31/16000),0,(1/8)] ![(1/16000),1,(1/8)] affine00077
theorem leaf00077_checked : FastNestedCellData.accepts 1 2 4 leaf00077=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (30621312843/1000000000000) (1939829387/2147483648) (-109196057/2147483648) 1 8 ![60,0,4] ![(31/16000),0,(1/8)] ![(1/16000),1,(1/8)] 141215880303954107887698051072000000000000 131466870716168981105929112456561241882624 4293312680296206498801456775168000000000000 raw00077 affine00077
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00077_raw leaf00077_rectangular
    leaf00077_transform leaf00077_sign leaf00077_log
#print axioms leaf00077_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
