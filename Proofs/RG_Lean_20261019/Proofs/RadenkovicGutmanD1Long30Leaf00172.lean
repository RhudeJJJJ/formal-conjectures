/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00172 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 3340542645240293554535373209600000000000 2923737233090452428490355821375247089664 50453472501729299065619873792000000000000))
theorem leaf00172_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 3340542645240293554535373209600000000000 2923737233090452428490355821375247089664 50453472501729299065619873792000000000000 raw00172=true := by decide +kernel
#print axioms leaf00172_raw
theorem leaf00172_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00172=true := by decide +kernel
#print axioms leaf00172_rectangular
def affine00172 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00172 (IntegerComputedClassCell.leftNumerator ![(59/16000),0,(1/8)] ![(3/32000),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(59/16000),0,(1/8)] ![(3/32000),1,(1/8)]) (IntegerComputedClassCell.denominator ![(59/16000),0,(1/8)] ![(3/32000),1,(1/8)]))
theorem leaf00172_transform : affine00172=(NestedInteger.clearedAll 3 raw00172 (IntegerComputedClassCell.leftNumerator ![(59/16000),0,(1/8)] ![(3/32000),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(59/16000),0,(1/8)] ![(3/32000),1,(1/8)]) (IntegerComputedClassCell.denominator ![(59/16000),0,(1/8)] ![(3/32000),1,(1/8)])) := by decide +kernel
#print axioms leaf00172_transform
theorem leaf00172_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00172=true := by decide +kernel
#print axioms leaf00172_sign
theorem leaf00172_log : RationalLog.accepts (1776586585/2147483648) (-407169133/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00172_log
def leaf00172 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (14487294373/250000000000) (1776586585/2147483648) (-407169133/4294967296) 1 8 ![60,0,4] ![(59/16000),0,(1/8)] ![(3/32000),1,(1/8)] affine00172
theorem leaf00172_checked : FastNestedCellData.accepts 1 2 4 leaf00172=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (14487294373/250000000000) (1776586585/2147483648) (-407169133/4294967296) 1 8 ![60,0,4] ![(59/16000),0,(1/8)] ![(3/32000),1,(1/8)] 3340542645240293554535373209600000000000 2923737233090452428490355821375247089664 50453472501729299065619873792000000000000 raw00172 affine00172
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00172_raw leaf00172_rectangular
    leaf00172_transform leaf00172_sign leaf00172_log
#print axioms leaf00172_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
