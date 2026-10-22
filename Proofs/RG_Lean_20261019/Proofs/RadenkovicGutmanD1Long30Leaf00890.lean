/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00890 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 15739306532046402218874181255168000000000000 2326857393086454967619444922630835531677696 2727117788759657626410839703552000000000000))
theorem leaf00890_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 15739306532046402218874181255168000000000000 2326857393086454967619444922630835531677696 2727117788759657626410839703552000000000000 raw00890=true := by decide +kernel
#print axioms leaf00890_raw
theorem leaf00890_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00890=true := by decide +kernel
#print axioms leaf00890_rectangular
def affine00890 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00890 (IntegerComputedClassCell.leftNumerator ![(21/320),0,0] ![(1/640),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(21/320),0,0] ![(1/640),1,(1/16)]) (IntegerComputedClassCell.denominator ![(21/320),0,0] ![(1/640),1,(1/16)]))
theorem leaf00890_transform : affine00890=(NestedInteger.clearedAll 3 raw00890 (IntegerComputedClassCell.leftNumerator ![(21/320),0,0] ![(1/640),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(21/320),0,0] ![(1/640),1,(1/16)]) (IntegerComputedClassCell.denominator ![(21/320),0,0] ![(1/640),1,(1/16)])) := by decide +kernel
#print axioms leaf00890_transform
theorem leaf00890_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00890=true := by decide +kernel
#print axioms leaf00890_sign
theorem leaf00890_log : RationalLog.accepts (342621669/4294967296) (-1357516999/1073741824) 4 8=true := by decide +kernel
#print axioms leaf00890_log
def leaf00890 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (853229516773/1000000000000) (342621669/4294967296) (-1357516999/1073741824) 4 8 ![60,0,4] ![(21/320),0,0] ![(1/640),1,(1/16)] affine00890
theorem leaf00890_checked : FastNestedCellData.accepts 1 2 4 leaf00890=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (853229516773/1000000000000) (342621669/4294967296) (-1357516999/1073741824) 4 8 ![60,0,4] ![(21/320),0,0] ![(1/640),1,(1/16)] 15739306532046402218874181255168000000000000 2326857393086454967619444922630835531677696 2727117788759657626410839703552000000000000 raw00890 affine00890
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00890_raw leaf00890_rectangular
    leaf00890_transform leaf00890_sign leaf00890_log
#print axioms leaf00890_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
