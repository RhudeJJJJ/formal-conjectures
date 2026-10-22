/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01176 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 10758839270184367265362739200000000000 13223386640073769469878209449941794816 369016506020614649646415872000000000000))
theorem leaf01176_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 10758839270184367265362739200000000000 13223386640073769469878209449941794816 369016506020614649646415872000000000000 raw01176=true := by decide +kernel
#print axioms leaf01176_raw
theorem leaf01176_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01176=true := by decide +kernel
#print axioms leaf01176_rectangular
def affine01176 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01176 (IntegerComputedClassCell.leftNumerator ![(1/2),0,(1/2)] ![(1/16),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(1/2),0,(1/2)] ![(1/16),1,(1/4)]) (IntegerComputedClassCell.denominator ![(1/2),0,(1/2)] ![(1/16),1,(1/4)]))
theorem leaf01176_transform : affine01176=(NestedInteger.clearedAll 3 raw01176 (IntegerComputedClassCell.leftNumerator ![(1/2),0,(1/2)] ![(1/16),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(1/2),0,(1/2)] ![(1/16),1,(1/4)]) (IntegerComputedClassCell.denominator ![(1/2),0,(1/2)] ![(1/16),1,(1/4)])) := by decide +kernel
#print axioms leaf01176_transform
theorem leaf01176_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01176=true := by decide +kernel
#print axioms leaf01176_sign
theorem leaf01176_log : RationalLog.accepts (318512835/268435456) (183665981/2147483648) 0 8=true := by decide +kernel
#print axioms leaf01176_log
def leaf01176 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (8958533307/250000000000) (318512835/268435456) (183665981/2147483648) 0 8 ![60,0,4] ![(1/2),0,(1/2)] ![(1/16),1,(1/4)] affine01176
theorem leaf01176_checked : FastNestedCellData.accepts 1 2 4 leaf01176=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (8958533307/250000000000) (318512835/268435456) (183665981/2147483648) 0 8 ![60,0,4] ![(1/2),0,(1/2)] ![(1/16),1,(1/4)] 10758839270184367265362739200000000000 13223386640073769469878209449941794816 369016506020614649646415872000000000000 raw01176 affine01176
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01176_raw leaf01176_rectangular
    leaf01176_transform leaf01176_sign leaf01176_log
#print axioms leaf01176_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
