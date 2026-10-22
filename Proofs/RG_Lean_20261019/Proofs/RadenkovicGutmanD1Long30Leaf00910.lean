/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00910 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 60582425495840284849423253504000000000000 10498315859539738077924002406580283768832 12486845419231302407776370688000000000000))
theorem leaf00910_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 60582425495840284849423253504000000000000 10498315859539738077924002406580283768832 12486845419231302407776370688000000000000 raw00910=true := by decide +kernel
#print axioms leaf00910_raw
theorem leaf00910_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00910=true := by decide +kernel
#print axioms leaf00910_rectangular
def affine00910 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00910 (IntegerComputedClassCell.leftNumerator ![(23/320),0,0] ![(1/320),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(23/320),0,0] ![(1/320),1,(1/16)]) (IntegerComputedClassCell.denominator ![(23/320),0,0] ![(1/320),1,(1/16)]))
theorem leaf00910_transform : affine00910=(NestedInteger.clearedAll 3 raw00910 (IntegerComputedClassCell.leftNumerator ![(23/320),0,0] ![(1/320),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(23/320),0,0] ![(1/320),1,(1/16)]) (IntegerComputedClassCell.denominator ![(23/320),0,0] ![(1/320),1,(1/16)])) := by decide +kernel
#print axioms leaf00910_transform
theorem leaf00910_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00910=true := by decide +kernel
#print axioms leaf00910_sign
theorem leaf00910_log : RationalLog.accepts (50541489/536870912) (-634303099/536870912) 4 8=true := by decide +kernel
#print axioms leaf00910_log
def leaf00910 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (420375022957/500000000000) (50541489/536870912) (-634303099/536870912) 4 8 ![60,0,4] ![(23/320),0,0] ![(1/320),1,(1/16)] affine00910
theorem leaf00910_checked : FastNestedCellData.accepts 1 2 4 leaf00910=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (420375022957/500000000000) (50541489/536870912) (-634303099/536870912) 4 8 ![60,0,4] ![(23/320),0,0] ![(1/320),1,(1/16)] 60582425495840284849423253504000000000000 10498315859539738077924002406580283768832 12486845419231302407776370688000000000000 raw00910 affine00910
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00910_raw leaf00910_rectangular
    leaf00910_transform leaf00910_sign leaf00910_log
#print axioms leaf00910_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
