/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00015 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 133176308080982438690355675136000000000000 1575160669729017554345167242410328064 13636333935891991414964224000000000000))
theorem leaf00015_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 133176308080982438690355675136000000000000 1575160669729017554345167242410328064 13636333935891991414964224000000000000 raw00015=true := by decide +kernel
#print axioms leaf00015_raw
theorem leaf00015_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00015=true := by decide +kernel
#print axioms leaf00015_rectangular
def affine00015 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00015 (IntegerComputedClassCell.leftNumerator ![(19/16000),0,0] ![(1/16000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(19/16000),0,0] ![(1/16000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(19/16000),0,0] ![(1/16000),1,(1/16)]))
theorem leaf00015_transform : affine00015=(NestedInteger.clearedAll 3 raw00015 (IntegerComputedClassCell.leftNumerator ![(19/16000),0,0] ![(1/16000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(19/16000),0,0] ![(1/16000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(19/16000),0,0] ![(1/16000),1,(1/16)])) := by decide +kernel
#print axioms leaf00015_transform
theorem leaf00015_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00015=true := by decide +kernel
#print axioms leaf00015_sign
theorem leaf00015_log : RationalLog.accepts (45539/4294967296) (-12299052969/2147483648) 17 8=true := by decide +kernel
#print axioms leaf00015_log
def leaf00015 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (28878008509/250000000000) (45539/4294967296) (-12299052969/2147483648) 17 8 ![60,0,4] ![(19/16000),0,0] ![(1/16000),1,(1/16)] affine00015
theorem leaf00015_checked : FastNestedCellData.accepts 1 2 4 leaf00015=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (28878008509/250000000000) (45539/4294967296) (-12299052969/2147483648) 17 8 ![60,0,4] ![(19/16000),0,0] ![(1/16000),1,(1/16)] 133176308080982438690355675136000000000000 1575160669729017554345167242410328064 13636333935891991414964224000000000000 raw00015 affine00015
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00015_raw leaf00015_rectangular
    leaf00015_transform leaf00015_sign leaf00015_log
#print axioms leaf00015_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
