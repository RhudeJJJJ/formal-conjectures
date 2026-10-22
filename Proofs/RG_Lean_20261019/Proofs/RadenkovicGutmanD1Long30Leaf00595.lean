/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00595 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 3827934995827992665590425714688000000000000 52407345448457930203909667635868798550016 63137493852679768422825852928000000000000))
theorem leaf00595_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 3827934995827992665590425714688000000000000 52407345448457930203909667635868798550016 63137493852679768422825852928000000000000 raw00595=true := by decide +kernel
#print axioms leaf00595_raw
theorem leaf00595_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00595=true := by decide +kernel
#print axioms leaf00595_rectangular
def affine00595 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00595 (IntegerComputedClassCell.leftNumerator ![(31/1600),0,0] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(31/1600),0,0] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.denominator ![(31/1600),0,0] ![(1/3200),1,(1/16)]))
theorem leaf00595_transform : affine00595=(NestedInteger.clearedAll 3 raw00595 (IntegerComputedClassCell.leftNumerator ![(31/1600),0,0] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(31/1600),0,0] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.denominator ![(31/1600),0,0] ![(1/3200),1,(1/16)])) := by decide +kernel
#print axioms leaf00595_transform
theorem leaf00595_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00595=true := by decide +kernel
#print axioms leaf00595_sign
theorem leaf00595_log : RationalLog.accepts (32131001/4294967296) (-5256372129/2147483648) 8 8=true := by decide +kernel
#print axioms leaf00595_log
def leaf00595 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (415025543861/500000000000) (32131001/4294967296) (-5256372129/2147483648) 8 8 ![60,0,4] ![(31/1600),0,0] ![(1/3200),1,(1/16)] affine00595
theorem leaf00595_checked : FastNestedCellData.accepts 1 2 4 leaf00595=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (415025543861/500000000000) (32131001/4294967296) (-5256372129/2147483648) 8 8 ![60,0,4] ![(31/1600),0,0] ![(1/3200),1,(1/16)] 3827934995827992665590425714688000000000000 52407345448457930203909667635868798550016 63137493852679768422825852928000000000000 raw00595 affine00595
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00595_raw leaf00595_rectangular
    leaf00595_transform leaf00595_sign leaf00595_log
#print axioms leaf00595_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
