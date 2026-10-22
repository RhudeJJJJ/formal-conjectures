/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00651 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 649181512299460231392110051328000000000000 195807781388057575727971283811052780781568 347747121035559426911482413056000000000000))
theorem leaf00651_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 649181512299460231392110051328000000000000 195807781388057575727971283811052780781568 347747121035559426911482413056000000000000 raw00651=true := by decide +kernel
#print axioms leaf00651_raw
theorem leaf00651_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00651=true := by decide +kernel
#print axioms leaf00651_rectangular
def affine00651 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00651 (IntegerComputedClassCell.leftNumerator ![(31/1280),0,(1/16)] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(31/1280),0,(1/16)] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(31/1280),0,(1/16)] ![(3/6400),1,(1/16)]))
theorem leaf00651_transform : affine00651=(NestedInteger.clearedAll 3 raw00651 (IntegerComputedClassCell.leftNumerator ![(31/1280),0,(1/16)] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(31/1280),0,(1/16)] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(31/1280),0,(1/16)] ![(3/6400),1,(1/16)])) := by decide +kernel
#print axioms leaf00651_transform
theorem leaf00651_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00651=true := by decide +kernel
#print axioms leaf00651_sign
theorem leaf00651_log : RationalLog.accepts (414394321/2147483648) (-883278333/1073741824) 3 8=true := by decide +kernel
#print axioms leaf00651_log
def leaf00651 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (281537602389/500000000000) (414394321/2147483648) (-883278333/1073741824) 3 8 ![60,0,4] ![(31/1280),0,(1/16)] ![(3/6400),1,(1/16)] affine00651
theorem leaf00651_checked : FastNestedCellData.accepts 1 2 4 leaf00651=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (281537602389/500000000000) (414394321/2147483648) (-883278333/1073741824) 3 8 ![60,0,4] ![(31/1280),0,(1/16)] ![(3/6400),1,(1/16)] 649181512299460231392110051328000000000000 195807781388057575727971283811052780781568 347747121035559426911482413056000000000000 raw00651 affine00651
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00651_raw leaf00651_rectangular
    leaf00651_transform leaf00651_sign leaf00651_log
#print axioms leaf00651_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
