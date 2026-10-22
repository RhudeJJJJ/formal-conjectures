/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00275 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 2298338589935186390436441751552000000000000 2298130806139673081920802354453201027072 4611269093946016548408786944000000000000))
theorem leaf00275_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 2298338589935186390436441751552000000000000 2298130806139673081920802354453201027072 4611269093946016548408786944000000000000 raw00275=true := by decide +kernel
#print axioms leaf00275_raw
theorem leaf00275_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00275=true := by decide +kernel
#print axioms leaf00275_rectangular
def affine00275 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00275 (IntegerComputedClassCell.leftNumerator ![(39/6400),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(39/6400),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(39/6400),0,0] ![(1/6400),1,(1/16)]))
theorem leaf00275_transform : affine00275=(NestedInteger.clearedAll 3 raw00275 (IntegerComputedClassCell.leftNumerator ![(39/6400),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(39/6400),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(39/6400),0,0] ![(1/6400),1,(1/16)])) := by decide +kernel
#print axioms leaf00275_transform
theorem leaf00275_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00275=true := by decide +kernel
#print axioms leaf00275_sign
theorem leaf00275_log : RationalLog.accepts (1433081/2147483648) (-15702884795/4294967296) 11 8=true := by decide +kernel
#print axioms leaf00275_log
def leaf00275 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (498372738463/1000000000000) (1433081/2147483648) (-15702884795/4294967296) 11 8 ![60,0,4] ![(39/6400),0,0] ![(1/6400),1,(1/16)] affine00275
theorem leaf00275_checked : FastNestedCellData.accepts 1 2 4 leaf00275=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (498372738463/1000000000000) (1433081/2147483648) (-15702884795/4294967296) 11 8 ![60,0,4] ![(39/6400),0,0] ![(1/6400),1,(1/16)] 2298338589935186390436441751552000000000000 2298130806139673081920802354453201027072 4611269093946016548408786944000000000000 raw00275 affine00275
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00275_raw leaf00275_rectangular
    leaf00275_transform leaf00275_sign leaf00275_log
#print axioms leaf00275_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
