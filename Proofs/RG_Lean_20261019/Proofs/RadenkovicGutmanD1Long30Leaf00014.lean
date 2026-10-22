/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00014 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 19687513018044041637614583808000000000000 19482010385055317210400047117126426689536 4563548215626418842334572576768000000000000))
theorem leaf00014_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 19687513018044041637614583808000000000000 19482010385055317210400047117126426689536 4563548215626418842334572576768000000000000 raw00014=true := by decide +kernel
#print axioms leaf00014_raw
theorem leaf00014_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00014=true := by decide +kernel
#print axioms leaf00014_rectangular
def affine00014 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00014 (IntegerComputedClassCell.leftNumerator ![(9/8000),0,(1/2)] ![(1/16000),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(9/8000),0,(1/2)] ![(1/16000),1,(1/2)]) (IntegerComputedClassCell.denominator ![(9/8000),0,(1/2)] ![(1/16000),1,(1/2)]))
theorem leaf00014_transform : affine00014=(NestedInteger.clearedAll 3 raw00014 (IntegerComputedClassCell.leftNumerator ![(9/8000),0,(1/2)] ![(1/16000),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(9/8000),0,(1/2)] ![(1/16000),1,(1/2)]) (IntegerComputedClassCell.denominator ![(9/8000),0,(1/2)] ![(1/16000),1,(1/2)])) := by decide +kernel
#print axioms leaf00014_transform
theorem leaf00014_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00014=true := by decide +kernel
#print axioms leaf00014_sign
theorem leaf00014_log : RationalLog.accepts (2116034283/2147483648) (-3960245/536870912) 1 8=true := by decide +kernel
#print axioms leaf00014_log
def leaf00014 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (4269048877/1000000000000) (2116034283/2147483648) (-3960245/536870912) 1 8 ![60,0,4] ![(9/8000),0,(1/2)] ![(1/16000),1,(1/2)] affine00014
theorem leaf00014_checked : FastNestedCellData.accepts 1 2 4 leaf00014=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (4269048877/1000000000000) (2116034283/2147483648) (-3960245/536870912) 1 8 ![60,0,4] ![(9/8000),0,(1/2)] ![(1/16000),1,(1/2)] 19687513018044041637614583808000000000000 19482010385055317210400047117126426689536 4563548215626418842334572576768000000000000 raw00014 affine00014
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00014_raw leaf00014_rectangular
    leaf00014_transform leaf00014_sign leaf00014_log
#print axioms leaf00014_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
