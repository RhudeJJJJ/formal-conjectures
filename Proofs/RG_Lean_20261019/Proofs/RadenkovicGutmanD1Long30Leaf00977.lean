/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00977 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 434431169076353539293950928486400000000000 216398740483415745146883605551018009427968 367547493616331366655492672716800000000000))
theorem leaf00977_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 434431169076353539293950928486400000000000 216398740483415745146883605551018009427968 367547493616331366655492672716800000000000 raw00977=true := by decide +kernel
#print axioms leaf00977_raw
theorem leaf00977_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00977=true := by decide +kernel
#print axioms leaf00977_rectangular
def affine00977 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00977 (IntegerComputedClassCell.leftNumerator ![(19/160),0,(1/8)] ![(1/160),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(19/160),0,(1/8)] ![(1/160),1,(1/8)]) (IntegerComputedClassCell.denominator ![(19/160),0,(1/8)] ![(1/160),1,(1/8)]))
theorem leaf00977_transform : affine00977=(NestedInteger.clearedAll 3 raw00977 (IntegerComputedClassCell.leftNumerator ![(19/160),0,(1/8)] ![(1/160),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(19/160),0,(1/8)] ![(1/160),1,(1/8)]) (IntegerComputedClassCell.denominator ![(19/160),0,(1/8)] ![(1/160),1,(1/8)])) := by decide +kernel
#print axioms leaf00977_transform
theorem leaf00977_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00977=true := by decide +kernel
#print axioms leaf00977_sign
theorem leaf00977_log : RationalLog.accepts (1346586377/4294967296) (-1245402211/2147483648) 2 8=true := by decide +kernel
#print axioms leaf00977_log
def leaf00977 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (117752804327/200000000000) (1346586377/4294967296) (-1245402211/2147483648) 2 8 ![60,0,4] ![(19/160),0,(1/8)] ![(1/160),1,(1/8)] affine00977
theorem leaf00977_checked : FastNestedCellData.accepts 1 2 4 leaf00977=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (117752804327/200000000000) (1346586377/4294967296) (-1245402211/2147483648) 2 8 ![60,0,4] ![(19/160),0,(1/8)] ![(1/160),1,(1/8)] 434431169076353539293950928486400000000000 216398740483415745146883605551018009427968 367547493616331366655492672716800000000000 raw00977 affine00977
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00977_raw leaf00977_rectangular
    leaf00977_transform leaf00977_sign leaf00977_log
#print axioms leaf00977_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
