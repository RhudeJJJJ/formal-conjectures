/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01226 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 639426988320373759541248000000000000 712867046572115054932067670437134336 78450800090074513772904448000000000000))
theorem leaf01226_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 639426988320373759541248000000000000 712867046572115054932067670437134336 78450800090074513772904448000000000000 raw01226=true := by decide +kernel
#print axioms leaf01226_raw
theorem leaf01226_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01226=true := by decide +kernel
#print axioms leaf01226_rectangular
def affine01226 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01226 (IntegerComputedClassCell.leftNumerator ![(9/32),0,(1/2)] ![(1/64),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(9/32),0,(1/2)] ![(1/64),1,(1/4)]) (IntegerComputedClassCell.denominator ![(9/32),0,(1/2)] ![(1/64),1,(1/4)]))
theorem leaf01226_transform : affine01226=(NestedInteger.clearedAll 3 raw01226 (IntegerComputedClassCell.leftNumerator ![(9/32),0,(1/2)] ![(1/64),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(9/32),0,(1/2)] ![(1/64),1,(1/4)]) (IntegerComputedClassCell.denominator ![(9/32),0,(1/2)] ![(1/64),1,(1/4)])) := by decide +kernel
#print axioms leaf01226_transform
theorem leaf01226_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01226=true := by decide +kernel
#print axioms leaf01226_sign
theorem leaf01226_log : RationalLog.accepts (593142337/536870912) (214054127/4294967296) 0 8=true := by decide +kernel
#print axioms leaf01226_log
def leaf01226 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (141981313/15625000000) (593142337/536870912) (214054127/4294967296) 0 8 ![60,0,4] ![(9/32),0,(1/2)] ![(1/64),1,(1/4)] affine01226
theorem leaf01226_checked : FastNestedCellData.accepts 1 2 4 leaf01226=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (141981313/15625000000) (593142337/536870912) (214054127/4294967296) 0 8 ![60,0,4] ![(9/32),0,(1/2)] ![(1/64),1,(1/4)] 639426988320373759541248000000000000 712867046572115054932067670437134336 78450800090074513772904448000000000000 raw01226 affine01226
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01226_raw leaf01226_rectangular
    leaf01226_transform leaf01226_sign leaf01226_log
#print axioms leaf01226_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
