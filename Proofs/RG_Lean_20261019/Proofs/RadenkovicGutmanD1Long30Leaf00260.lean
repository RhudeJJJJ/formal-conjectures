/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00260 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 9642398135980281868054010265600000000000 7902927718563961129598775980420235264 16798873636745949411383705600000000000))
theorem leaf00260_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 9642398135980281868054010265600000000000 7902927718563961129598775980420235264 16798873636745949411383705600000000000 raw00260=true := by decide +kernel
#print axioms leaf00260_raw
theorem leaf00260_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00260=true := by decide +kernel
#print axioms leaf00260_rectangular
def affine00260 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00260 (IntegerComputedClassCell.leftNumerator ![(9/1600),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(9/1600),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(9/1600),0,0] ![(1/6400),1,(1/16)]))
theorem leaf00260_transform : affine00260=(NestedInteger.clearedAll 3 raw00260 (IntegerComputedClassCell.leftNumerator ![(9/1600),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(9/1600),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(9/1600),0,0] ![(1/6400),1,(1/16)])) := by decide +kernel
#print axioms leaf00260_transform
theorem leaf00260_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00260=true := by decide +kernel
#print axioms leaf00260_sign
theorem leaf00260_log : RationalLog.accepts (1196973/2147483648) (-16089497999/4294967296) 11 8=true := by decide +kernel
#print axioms leaf00260_log
def leaf00260 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (94088781063/200000000000) (1196973/2147483648) (-16089497999/4294967296) 11 8 ![60,0,4] ![(9/1600),0,0] ![(1/6400),1,(1/16)] affine00260
theorem leaf00260_checked : FastNestedCellData.accepts 1 2 4 leaf00260=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (94088781063/200000000000) (1196973/2147483648) (-16089497999/4294967296) 11 8 ![60,0,4] ![(9/1600),0,0] ![(1/6400),1,(1/16)] 9642398135980281868054010265600000000000 7902927718563961129598775980420235264 16798873636745949411383705600000000000 raw00260 affine00260
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00260_raw leaf00260_rectangular
    leaf00260_transform leaf00260_sign leaf00260_log
#print axioms leaf00260_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
