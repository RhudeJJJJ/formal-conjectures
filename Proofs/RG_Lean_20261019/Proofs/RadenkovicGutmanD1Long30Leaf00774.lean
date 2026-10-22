/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00774 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 38064862533677289534165876736000000000000 28975114638624628573467701201923339190272 219402032095633610439223410688000000000000))
theorem leaf00774_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 38064862533677289534165876736000000000000 28975114638624628573467701201923339190272 219402032095633610439223410688000000000000 raw00774=true := by decide +kernel
#print axioms leaf00774_raw
theorem leaf00774_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00774=true := by decide +kernel
#print axioms leaf00774_rectangular
def affine00774 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00774 (IntegerComputedClassCell.leftNumerator ![(59/1600),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(59/1600),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(59/1600),0,(1/2)] ![(3/3200),1,(1/2)]))
theorem leaf00774_transform : affine00774=(NestedInteger.clearedAll 3 raw00774 (IntegerComputedClassCell.leftNumerator ![(59/1600),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(59/1600),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(59/1600),0,(1/2)] ![(3/3200),1,(1/2)])) := by decide +kernel
#print axioms leaf00774_transform
theorem leaf00774_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00774=true := by decide +kernel
#print axioms leaf00774_sign
theorem leaf00774_log : RationalLog.accepts (721987667/1073741824) (-213082357/1073741824) 1 8=true := by decide +kernel
#print axioms leaf00774_log
def leaf00774 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (66032010647/500000000000) (721987667/1073741824) (-213082357/1073741824) 1 8 ![60,0,4] ![(59/1600),0,(1/2)] ![(3/3200),1,(1/2)] affine00774
theorem leaf00774_checked : FastNestedCellData.accepts 1 2 4 leaf00774=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (66032010647/500000000000) (721987667/1073741824) (-213082357/1073741824) 1 8 ![60,0,4] ![(59/1600),0,(1/2)] ![(3/3200),1,(1/2)] 38064862533677289534165876736000000000000 28975114638624628573467701201923339190272 219402032095633610439223410688000000000000 raw00774 affine00774
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00774_raw leaf00774_rectangular
    leaf00774_transform leaf00774_sign leaf00774_log
#print axioms leaf00774_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
