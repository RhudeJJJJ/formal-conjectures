/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01088 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 4796252618916675705475432448000000000000 5225577128034558167215028457586569510912 19626912155371666407105232896000000000000))
theorem leaf01088_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 4796252618916675705475432448000000000000 5225577128034558167215028457586569510912 19626912155371666407105232896000000000000 raw01088=true := by decide +kernel
#print axioms leaf01088_raw
theorem leaf01088_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01088=true := by decide +kernel
#print axioms leaf01088_rectangular
def affine01088 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01088 (IntegerComputedClassCell.leftNumerator ![(17/40),0,(1/4)] ![(3/80),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(17/40),0,(1/4)] ![(3/80),1,(1/4)]) (IntegerComputedClassCell.denominator ![(17/40),0,(1/4)] ![(3/80),1,(1/4)]))
theorem leaf01088_transform : affine01088=(NestedInteger.clearedAll 3 raw01088 (IntegerComputedClassCell.leftNumerator ![(17/40),0,(1/4)] ![(3/80),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(17/40),0,(1/4)] ![(3/80),1,(1/4)]) (IntegerComputedClassCell.denominator ![(17/40),0,(1/4)] ![(3/80),1,(1/4)])) := by decide +kernel
#print axioms leaf01088_transform
theorem leaf01088_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01088=true := by decide +kernel
#print axioms leaf01088_sign
theorem leaf01088_log : RationalLog.accepts (923877023/1073741824) (-161411211/2147483648) 1 8=true := by decide +kernel
#print axioms leaf01088_log
def leaf01088 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (33280688059/125000000000) (923877023/1073741824) (-161411211/2147483648) 1 8 ![60,0,4] ![(17/40),0,(1/4)] ![(3/80),1,(1/4)] affine01088
theorem leaf01088_checked : FastNestedCellData.accepts 1 2 4 leaf01088=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (33280688059/125000000000) (923877023/1073741824) (-161411211/2147483648) 1 8 ![60,0,4] ![(17/40),0,(1/4)] ![(3/80),1,(1/4)] 4796252618916675705475432448000000000000 5225577128034558167215028457586569510912 19626912155371666407105232896000000000000 raw01088 affine01088
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01088_raw leaf01088_rectangular
    leaf01088_transform leaf01088_sign leaf01088_log
#print axioms leaf01088_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
