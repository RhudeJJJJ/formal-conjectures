/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00488 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 353267209636697908526181043404800000000000 285635964968132891692968761314810236239872 2983041392057270414472588034048000000000000))
theorem leaf00488_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 353267209636697908526181043404800000000000 285635964968132891692968761314810236239872 2983041392057270414472588034048000000000000 raw00488=true := by decide +kernel
#print axioms leaf00488_raw
theorem leaf00488_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00488=true := by decide +kernel
#print axioms leaf00488_rectangular
def affine00488 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00488 (IntegerComputedClassCell.leftNumerator ![(81/6400),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(81/6400),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(81/6400),0,(1/4)] ![(1/6400),1,(1/4)]))
theorem leaf00488_transform : affine00488=(NestedInteger.clearedAll 3 raw00488 (IntegerComputedClassCell.leftNumerator ![(81/6400),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(81/6400),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(81/6400),0,(1/4)] ![(1/6400),1,(1/4)])) := by decide +kernel
#print axioms leaf00488_transform
theorem leaf00488_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00488=true := by decide +kernel
#print axioms leaf00488_sign
theorem leaf00488_log : RationalLog.accepts (3169251085/4294967296) (-40795297/268435456) 1 8=true := by decide +kernel
#print axioms leaf00488_log
def leaf00488 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (95753269039/1000000000000) (3169251085/4294967296) (-40795297/268435456) 1 8 ![60,0,4] ![(81/6400),0,(1/4)] ![(1/6400),1,(1/4)] affine00488
theorem leaf00488_checked : FastNestedCellData.accepts 1 2 4 leaf00488=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (95753269039/1000000000000) (3169251085/4294967296) (-40795297/268435456) 1 8 ![60,0,4] ![(81/6400),0,(1/4)] ![(1/6400),1,(1/4)] 353267209636697908526181043404800000000000 285635964968132891692968761314810236239872 2983041392057270414472588034048000000000000 raw00488 affine00488
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00488_raw leaf00488_rectangular
    leaf00488_transform leaf00488_sign leaf00488_log
#print axioms leaf00488_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
