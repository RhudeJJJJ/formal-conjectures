/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons14
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0731 : Family 7 := level7.get ⟨100,by decide⟩
def sourceMap0731 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 3) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (sourceLabel 7 0 2 v)
def fusedMap0731 : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11] (fusedLabel 7 0 2 v)
theorem sourceMap0731_checked : acceptsGraphIso
    (source (graph core0731) (root 7) 0 2) SmallGeFourSpectrum113.graph sourceMap0731=true := by decide +kernel
theorem fusedMap0731_checked : acceptsGraphIso
    (fused (graph core0731) (root 7) 0 2) SmallGeFourSpectrum116.graph fusedMap0731=true := by decide +kernel
theorem certified0731 : Certified (graph core0731) (root 7) 0 2 :=
  of_native_maps core0731 SmallGeFourSpectrum113.graph SmallGeFourSpectrum116.graph
    sourceMap0731 fusedMap0731 sourceMap0731_checked fusedMap0731_checked
    DegreeOneSmallComparisons.comparison0731
#print axioms sourceMap0731_checked
#print axioms fusedMap0731_checked
#print axioms certified0731
def sourceMap0731swap : (Vertices 7 ⊕ Fin 3 ⊕ Fin 1) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,9,10,11,8] (sourceLabel 7 2 0 v)
def fusedMap0731swap : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11] (fusedLabel 7 2 0 v)
theorem sourceMap0731swap_checked : acceptsGraphIso
    (source (graph core0731) (root 7) 2 0) SmallGeFourSpectrum113.graph sourceMap0731swap=true := by decide +kernel
theorem fusedMap0731swap_checked : acceptsGraphIso
    (fused (graph core0731) (root 7) 2 0) SmallGeFourSpectrum116.graph fusedMap0731swap=true := by decide +kernel
theorem certified0731swap : Certified (graph core0731) (root 7) 2 0 :=
  of_native_maps core0731 SmallGeFourSpectrum113.graph SmallGeFourSpectrum116.graph
    sourceMap0731swap fusedMap0731swap sourceMap0731swap_checked fusedMap0731swap_checked
    DegreeOneSmallComparisons.comparison0731
#print axioms sourceMap0731swap_checked
#print axioms fusedMap0731swap_checked
#print axioms certified0731swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
