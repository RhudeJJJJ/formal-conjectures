/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons11
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0562 : Family 7 := level7.get ⟨26,by decide⟩
def sourceMap0562 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 2) → Fin 11 :=
  fun v => ![7,0,1,2,3,4,5,6,10,8,9] (sourceLabel 7 0 1 v)
def fusedMap0562 : (Vertices 7 ⊕ Fin 3) → Fin 11 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10] (fusedLabel 7 0 1 v)
theorem sourceMap0562_checked : acceptsGraphIso
    (source (graph core0562) (root 7) 0 1) DegreeOneSmallSpectrum243.graph sourceMap0562=true := by decide +kernel
theorem fusedMap0562_checked : acceptsGraphIso
    (fused (graph core0562) (root 7) 0 1) SmallGeFourSpectrum037.graph fusedMap0562=true := by decide +kernel
theorem certified0562 : Certified (graph core0562) (root 7) 0 1 :=
  of_native_maps core0562 DegreeOneSmallSpectrum243.graph SmallGeFourSpectrum037.graph
    sourceMap0562 fusedMap0562 sourceMap0562_checked fusedMap0562_checked
    DegreeOneSmallComparisons.comparison0562
#print axioms sourceMap0562_checked
#print axioms fusedMap0562_checked
#print axioms certified0562
def sourceMap0562swap : (Vertices 7 ⊕ Fin 2 ⊕ Fin 1) → Fin 11 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10] (sourceLabel 7 1 0 v)
def fusedMap0562swap : (Vertices 7 ⊕ Fin 3) → Fin 11 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10] (fusedLabel 7 1 0 v)
theorem sourceMap0562swap_checked : acceptsGraphIso
    (source (graph core0562) (root 7) 1 0) DegreeOneSmallSpectrum243.graph sourceMap0562swap=true := by decide +kernel
theorem fusedMap0562swap_checked : acceptsGraphIso
    (fused (graph core0562) (root 7) 1 0) SmallGeFourSpectrum037.graph fusedMap0562swap=true := by decide +kernel
theorem certified0562swap : Certified (graph core0562) (root 7) 1 0 :=
  of_native_maps core0562 DegreeOneSmallSpectrum243.graph SmallGeFourSpectrum037.graph
    sourceMap0562swap fusedMap0562swap sourceMap0562swap_checked fusedMap0562swap_checked
    DegreeOneSmallComparisons.comparison0562
#print axioms sourceMap0562swap_checked
#print axioms fusedMap0562swap_checked
#print axioms certified0562swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
