/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons17
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0877 : Family 8 := level8.get ⟨45,by decide⟩
def sourceMap0877 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,9,10,11] (sourceLabel 8 0 2 v)
def fusedMap0877 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (fusedLabel 8 0 2 v)
theorem sourceMap0877_checked : acceptsGraphIso
    (source (graph core0877) (root 8) 0 2) DegreeOneSmallSpectrum1225.graph sourceMap0877=true := by decide +kernel
theorem fusedMap0877_checked : acceptsGraphIso
    (fused (graph core0877) (root 8) 0 2) DegreeOneSmallSpectrum881.graph fusedMap0877=true := by decide +kernel
theorem certified0877 : Certified (graph core0877) (root 8) 0 2 :=
  of_native_maps core0877 DegreeOneSmallSpectrum1225.graph DegreeOneSmallSpectrum881.graph
    sourceMap0877 fusedMap0877 sourceMap0877_checked fusedMap0877_checked
    DegreeOneSmallComparisons.comparison0877
#print axioms sourceMap0877_checked
#print axioms fusedMap0877_checked
#print axioms certified0877
def sourceMap0877swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (sourceLabel 8 2 0 v)
def fusedMap0877swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (fusedLabel 8 2 0 v)
theorem sourceMap0877swap_checked : acceptsGraphIso
    (source (graph core0877) (root 8) 2 0) DegreeOneSmallSpectrum1225.graph sourceMap0877swap=true := by decide +kernel
theorem fusedMap0877swap_checked : acceptsGraphIso
    (fused (graph core0877) (root 8) 2 0) DegreeOneSmallSpectrum881.graph fusedMap0877swap=true := by decide +kernel
theorem certified0877swap : Certified (graph core0877) (root 8) 2 0 :=
  of_native_maps core0877 DegreeOneSmallSpectrum1225.graph DegreeOneSmallSpectrum881.graph
    sourceMap0877swap fusedMap0877swap sourceMap0877swap_checked fusedMap0877swap_checked
    DegreeOneSmallComparisons.comparison0877
#print axioms sourceMap0877swap_checked
#print axioms fusedMap0877swap_checked
#print axioms certified0877swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
