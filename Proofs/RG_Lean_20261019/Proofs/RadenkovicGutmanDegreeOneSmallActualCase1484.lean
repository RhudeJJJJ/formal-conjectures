/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons29
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1484 : Family 9 := level9.get ⟨217,by decide⟩
def sourceMap1484 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,12,10,11] (sourceLabel 9 0 1 v)
def fusedMap1484 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 0 1 v)
theorem sourceMap1484_checked : acceptsGraphIso
    (source (graph core1484) (root 9) 0 1) DegreeOneSmallSpectrum1368.graph sourceMap1484=true := by decide +kernel
theorem fusedMap1484_checked : acceptsGraphIso
    (fused (graph core1484) (root 9) 0 1) DegreeOneSmallSpectrum1370.graph fusedMap1484=true := by decide +kernel
theorem certified1484 : Certified (graph core1484) (root 9) 0 1 :=
  of_native_maps core1484 DegreeOneSmallSpectrum1368.graph DegreeOneSmallSpectrum1370.graph
    sourceMap1484 fusedMap1484 sourceMap1484_checked fusedMap1484_checked
    DegreeOneSmallComparisons.comparison1484
#print axioms sourceMap1484_checked
#print axioms fusedMap1484_checked
#print axioms certified1484
def sourceMap1484swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11,12] (sourceLabel 9 1 0 v)
def fusedMap1484swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 1 0 v)
theorem sourceMap1484swap_checked : acceptsGraphIso
    (source (graph core1484) (root 9) 1 0) DegreeOneSmallSpectrum1368.graph sourceMap1484swap=true := by decide +kernel
theorem fusedMap1484swap_checked : acceptsGraphIso
    (fused (graph core1484) (root 9) 1 0) DegreeOneSmallSpectrum1370.graph fusedMap1484swap=true := by decide +kernel
theorem certified1484swap : Certified (graph core1484) (root 9) 1 0 :=
  of_native_maps core1484 DegreeOneSmallSpectrum1368.graph DegreeOneSmallSpectrum1370.graph
    sourceMap1484swap fusedMap1484swap sourceMap1484swap_checked fusedMap1484swap_checked
    DegreeOneSmallComparisons.comparison1484
#print axioms sourceMap1484swap_checked
#print axioms fusedMap1484swap_checked
#print axioms certified1484swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
