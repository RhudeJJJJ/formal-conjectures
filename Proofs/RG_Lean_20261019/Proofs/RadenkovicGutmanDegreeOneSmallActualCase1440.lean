/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons28
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1440 : Family 9 := level9.get ⟨176,by decide⟩
def sourceMap1440 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,12,10,11] (sourceLabel 9 0 1 v)
def fusedMap1440 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 0 1 v)
theorem sourceMap1440_checked : acceptsGraphIso
    (source (graph core1440) (root 9) 0 1) DegreeOneSmallSpectrum1199.graph sourceMap1440=true := by decide +kernel
theorem fusedMap1440_checked : acceptsGraphIso
    (fused (graph core1440) (root 9) 0 1) DegreeOneSmallSpectrum1201.graph fusedMap1440=true := by decide +kernel
theorem certified1440 : Certified (graph core1440) (root 9) 0 1 :=
  of_native_maps core1440 DegreeOneSmallSpectrum1199.graph DegreeOneSmallSpectrum1201.graph
    sourceMap1440 fusedMap1440 sourceMap1440_checked fusedMap1440_checked
    DegreeOneSmallComparisons.comparison1440
#print axioms sourceMap1440_checked
#print axioms fusedMap1440_checked
#print axioms certified1440
def sourceMap1440swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11,12] (sourceLabel 9 1 0 v)
def fusedMap1440swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 1 0 v)
theorem sourceMap1440swap_checked : acceptsGraphIso
    (source (graph core1440) (root 9) 1 0) DegreeOneSmallSpectrum1199.graph sourceMap1440swap=true := by decide +kernel
theorem fusedMap1440swap_checked : acceptsGraphIso
    (fused (graph core1440) (root 9) 1 0) DegreeOneSmallSpectrum1201.graph fusedMap1440swap=true := by decide +kernel
theorem certified1440swap : Certified (graph core1440) (root 9) 1 0 :=
  of_native_maps core1440 DegreeOneSmallSpectrum1199.graph DegreeOneSmallSpectrum1201.graph
    sourceMap1440swap fusedMap1440swap sourceMap1440swap_checked fusedMap1440swap_checked
    DegreeOneSmallComparisons.comparison1440
#print axioms sourceMap1440swap_checked
#print axioms fusedMap1440swap_checked
#print axioms certified1440swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
