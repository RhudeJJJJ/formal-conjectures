/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons27
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1354 : Family 9 := level9.get ⟨104,by decide⟩
def sourceMap1354 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,6,7,8,9,10,11,12,5,3,4] (sourceLabel 9 0 1 v)
def fusedMap1354 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11,12] (fusedLabel 9 0 1 v)
theorem sourceMap1354_checked : acceptsGraphIso
    (source (graph core1354) (root 9) 0 1) DegreeOneSmallSpectrum1451.graph sourceMap1354=true := by decide +kernel
theorem fusedMap1354_checked : acceptsGraphIso
    (fused (graph core1354) (root 9) 0 1) DegreeOneSmallSpectrum958.graph fusedMap1354=true := by decide +kernel
theorem certified1354 : Certified (graph core1354) (root 9) 0 1 :=
  of_native_maps core1354 DegreeOneSmallSpectrum1451.graph DegreeOneSmallSpectrum958.graph
    sourceMap1354 fusedMap1354 sourceMap1354_checked fusedMap1354_checked
    DegreeOneSmallComparisons.comparison1354
#print axioms sourceMap1354_checked
#print axioms fusedMap1354_checked
#print axioms certified1354
def sourceMap1354swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,6,7,8,9,10,11,12,3,4,5] (sourceLabel 9 1 0 v)
def fusedMap1354swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11,12] (fusedLabel 9 1 0 v)
theorem sourceMap1354swap_checked : acceptsGraphIso
    (source (graph core1354) (root 9) 1 0) DegreeOneSmallSpectrum1451.graph sourceMap1354swap=true := by decide +kernel
theorem fusedMap1354swap_checked : acceptsGraphIso
    (fused (graph core1354) (root 9) 1 0) DegreeOneSmallSpectrum958.graph fusedMap1354swap=true := by decide +kernel
theorem certified1354swap : Certified (graph core1354) (root 9) 1 0 :=
  of_native_maps core1354 DegreeOneSmallSpectrum1451.graph DegreeOneSmallSpectrum958.graph
    sourceMap1354swap fusedMap1354swap sourceMap1354swap_checked fusedMap1354swap_checked
    DegreeOneSmallComparisons.comparison1354
#print axioms sourceMap1354swap_checked
#print axioms fusedMap1354swap_checked
#print axioms certified1354swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
