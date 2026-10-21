/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons27
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1360 : Family 9 := level9.get ⟨108,by decide⟩
def sourceMap1360 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,8,9,10,11,12,6,7,5,3,4] (sourceLabel 9 0 1 v)
def fusedMap1360 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![7,6,0,1,2,3,4,5,11,12,8,9,10] (fusedLabel 9 0 1 v)
theorem sourceMap1360_checked : acceptsGraphIso
    (source (graph core1360) (root 9) 0 1) DegreeOneSmallSpectrum1423.graph sourceMap1360=true := by decide +kernel
theorem fusedMap1360_checked : acceptsGraphIso
    (fused (graph core1360) (root 9) 0 1) DegreeOneSmallSpectrum964.graph fusedMap1360=true := by decide +kernel
theorem certified1360 : Certified (graph core1360) (root 9) 0 1 :=
  of_native_maps core1360 DegreeOneSmallSpectrum1423.graph DegreeOneSmallSpectrum964.graph
    sourceMap1360 fusedMap1360 sourceMap1360_checked fusedMap1360_checked
    DegreeOneSmallComparisons.comparison1360
#print axioms sourceMap1360_checked
#print axioms fusedMap1360_checked
#print axioms certified1360
def sourceMap1360swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,8,9,10,11,12,6,7,3,4,5] (sourceLabel 9 1 0 v)
def fusedMap1360swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![7,6,0,1,2,3,4,5,11,12,8,9,10] (fusedLabel 9 1 0 v)
theorem sourceMap1360swap_checked : acceptsGraphIso
    (source (graph core1360) (root 9) 1 0) DegreeOneSmallSpectrum1423.graph sourceMap1360swap=true := by decide +kernel
theorem fusedMap1360swap_checked : acceptsGraphIso
    (fused (graph core1360) (root 9) 1 0) DegreeOneSmallSpectrum964.graph fusedMap1360swap=true := by decide +kernel
theorem certified1360swap : Certified (graph core1360) (root 9) 1 0 :=
  of_native_maps core1360 DegreeOneSmallSpectrum1423.graph DegreeOneSmallSpectrum964.graph
    sourceMap1360swap fusedMap1360swap sourceMap1360swap_checked fusedMap1360swap_checked
    DegreeOneSmallComparisons.comparison1360
#print axioms sourceMap1360swap_checked
#print axioms fusedMap1360swap_checked
#print axioms certified1360swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
