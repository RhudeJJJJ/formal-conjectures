/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons23
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1169 : Family 8 := level8.get ⟨209,by decide⟩
def sourceMap1169 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,12,9,10,11] (sourceLabel 8 0 2 v)
def fusedMap1169 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 0 2 v)
theorem sourceMap1169_checked : acceptsGraphIso
    (source (graph core1169) (root 8) 0 2) DegreeOneSmallSpectrum1733.graph sourceMap1169=true := by decide +kernel
theorem fusedMap1169_checked : acceptsGraphIso
    (fused (graph core1169) (root 8) 0 2) DegreeOneSmallSpectrum1089.graph fusedMap1169=true := by decide +kernel
theorem certified1169 : Certified (graph core1169) (root 8) 0 2 :=
  of_native_maps core1169 DegreeOneSmallSpectrum1733.graph DegreeOneSmallSpectrum1089.graph
    sourceMap1169 fusedMap1169 sourceMap1169_checked fusedMap1169_checked
    DegreeOneSmallComparisons.comparison1169
#print axioms sourceMap1169_checked
#print axioms fusedMap1169_checked
#print axioms certified1169
def sourceMap1169swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (sourceLabel 8 2 0 v)
def fusedMap1169swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 2 0 v)
theorem sourceMap1169swap_checked : acceptsGraphIso
    (source (graph core1169) (root 8) 2 0) DegreeOneSmallSpectrum1733.graph sourceMap1169swap=true := by decide +kernel
theorem fusedMap1169swap_checked : acceptsGraphIso
    (fused (graph core1169) (root 8) 2 0) DegreeOneSmallSpectrum1089.graph fusedMap1169swap=true := by decide +kernel
theorem certified1169swap : Certified (graph core1169) (root 8) 2 0 :=
  of_native_maps core1169 DegreeOneSmallSpectrum1733.graph DegreeOneSmallSpectrum1089.graph
    sourceMap1169swap fusedMap1169swap sourceMap1169swap_checked fusedMap1169swap_checked
    DegreeOneSmallComparisons.comparison1169
#print axioms sourceMap1169swap_checked
#print axioms fusedMap1169swap_checked
#print axioms certified1169swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
