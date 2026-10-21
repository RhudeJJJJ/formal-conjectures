/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons23
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1165 : Family 8 := level8.get ⟨207,by decide⟩
def sourceMap1165 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,12,9,10,11] (sourceLabel 8 0 2 v)
def fusedMap1165 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 0 2 v)
theorem sourceMap1165_checked : acceptsGraphIso
    (source (graph core1165) (root 8) 0 2) DegreeOneSmallSpectrum1711.graph sourceMap1165=true := by decide +kernel
theorem fusedMap1165_checked : acceptsGraphIso
    (fused (graph core1165) (root 8) 0 2) DegreeOneSmallSpectrum1083.graph fusedMap1165=true := by decide +kernel
theorem certified1165 : Certified (graph core1165) (root 8) 0 2 :=
  of_native_maps core1165 DegreeOneSmallSpectrum1711.graph DegreeOneSmallSpectrum1083.graph
    sourceMap1165 fusedMap1165 sourceMap1165_checked fusedMap1165_checked
    DegreeOneSmallComparisons.comparison1165
#print axioms sourceMap1165_checked
#print axioms fusedMap1165_checked
#print axioms certified1165
def sourceMap1165swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (sourceLabel 8 2 0 v)
def fusedMap1165swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 2 0 v)
theorem sourceMap1165swap_checked : acceptsGraphIso
    (source (graph core1165) (root 8) 2 0) DegreeOneSmallSpectrum1711.graph sourceMap1165swap=true := by decide +kernel
theorem fusedMap1165swap_checked : acceptsGraphIso
    (fused (graph core1165) (root 8) 2 0) DegreeOneSmallSpectrum1083.graph fusedMap1165swap=true := by decide +kernel
theorem certified1165swap : Certified (graph core1165) (root 8) 2 0 :=
  of_native_maps core1165 DegreeOneSmallSpectrum1711.graph DegreeOneSmallSpectrum1083.graph
    sourceMap1165swap fusedMap1165swap sourceMap1165swap_checked fusedMap1165swap_checked
    DegreeOneSmallComparisons.comparison1165
#print axioms sourceMap1165swap_checked
#print axioms fusedMap1165swap_checked
#print axioms certified1165swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
