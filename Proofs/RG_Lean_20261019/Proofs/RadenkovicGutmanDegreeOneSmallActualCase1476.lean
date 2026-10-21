/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons29
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1476 : Family 9 := level9.get ⟨209,by decide⟩
def sourceMap1476 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,6,0,1,2,3,4,5,11,12,10,8,9] (sourceLabel 9 0 1 v)
def fusedMap1476 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,8,9,10] (fusedLabel 9 0 1 v)
theorem sourceMap1476_checked : acceptsGraphIso
    (source (graph core1476) (root 9) 0 1) DegreeOneSmallSpectrum1337.graph sourceMap1476=true := by decide +kernel
theorem fusedMap1476_checked : acceptsGraphIso
    (fused (graph core1476) (root 9) 0 1) DegreeOneSmallSpectrum1348.graph fusedMap1476=true := by decide +kernel
theorem certified1476 : Certified (graph core1476) (root 9) 0 1 :=
  of_native_maps core1476 DegreeOneSmallSpectrum1337.graph DegreeOneSmallSpectrum1348.graph
    sourceMap1476 fusedMap1476 sourceMap1476_checked fusedMap1476_checked
    DegreeOneSmallComparisons.comparison1476
#print axioms sourceMap1476_checked
#print axioms fusedMap1476_checked
#print axioms certified1476
def sourceMap1476swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![7,6,0,1,2,3,4,5,11,12,8,9,10] (sourceLabel 9 1 0 v)
def fusedMap1476swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,8,9,10] (fusedLabel 9 1 0 v)
theorem sourceMap1476swap_checked : acceptsGraphIso
    (source (graph core1476) (root 9) 1 0) DegreeOneSmallSpectrum1337.graph sourceMap1476swap=true := by decide +kernel
theorem fusedMap1476swap_checked : acceptsGraphIso
    (fused (graph core1476) (root 9) 1 0) DegreeOneSmallSpectrum1348.graph fusedMap1476swap=true := by decide +kernel
theorem certified1476swap : Certified (graph core1476) (root 9) 1 0 :=
  of_native_maps core1476 DegreeOneSmallSpectrum1337.graph DegreeOneSmallSpectrum1348.graph
    sourceMap1476swap fusedMap1476swap sourceMap1476swap_checked fusedMap1476swap_checked
    DegreeOneSmallComparisons.comparison1476
#print axioms sourceMap1476swap_checked
#print axioms fusedMap1476swap_checked
#print axioms certified1476swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
