/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons30
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1519 : Family 9 := level9.get ⟨252,by decide⟩
def sourceMap1519 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,1,0,6,7,8,9,10,11,5,3,4] (sourceLabel 9 0 0 v)
def fusedMap1519 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![8,7,0,1,2,3,4,5,6,11,9,10] (fusedLabel 9 0 0 v)
theorem sourceMap1519_checked : acceptsGraphIso
    (source (graph core1519) (root 9) 0 0) DegreeOneSmallSpectrum741.graph sourceMap1519=true := by decide +kernel
theorem fusedMap1519_checked : acceptsGraphIso
    (fused (graph core1519) (root 9) 0 0) DegreeOneSmallSpectrum562.graph fusedMap1519=true := by decide +kernel
theorem certified1519 : Certified (graph core1519) (root 9) 0 0 :=
  of_native_maps core1519 DegreeOneSmallSpectrum741.graph DegreeOneSmallSpectrum562.graph
    sourceMap1519 fusedMap1519 sourceMap1519_checked fusedMap1519_checked
    DegreeOneSmallComparisons.comparison1519
#print axioms sourceMap1519_checked
#print axioms fusedMap1519_checked
#print axioms certified1519
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
