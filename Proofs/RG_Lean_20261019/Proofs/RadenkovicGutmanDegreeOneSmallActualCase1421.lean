/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons28
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1421 : Family 9 := level9.get ⟨162,by decide⟩
def sourceMap1421 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![8,7,0,1,2,3,4,5,6,11,9,10] (sourceLabel 9 0 0 v)
def fusedMap1421 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11] (fusedLabel 9 0 0 v)
theorem sourceMap1421_checked : acceptsGraphIso
    (source (graph core1421) (root 9) 0 0) DegreeOneSmallSpectrum721.graph sourceMap1421=true := by decide +kernel
theorem fusedMap1421_checked : acceptsGraphIso
    (fused (graph core1421) (root 9) 0 0) DegreeOneSmallSpectrum436.graph fusedMap1421=true := by decide +kernel
theorem certified1421 : Certified (graph core1421) (root 9) 0 0 :=
  of_native_maps core1421 DegreeOneSmallSpectrum721.graph DegreeOneSmallSpectrum436.graph
    sourceMap1421 fusedMap1421 sourceMap1421_checked fusedMap1421_checked
    DegreeOneSmallComparisons.comparison1421
#print axioms sourceMap1421_checked
#print axioms fusedMap1421_checked
#print axioms certified1421
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
