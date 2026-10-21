/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons28
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1425 : Family 9 := level9.get ⟨165,by decide⟩
def sourceMap1425 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![7,6,0,1,2,3,4,5,10,11,8,9] (sourceLabel 9 0 0 v)
def fusedMap1425 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11] (fusedLabel 9 0 0 v)
theorem sourceMap1425_checked : acceptsGraphIso
    (source (graph core1425) (root 9) 0 0) DegreeOneSmallSpectrum730.graph sourceMap1425=true := by decide +kernel
theorem fusedMap1425_checked : acceptsGraphIso
    (fused (graph core1425) (root 9) 0 0) DegreeOneSmallSpectrum441.graph fusedMap1425=true := by decide +kernel
theorem certified1425 : Certified (graph core1425) (root 9) 0 0 :=
  of_native_maps core1425 DegreeOneSmallSpectrum730.graph DegreeOneSmallSpectrum441.graph
    sourceMap1425 fusedMap1425 sourceMap1425_checked fusedMap1425_checked
    DegreeOneSmallComparisons.comparison1425
#print axioms sourceMap1425_checked
#print axioms fusedMap1425_checked
#print axioms certified1425
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
