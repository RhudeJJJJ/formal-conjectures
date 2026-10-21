/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons27
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1379 : Family 9 := level9.get ⟨126,by decide⟩
def sourceMap1379 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,1,0,8,9,10,11,5,6,7,3,4] (sourceLabel 9 0 0 v)
def fusedMap1379 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![2,1,0,8,9,10,11,5,6,7,3,4] (fusedLabel 9 0 0 v)
theorem sourceMap1379_checked : acceptsGraphIso
    (source (graph core1379) (root 9) 0 0) DegreeOneSmallSpectrum428.graph sourceMap1379=true := by decide +kernel
theorem fusedMap1379_checked : acceptsGraphIso
    (fused (graph core1379) (root 9) 0 0) DegreeOneSmallSpectrum567.graph fusedMap1379=true := by decide +kernel
theorem certified1379 : Certified (graph core1379) (root 9) 0 0 :=
  of_native_maps core1379 DegreeOneSmallSpectrum428.graph DegreeOneSmallSpectrum567.graph
    sourceMap1379 fusedMap1379 sourceMap1379_checked fusedMap1379_checked
    DegreeOneSmallComparisons.comparison1379
#print axioms sourceMap1379_checked
#print axioms fusedMap1379_checked
#print axioms certified1379
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
