/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons27
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1359 : Family 9 := level9.get ⟨108,by decide⟩
def sourceMap1359 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,1,0,7,8,9,10,11,5,6,3,4] (sourceLabel 9 0 0 v)
def fusedMap1359 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![2,1,0,7,8,9,10,11,5,6,3,4] (fusedLabel 9 0 0 v)
theorem sourceMap1359_checked : acceptsGraphIso
    (source (graph core1359) (root 9) 0 0) DegreeOneSmallSpectrum439.graph sourceMap1359=true := by decide +kernel
theorem fusedMap1359_checked : acceptsGraphIso
    (fused (graph core1359) (root 9) 0 0) DegreeOneSmallSpectrum580.graph fusedMap1359=true := by decide +kernel
theorem certified1359 : Certified (graph core1359) (root 9) 0 0 :=
  of_native_maps core1359 DegreeOneSmallSpectrum439.graph DegreeOneSmallSpectrum580.graph
    sourceMap1359 fusedMap1359 sourceMap1359_checked fusedMap1359_checked
    DegreeOneSmallComparisons.comparison1359
#print axioms sourceMap1359_checked
#print axioms fusedMap1359_checked
#print axioms certified1359
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
