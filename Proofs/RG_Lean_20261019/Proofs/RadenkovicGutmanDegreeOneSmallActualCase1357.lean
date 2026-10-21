/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons27
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1357 : Family 9 := level9.get ⟨107,by decide⟩
def sourceMap1357 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,1,0,7,8,9,10,11,5,6,3,4] (sourceLabel 9 0 0 v)
def fusedMap1357 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![2,1,0,7,8,9,10,11,5,6,3,4] (fusedLabel 9 0 0 v)
theorem sourceMap1357_checked : acceptsGraphIso
    (source (graph core1357) (root 9) 0 0) DegreeOneSmallSpectrum433.graph sourceMap1357=true := by decide +kernel
theorem fusedMap1357_checked : acceptsGraphIso
    (fused (graph core1357) (root 9) 0 0) DegreeOneSmallSpectrum574.graph fusedMap1357=true := by decide +kernel
theorem certified1357 : Certified (graph core1357) (root 9) 0 0 :=
  of_native_maps core1357 DegreeOneSmallSpectrum433.graph DegreeOneSmallSpectrum574.graph
    sourceMap1357 fusedMap1357 sourceMap1357_checked fusedMap1357_checked
    DegreeOneSmallComparisons.comparison1357
#print axioms sourceMap1357_checked
#print axioms fusedMap1357_checked
#print axioms certified1357
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
