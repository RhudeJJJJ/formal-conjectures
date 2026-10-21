/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons26
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1305 : Family 9 := level9.get ⟨71,by decide⟩
def sourceMap1305 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,1,0,6,7,8,9,10,11,5,3,4] (sourceLabel 9 0 0 v)
def fusedMap1305 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![8,7,0,1,2,3,4,5,6,11,9,10] (fusedLabel 9 0 0 v)
theorem sourceMap1305_checked : acceptsGraphIso
    (source (graph core1305) (root 9) 0 0) DegreeOneSmallSpectrum472.graph sourceMap1305=true := by decide +kernel
theorem fusedMap1305_checked : acceptsGraphIso
    (fused (graph core1305) (root 9) 0 0) DegreeOneSmallSpectrum518.graph fusedMap1305=true := by decide +kernel
theorem certified1305 : Certified (graph core1305) (root 9) 0 0 :=
  of_native_maps core1305 DegreeOneSmallSpectrum472.graph DegreeOneSmallSpectrum518.graph
    sourceMap1305 fusedMap1305 sourceMap1305_checked fusedMap1305_checked
    DegreeOneSmallComparisons.comparison1305
#print axioms sourceMap1305_checked
#print axioms fusedMap1305_checked
#print axioms certified1305
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
