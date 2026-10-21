/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons25
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1291 : Family 9 := level9.get ⟨60,by decide⟩
def sourceMap1291 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,1,0,7,8,9,10,11,5,6,3,4] (sourceLabel 9 0 0 v)
def fusedMap1291 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![7,6,0,1,2,3,4,5,10,11,8,9] (fusedLabel 9 0 0 v)
theorem sourceMap1291_checked : acceptsGraphIso
    (source (graph core1291) (root 9) 0 0) DegreeOneSmallSpectrum461.graph sourceMap1291=true := by decide +kernel
theorem fusedMap1291_checked : acceptsGraphIso
    (fused (graph core1291) (root 9) 0 0) DegreeOneSmallSpectrum498.graph fusedMap1291=true := by decide +kernel
theorem certified1291 : Certified (graph core1291) (root 9) 0 0 :=
  of_native_maps core1291 DegreeOneSmallSpectrum461.graph DegreeOneSmallSpectrum498.graph
    sourceMap1291 fusedMap1291 sourceMap1291_checked fusedMap1291_checked
    DegreeOneSmallComparisons.comparison1291
#print axioms sourceMap1291_checked
#print axioms fusedMap1291_checked
#print axioms certified1291
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
