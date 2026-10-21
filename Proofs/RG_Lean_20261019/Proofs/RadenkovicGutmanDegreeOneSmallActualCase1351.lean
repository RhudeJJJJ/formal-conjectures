/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons27
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1351 : Family 9 := level9.get ⟨103,by decide⟩
def sourceMap1351 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,1,0,7,8,9,10,11,5,6,3,4] (sourceLabel 9 0 0 v)
def fusedMap1351 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![7,6,0,1,2,3,4,5,10,11,8,9] (fusedLabel 9 0 0 v)
theorem sourceMap1351_checked : acceptsGraphIso
    (source (graph core1351) (root 9) 0 0) DegreeOneSmallSpectrum463.graph sourceMap1351=true := by decide +kernel
theorem fusedMap1351_checked : acceptsGraphIso
    (fused (graph core1351) (root 9) 0 0) DegreeOneSmallSpectrum583.graph fusedMap1351=true := by decide +kernel
theorem certified1351 : Certified (graph core1351) (root 9) 0 0 :=
  of_native_maps core1351 DegreeOneSmallSpectrum463.graph DegreeOneSmallSpectrum583.graph
    sourceMap1351 fusedMap1351 sourceMap1351_checked fusedMap1351_checked
    DegreeOneSmallComparisons.comparison1351
#print axioms sourceMap1351_checked
#print axioms fusedMap1351_checked
#print axioms certified1351
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
