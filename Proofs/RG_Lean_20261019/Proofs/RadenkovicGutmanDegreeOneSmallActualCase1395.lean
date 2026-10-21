/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons27
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1395 : Family 9 := level9.get ⟨143,by decide⟩
def sourceMap1395 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11] (sourceLabel 9 0 0 v)
def fusedMap1395 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11] (fusedLabel 9 0 0 v)
theorem sourceMap1395_checked : acceptsGraphIso
    (source (graph core1395) (root 9) 0 0) DegreeOneSmallSpectrum646.graph sourceMap1395=true := by decide +kernel
theorem fusedMap1395_checked : acceptsGraphIso
    (fused (graph core1395) (root 9) 0 0) DegreeOneSmallSpectrum406.graph fusedMap1395=true := by decide +kernel
theorem certified1395 : Certified (graph core1395) (root 9) 0 0 :=
  of_native_maps core1395 DegreeOneSmallSpectrum646.graph DegreeOneSmallSpectrum406.graph
    sourceMap1395 fusedMap1395 sourceMap1395_checked fusedMap1395_checked
    DegreeOneSmallComparisons.comparison1395
#print axioms sourceMap1395_checked
#print axioms fusedMap1395_checked
#print axioms certified1395
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
