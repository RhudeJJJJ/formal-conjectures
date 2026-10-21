/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons32
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1627 : Family 9 := level9.get ⟨369,by decide⟩
def sourceMap1627 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,0,6,7,8,9,10,11,4,5,2,3] (sourceLabel 9 0 0 v)
def fusedMap1627 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,10,11,8,9] (fusedLabel 9 0 0 v)
theorem sourceMap1627_checked : acceptsGraphIso
    (source (graph core1627) (root 9) 0 0) DegreeOneSmallSpectrum699.graph sourceMap1627=true := by decide +kernel
theorem fusedMap1627_checked : acceptsGraphIso
    (fused (graph core1627) (root 9) 0 0) DegreeOneSmallSpectrum727.graph fusedMap1627=true := by decide +kernel
theorem certified1627 : Certified (graph core1627) (root 9) 0 0 :=
  of_native_maps core1627 DegreeOneSmallSpectrum699.graph DegreeOneSmallSpectrum727.graph
    sourceMap1627 fusedMap1627 sourceMap1627_checked fusedMap1627_checked
    DegreeOneSmallComparisons.comparison1627
#print axioms sourceMap1627_checked
#print axioms fusedMap1627_checked
#print axioms certified1627
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
