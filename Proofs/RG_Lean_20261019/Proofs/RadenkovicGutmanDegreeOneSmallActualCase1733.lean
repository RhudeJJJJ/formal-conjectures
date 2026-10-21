/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons34
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1733 : Family 9 := level9.get ⟨551,by decide⟩
def sourceMap1733 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![6,0,1,2,3,4,5,9,10,11,7,8] (sourceLabel 9 0 0 v)
def fusedMap1733 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11] (fusedLabel 9 0 0 v)
theorem sourceMap1733_checked : acceptsGraphIso
    (source (graph core1733) (root 9) 0 0) DegreeOneSmallSpectrum840.graph sourceMap1733=true := by decide +kernel
theorem fusedMap1733_checked : acceptsGraphIso
    (fused (graph core1733) (root 9) 0 0) DegreeOneSmallSpectrum605.graph fusedMap1733=true := by decide +kernel
theorem certified1733 : Certified (graph core1733) (root 9) 0 0 :=
  of_native_maps core1733 DegreeOneSmallSpectrum840.graph DegreeOneSmallSpectrum605.graph
    sourceMap1733 fusedMap1733 sourceMap1733_checked fusedMap1733_checked
    DegreeOneSmallComparisons.comparison1733
#print axioms sourceMap1733_checked
#print axioms fusedMap1733_checked
#print axioms certified1733
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
