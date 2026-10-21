/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons33
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1687 : Family 9 := level9.get ⟨448,by decide⟩
def sourceMap1687 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,0,7,8,9,10,11,4,5,6,2,3] (sourceLabel 9 0 0 v)
def fusedMap1687 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![6,0,1,2,3,4,5,9,10,11,7,8] (fusedLabel 9 0 0 v)
theorem sourceMap1687_checked : acceptsGraphIso
    (source (graph core1687) (root 9) 0 0) DegreeOneSmallSpectrum695.graph sourceMap1687=true := by decide +kernel
theorem fusedMap1687_checked : acceptsGraphIso
    (fused (graph core1687) (root 9) 0 0) DegreeOneSmallSpectrum810.graph fusedMap1687=true := by decide +kernel
theorem certified1687 : Certified (graph core1687) (root 9) 0 0 :=
  of_native_maps core1687 DegreeOneSmallSpectrum695.graph DegreeOneSmallSpectrum810.graph
    sourceMap1687 fusedMap1687 sourceMap1687_checked fusedMap1687_checked
    DegreeOneSmallComparisons.comparison1687
#print axioms sourceMap1687_checked
#print axioms fusedMap1687_checked
#print axioms certified1687
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
