/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons34
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1747 : Family 9 := level9.get ⟨585,by decide⟩
def sourceMap1747 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,0,4,5,6,7,8,9,10,11,2,3] (sourceLabel 9 0 0 v)
def fusedMap1747 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11] (fusedLabel 9 0 0 v)
theorem sourceMap1747_checked : acceptsGraphIso
    (source (graph core1747) (root 9) 0 0) DegreeOneSmallSpectrum847.graph sourceMap1747=true := by decide +kernel
theorem fusedMap1747_checked : acceptsGraphIso
    (fused (graph core1747) (root 9) 0 0) DegreeOneSmallSpectrum673.graph fusedMap1747=true := by decide +kernel
theorem certified1747 : Certified (graph core1747) (root 9) 0 0 :=
  of_native_maps core1747 DegreeOneSmallSpectrum847.graph DegreeOneSmallSpectrum673.graph
    sourceMap1747 fusedMap1747 sourceMap1747_checked fusedMap1747_checked
    DegreeOneSmallComparisons.comparison1747
#print axioms sourceMap1747_checked
#print axioms fusedMap1747_checked
#print axioms certified1747
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
