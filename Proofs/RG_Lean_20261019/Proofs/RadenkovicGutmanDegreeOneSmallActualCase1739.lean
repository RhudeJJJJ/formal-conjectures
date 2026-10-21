/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons34
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1739 : Family 9 := level9.get ⟨562,by decide⟩
def sourceMap1739 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![5,0,1,2,3,4,8,9,10,11,6,7] (sourceLabel 9 0 0 v)
def fusedMap1739 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11] (fusedLabel 9 0 0 v)
theorem sourceMap1739_checked : acceptsGraphIso
    (source (graph core1739) (root 9) 0 0) DegreeOneSmallSpectrum843.graph sourceMap1739=true := by decide +kernel
theorem fusedMap1739_checked : acceptsGraphIso
    (fused (graph core1739) (root 9) 0 0) DegreeOneSmallSpectrum627.graph fusedMap1739=true := by decide +kernel
theorem certified1739 : Certified (graph core1739) (root 9) 0 0 :=
  of_native_maps core1739 DegreeOneSmallSpectrum843.graph DegreeOneSmallSpectrum627.graph
    sourceMap1739 fusedMap1739 sourceMap1739_checked fusedMap1739_checked
    DegreeOneSmallComparisons.comparison1739
#print axioms sourceMap1739_checked
#print axioms fusedMap1739_checked
#print axioms certified1739
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
