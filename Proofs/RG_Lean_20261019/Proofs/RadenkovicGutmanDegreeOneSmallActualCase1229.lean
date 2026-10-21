/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons24
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1229 : Family 9 := level9.get ⟨19,by decide⟩
def sourceMap1229 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![3,2,1,0,6,7,8,9,10,11,4,5] (sourceLabel 9 0 0 v)
def fusedMap1229 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![9,8,7,0,1,2,3,4,5,6,10,11] (fusedLabel 9 0 0 v)
theorem sourceMap1229_checked : acceptsGraphIso
    (source (graph core1229) (root 9) 0 0) DegreeOneSmallSpectrum490.graph sourceMap1229=true := by decide +kernel
theorem fusedMap1229_checked : acceptsGraphIso
    (fused (graph core1229) (root 9) 0 0) DegreeOneSmallSpectrum382.graph fusedMap1229=true := by decide +kernel
theorem certified1229 : Certified (graph core1229) (root 9) 0 0 :=
  of_native_maps core1229 DegreeOneSmallSpectrum490.graph DegreeOneSmallSpectrum382.graph
    sourceMap1229 fusedMap1229 sourceMap1229_checked fusedMap1229_checked
    DegreeOneSmallComparisons.comparison1229
#print axioms sourceMap1229_checked
#print axioms fusedMap1229_checked
#print axioms certified1229
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
