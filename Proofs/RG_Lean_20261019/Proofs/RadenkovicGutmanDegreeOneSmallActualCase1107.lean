/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons22
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1107 : Family 8 := level8.get ⟨153,by decide⟩
def sourceMap1107 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![1,0,7,8,9,10,4,5,6,2,3] (sourceLabel 8 0 0 v)
def fusedMap1107 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![5,0,1,2,3,4,8,9,10,6,7] (fusedLabel 8 0 0 v)
theorem sourceMap1107_checked : acceptsGraphIso
    (source (graph core1107) (root 8) 0 0) DegreeOneSmallSpectrum284.graph sourceMap1107=true := by decide +kernel
theorem fusedMap1107_checked : acceptsGraphIso
    (fused (graph core1107) (root 8) 0 0) SmallGeFourSpectrum066.graph fusedMap1107=true := by decide +kernel
theorem certified1107 : Certified (graph core1107) (root 8) 0 0 :=
  of_native_maps core1107 DegreeOneSmallSpectrum284.graph SmallGeFourSpectrum066.graph
    sourceMap1107 fusedMap1107 sourceMap1107_checked fusedMap1107_checked
    DegreeOneSmallComparisons.comparison1107
#print axioms sourceMap1107_checked
#print axioms fusedMap1107_checked
#print axioms certified1107
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
