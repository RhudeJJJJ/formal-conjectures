/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons32
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1649 : Family 9 := level9.get ⟨393,by decide⟩
def sourceMap1649 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,0,8,9,10,11,4,5,6,7,2,3] (sourceLabel 9 0 0 v)
def fusedMap1649 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![5,0,1,2,3,4,8,9,10,11,6,7] (fusedLabel 9 0 0 v)
theorem sourceMap1649_checked : acceptsGraphIso
    (source (graph core1649) (root 9) 0 0) DegreeOneSmallSpectrum685.graph sourceMap1649=true := by decide +kernel
theorem fusedMap1649_checked : acceptsGraphIso
    (fused (graph core1649) (root 9) 0 0) DegreeOneSmallSpectrum768.graph fusedMap1649=true := by decide +kernel
theorem certified1649 : Certified (graph core1649) (root 9) 0 0 :=
  of_native_maps core1649 DegreeOneSmallSpectrum685.graph DegreeOneSmallSpectrum768.graph
    sourceMap1649 fusedMap1649 sourceMap1649_checked fusedMap1649_checked
    DegreeOneSmallComparisons.comparison1649
#print axioms sourceMap1649_checked
#print axioms fusedMap1649_checked
#print axioms certified1649
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
