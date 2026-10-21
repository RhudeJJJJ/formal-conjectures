/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons24
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1245 : Family 9 := level9.get ⟨29,by decide⟩
def sourceMap1245 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![3,2,1,0,6,7,8,9,10,11,4,5] (sourceLabel 9 0 0 v)
def fusedMap1245 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![9,8,7,0,1,2,3,4,5,6,10,11] (fusedLabel 9 0 0 v)
theorem sourceMap1245_checked : acceptsGraphIso
    (source (graph core1245) (root 9) 0 0) DegreeOneSmallSpectrum498.graph sourceMap1245=true := by decide +kernel
theorem fusedMap1245_checked : acceptsGraphIso
    (fused (graph core1245) (root 9) 0 0) DegreeOneSmallSpectrum393.graph fusedMap1245=true := by decide +kernel
theorem certified1245 : Certified (graph core1245) (root 9) 0 0 :=
  of_native_maps core1245 DegreeOneSmallSpectrum498.graph DegreeOneSmallSpectrum393.graph
    sourceMap1245 fusedMap1245 sourceMap1245_checked fusedMap1245_checked
    DegreeOneSmallComparisons.comparison1245
#print axioms sourceMap1245_checked
#print axioms fusedMap1245_checked
#print axioms certified1245
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
