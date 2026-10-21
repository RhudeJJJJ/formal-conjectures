/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons39
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1974 : Family 10 := level10.get ⟨293,by decide⟩
def sourceMap1974 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,6,7,8,9,10,11,12,5,3,4] (sourceLabel 10 0 0 v)
def fusedMap1974 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap1974_checked : acceptsGraphIso
    (source (graph core1974) (root 10) 0 0) DegreeOneSmallSpectrum1165.graph sourceMap1974=true := by decide +kernel
theorem fusedMap1974_checked : acceptsGraphIso
    (fused (graph core1974) (root 10) 0 0) DegreeOneSmallSpectrum1330.graph fusedMap1974=true := by decide +kernel
theorem certified1974 : Certified (graph core1974) (root 10) 0 0 :=
  of_native_maps core1974 DegreeOneSmallSpectrum1165.graph DegreeOneSmallSpectrum1330.graph
    sourceMap1974 fusedMap1974 sourceMap1974_checked fusedMap1974_checked
    DegreeOneSmallComparisons.comparison1974
#print axioms sourceMap1974_checked
#print axioms fusedMap1974_checked
#print axioms certified1974
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
