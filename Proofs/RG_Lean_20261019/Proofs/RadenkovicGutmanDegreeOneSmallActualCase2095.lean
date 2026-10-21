/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons41
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2095 : Family 10 := level10.get ⟨511,by decide⟩
def sourceMap2095 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,11,12,9,10] (sourceLabel 10 0 0 v)
def fusedMap2095 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,11,12,9,10] (fusedLabel 10 0 0 v)
theorem sourceMap2095_checked : acceptsGraphIso
    (source (graph core2095) (root 10) 0 0) DegreeOneSmallSpectrum1588.graph sourceMap2095=true := by decide +kernel
theorem fusedMap2095_checked : acceptsGraphIso
    (fused (graph core2095) (root 10) 0 0) DegreeOneSmallSpectrum1005.graph fusedMap2095=true := by decide +kernel
theorem certified2095 : Certified (graph core2095) (root 10) 0 0 :=
  of_native_maps core2095 DegreeOneSmallSpectrum1588.graph DegreeOneSmallSpectrum1005.graph
    sourceMap2095 fusedMap2095 sourceMap2095_checked fusedMap2095_checked
    DegreeOneSmallComparisons.comparison2095
#print axioms sourceMap2095_checked
#print axioms fusedMap2095_checked
#print axioms certified2095
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
