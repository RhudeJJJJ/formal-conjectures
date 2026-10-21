/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons41
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2070 : Family 10 := level10.get ⟨451,by decide⟩
def sourceMap2070 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,9,10,11,12,7,8,5,6,3,4] (sourceLabel 10 0 0 v)
def fusedMap2070 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,5,6,3,4] (fusedLabel 10 0 0 v)
theorem sourceMap2070_checked : acceptsGraphIso
    (source (graph core2070) (root 10) 0 0) DegreeOneSmallSpectrum1120.graph sourceMap2070=true := by decide +kernel
theorem fusedMap2070_checked : acceptsGraphIso
    (fused (graph core2070) (root 10) 0 0) DegreeOneSmallSpectrum1501.graph fusedMap2070=true := by decide +kernel
theorem certified2070 : Certified (graph core2070) (root 10) 0 0 :=
  of_native_maps core2070 DegreeOneSmallSpectrum1120.graph DegreeOneSmallSpectrum1501.graph
    sourceMap2070 fusedMap2070 sourceMap2070_checked fusedMap2070_checked
    DegreeOneSmallComparisons.comparison2070
#print axioms sourceMap2070_checked
#print axioms fusedMap2070_checked
#print axioms certified2070
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
