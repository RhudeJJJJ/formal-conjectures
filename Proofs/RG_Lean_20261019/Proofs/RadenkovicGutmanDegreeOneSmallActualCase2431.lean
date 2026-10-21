/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons48
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2431 : Family 10 := level10.get ⟨1345,by decide⟩
def sourceMap2431 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,12,10,11] (sourceLabel 10 0 0 v)
def fusedMap2431 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap2431_checked : acceptsGraphIso
    (source (graph core2431) (root 10) 0 0) DegreeOneSmallSpectrum1959.graph sourceMap2431=true := by decide +kernel
theorem fusedMap2431_checked : acceptsGraphIso
    (fused (graph core2431) (root 10) 0 0) DegreeOneSmallSpectrum1957.graph fusedMap2431=true := by decide +kernel
theorem certified2431 : Certified (graph core2431) (root 10) 0 0 :=
  of_native_maps core2431 DegreeOneSmallSpectrum1959.graph DegreeOneSmallSpectrum1957.graph
    sourceMap2431 fusedMap2431 sourceMap2431_checked fusedMap2431_checked
    DegreeOneSmallComparisons.comparison2431
#print axioms sourceMap2431_checked
#print axioms fusedMap2431_checked
#print axioms certified2431
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
