/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons43
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2162 : Family 10 := level10.get ⟨626,by decide⟩
def sourceMap2162 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,6,7,8,9,10,11,12,5,3,4] (sourceLabel 10 0 0 v)
def fusedMap2162 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap2162_checked : acceptsGraphIso
    (source (graph core2162) (root 10) 0 0) DegreeOneSmallSpectrum1815.graph sourceMap2162=true := by decide +kernel
theorem fusedMap2162_checked : acceptsGraphIso
    (fused (graph core2162) (root 10) 0 0) DegreeOneSmallSpectrum1200.graph fusedMap2162=true := by decide +kernel
theorem certified2162 : Certified (graph core2162) (root 10) 0 0 :=
  of_native_maps core2162 DegreeOneSmallSpectrum1815.graph DegreeOneSmallSpectrum1200.graph
    sourceMap2162 fusedMap2162 sourceMap2162_checked fusedMap2162_checked
    DegreeOneSmallComparisons.comparison2162
#print axioms sourceMap2162_checked
#print axioms fusedMap2162_checked
#print axioms certified2162
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
