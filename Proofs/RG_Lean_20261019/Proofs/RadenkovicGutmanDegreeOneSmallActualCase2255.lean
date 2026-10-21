/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons45
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2255 : Family 10 := level10.get ⟨832,by decide⟩
def sourceMap2255 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,6,7,8,9,10,11,12,5,3,4] (sourceLabel 10 0 0 v)
def fusedMap2255 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap2255_checked : acceptsGraphIso
    (source (graph core2255) (root 10) 0 0) DegreeOneSmallSpectrum1833.graph sourceMap2255=true := by decide +kernel
theorem fusedMap2255_checked : acceptsGraphIso
    (fused (graph core2255) (root 10) 0 0) DegreeOneSmallSpectrum1458.graph fusedMap2255=true := by decide +kernel
theorem certified2255 : Certified (graph core2255) (root 10) 0 0 :=
  of_native_maps core2255 DegreeOneSmallSpectrum1833.graph DegreeOneSmallSpectrum1458.graph
    sourceMap2255 fusedMap2255 sourceMap2255_checked fusedMap2255_checked
    DegreeOneSmallComparisons.comparison2255
#print axioms sourceMap2255_checked
#print axioms fusedMap2255_checked
#print axioms certified2255
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
