/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons48
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2438 : Family 10 := level10.get ⟨1360,by decide⟩
def sourceMap2438 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,9,10,11,12,4,5,6,7,8,2,3] (sourceLabel 10 0 0 v)
def fusedMap2438 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![5,0,1,2,3,4,8,9,10,11,12,6,7] (fusedLabel 10 0 0 v)
theorem sourceMap2438_checked : acceptsGraphIso
    (source (graph core2438) (root 10) 0 0) DegreeOneSmallSpectrum1726.graph sourceMap2438=true := by decide +kernel
theorem fusedMap2438_checked : acceptsGraphIso
    (fused (graph core2438) (root 10) 0 0) DegreeOneSmallSpectrum1969.graph fusedMap2438=true := by decide +kernel
theorem certified2438 : Certified (graph core2438) (root 10) 0 0 :=
  of_native_maps core2438 DegreeOneSmallSpectrum1726.graph DegreeOneSmallSpectrum1969.graph
    sourceMap2438 fusedMap2438 sourceMap2438_checked fusedMap2438_checked
    DegreeOneSmallComparisons.comparison2438
#print axioms sourceMap2438_checked
#print axioms fusedMap2438_checked
#print axioms certified2438
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
