/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons41
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2056 : Family 10 := level10.get ⟨430,by decide⟩
def sourceMap2056 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,9,10,11,12,5,6,7,8,3,4] (sourceLabel 10 0 0 v)
def fusedMap2056 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,5,6,7,8,9,10,11,12,3,4] (fusedLabel 10 0 0 v)
theorem sourceMap2056_checked : acceptsGraphIso
    (source (graph core2056) (root 10) 0 0) DegreeOneSmallSpectrum1184.graph sourceMap2056=true := by decide +kernel
theorem fusedMap2056_checked : acceptsGraphIso
    (fused (graph core2056) (root 10) 0 0) DegreeOneSmallSpectrum1510.graph fusedMap2056=true := by decide +kernel
theorem certified2056 : Certified (graph core2056) (root 10) 0 0 :=
  of_native_maps core2056 DegreeOneSmallSpectrum1184.graph DegreeOneSmallSpectrum1510.graph
    sourceMap2056 fusedMap2056 sourceMap2056_checked fusedMap2056_checked
    DegreeOneSmallComparisons.comparison2056
#print axioms sourceMap2056_checked
#print axioms fusedMap2056_checked
#print axioms certified2056
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
