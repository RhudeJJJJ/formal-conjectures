/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons44
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2225 : Family 10 := level10.get ⟨763,by decide⟩
def sourceMap2225 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,5,6,7,8,9,10,11,12,3,4] (sourceLabel 10 0 0 v)
def fusedMap2225 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap2225_checked : acceptsGraphIso
    (source (graph core2225) (root 10) 0 0) DegreeOneSmallSpectrum1869.graph sourceMap2225=true := by decide +kernel
theorem fusedMap2225_checked : acceptsGraphIso
    (fused (graph core2225) (root 10) 0 0) DegreeOneSmallSpectrum1394.graph fusedMap2225=true := by decide +kernel
theorem certified2225 : Certified (graph core2225) (root 10) 0 0 :=
  of_native_maps core2225 DegreeOneSmallSpectrum1869.graph DegreeOneSmallSpectrum1394.graph
    sourceMap2225 fusedMap2225 sourceMap2225_checked fusedMap2225_checked
    DegreeOneSmallComparisons.comparison2225
#print axioms sourceMap2225_checked
#print axioms fusedMap2225_checked
#print axioms certified2225
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
