/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons44
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2249 : Family 10 := level10.get ⟨806,by decide⟩
def sourceMap2249 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,9,10,11,12,5,6,7,8,3,4] (sourceLabel 10 0 0 v)
def fusedMap2249 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![6,5,0,1,2,3,4,9,10,11,12,7,8] (fusedLabel 10 0 0 v)
theorem sourceMap2249_checked : acceptsGraphIso
    (source (graph core2249) (root 10) 0 0) DegreeOneSmallSpectrum1710.graph sourceMap2249=true := by decide +kernel
theorem fusedMap2249_checked : acceptsGraphIso
    (fused (graph core2249) (root 10) 0 0) DegreeOneSmallSpectrum1441.graph fusedMap2249=true := by decide +kernel
theorem certified2249 : Certified (graph core2249) (root 10) 0 0 :=
  of_native_maps core2249 DegreeOneSmallSpectrum1710.graph DegreeOneSmallSpectrum1441.graph
    sourceMap2249 fusedMap2249 sourceMap2249_checked fusedMap2249_checked
    DegreeOneSmallComparisons.comparison2249
#print axioms sourceMap2249_checked
#print axioms fusedMap2249_checked
#print axioms certified2249
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
