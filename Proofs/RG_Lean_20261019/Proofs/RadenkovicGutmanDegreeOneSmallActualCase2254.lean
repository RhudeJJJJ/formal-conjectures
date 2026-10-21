/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons45
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2254 : Family 10 := level10.get ⟨831,by decide⟩
def sourceMap2254 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,5,6,7,8,9,10,11,12,3,4] (sourceLabel 10 0 0 v)
def fusedMap2254 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap2254_checked : acceptsGraphIso
    (source (graph core2254) (root 10) 0 0) DegreeOneSmallSpectrum1877.graph sourceMap2254=true := by decide +kernel
theorem fusedMap2254_checked : acceptsGraphIso
    (fused (graph core2254) (root 10) 0 0) DegreeOneSmallSpectrum1457.graph fusedMap2254=true := by decide +kernel
theorem certified2254 : Certified (graph core2254) (root 10) 0 0 :=
  of_native_maps core2254 DegreeOneSmallSpectrum1877.graph DegreeOneSmallSpectrum1457.graph
    sourceMap2254 fusedMap2254 sourceMap2254_checked fusedMap2254_checked
    DegreeOneSmallComparisons.comparison2254
#print axioms sourceMap2254_checked
#print axioms fusedMap2254_checked
#print axioms certified2254
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
