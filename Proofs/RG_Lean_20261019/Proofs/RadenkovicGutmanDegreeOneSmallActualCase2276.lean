/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons45
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2276 : Family 10 := level10.get ⟨875,by decide⟩
def sourceMap2276 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,5,6,7,8,9,10,11,12,3,4] (sourceLabel 10 0 0 v)
def fusedMap2276 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap2276_checked : acceptsGraphIso
    (source (graph core2276) (root 10) 0 0) DegreeOneSmallSpectrum1884.graph sourceMap2276=true := by decide +kernel
theorem fusedMap2276_checked : acceptsGraphIso
    (fused (graph core2276) (root 10) 0 0) DegreeOneSmallSpectrum1492.graph fusedMap2276=true := by decide +kernel
theorem certified2276 : Certified (graph core2276) (root 10) 0 0 :=
  of_native_maps core2276 DegreeOneSmallSpectrum1884.graph DegreeOneSmallSpectrum1492.graph
    sourceMap2276 fusedMap2276 sourceMap2276_checked fusedMap2276_checked
    DegreeOneSmallComparisons.comparison2276
#print axioms sourceMap2276_checked
#print axioms fusedMap2276_checked
#print axioms certified2276
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
