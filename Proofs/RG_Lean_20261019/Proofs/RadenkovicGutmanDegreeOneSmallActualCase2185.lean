/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons43
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2185 : Family 10 := level10.get ⟨687,by decide⟩
def sourceMap2185 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,5,6,7,8,9,10,11,12,3,4] (sourceLabel 10 0 0 v)
def fusedMap2185 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap2185_checked : acceptsGraphIso
    (source (graph core2185) (root 10) 0 0) DegreeOneSmallSpectrum1852.graph sourceMap2185=true := by decide +kernel
theorem fusedMap2185_checked : acceptsGraphIso
    (fused (graph core2185) (root 10) 0 0) DegreeOneSmallSpectrum1297.graph fusedMap2185=true := by decide +kernel
theorem certified2185 : Certified (graph core2185) (root 10) 0 0 :=
  of_native_maps core2185 DegreeOneSmallSpectrum1852.graph DegreeOneSmallSpectrum1297.graph
    sourceMap2185 fusedMap2185 sourceMap2185_checked fusedMap2185_checked
    DegreeOneSmallComparisons.comparison2185
#print axioms sourceMap2185_checked
#print axioms fusedMap2185_checked
#print axioms certified2185
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
