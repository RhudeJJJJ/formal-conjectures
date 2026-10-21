/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons43
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2179 : Family 10 := level10.get ⟨661,by decide⟩
def sourceMap2179 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,9,10,11,12,5,6,7,8,3,4] (sourceLabel 10 0 0 v)
def fusedMap2179 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![6,5,0,1,2,3,4,9,10,11,12,7,8] (fusedLabel 10 0 0 v)
theorem sourceMap2179_checked : acceptsGraphIso
    (source (graph core2179) (root 10) 0 0) DegreeOneSmallSpectrum1729.graph sourceMap2179=true := by decide +kernel
theorem fusedMap2179_checked : acceptsGraphIso
    (fused (graph core2179) (root 10) 0 0) DegreeOneSmallSpectrum1279.graph fusedMap2179=true := by decide +kernel
theorem certified2179 : Certified (graph core2179) (root 10) 0 0 :=
  of_native_maps core2179 DegreeOneSmallSpectrum1729.graph DegreeOneSmallSpectrum1279.graph
    sourceMap2179 fusedMap2179 sourceMap2179_checked fusedMap2179_checked
    DegreeOneSmallComparisons.comparison2179
#print axioms sourceMap2179_checked
#print axioms fusedMap2179_checked
#print axioms certified2179
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
