/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons43
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2188 : Family 10 := level10.get ⟨691,by decide⟩
def sourceMap2188 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,5,6,7,8,9,10,11,12,3,4] (sourceLabel 10 0 0 v)
def fusedMap2188 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap2188_checked : acceptsGraphIso
    (source (graph core2188) (root 10) 0 0) DegreeOneSmallSpectrum1854.graph sourceMap2188=true := by decide +kernel
theorem fusedMap2188_checked : acceptsGraphIso
    (fused (graph core2188) (root 10) 0 0) DegreeOneSmallSpectrum1302.graph fusedMap2188=true := by decide +kernel
theorem certified2188 : Certified (graph core2188) (root 10) 0 0 :=
  of_native_maps core2188 DegreeOneSmallSpectrum1854.graph DegreeOneSmallSpectrum1302.graph
    sourceMap2188 fusedMap2188 sourceMap2188_checked fusedMap2188_checked
    DegreeOneSmallComparisons.comparison2188
#print axioms sourceMap2188_checked
#print axioms fusedMap2188_checked
#print axioms certified2188
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
