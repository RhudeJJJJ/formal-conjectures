/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons43
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2194 : Family 10 := level10.get ⟨701,by decide⟩
def sourceMap2194 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,5,6,7,8,9,10,11,12,3,4] (sourceLabel 10 0 0 v)
def fusedMap2194 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap2194_checked : acceptsGraphIso
    (source (graph core2194) (root 10) 0 0) DegreeOneSmallSpectrum1857.graph sourceMap2194=true := by decide +kernel
theorem fusedMap2194_checked : acceptsGraphIso
    (fused (graph core2194) (root 10) 0 0) DegreeOneSmallSpectrum1315.graph fusedMap2194=true := by decide +kernel
theorem certified2194 : Certified (graph core2194) (root 10) 0 0 :=
  of_native_maps core2194 DegreeOneSmallSpectrum1857.graph DegreeOneSmallSpectrum1315.graph
    sourceMap2194 fusedMap2194 sourceMap2194_checked fusedMap2194_checked
    DegreeOneSmallComparisons.comparison2194
#print axioms sourceMap2194_checked
#print axioms fusedMap2194_checked
#print axioms certified2194
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
