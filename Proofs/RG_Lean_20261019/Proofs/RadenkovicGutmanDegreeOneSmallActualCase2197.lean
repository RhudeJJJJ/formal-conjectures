/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons43
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2197 : Family 10 := level10.get ⟨705,by decide⟩
def sourceMap2197 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,5,6,7,8,9,10,11,12,3,4] (sourceLabel 10 0 0 v)
def fusedMap2197 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap2197_checked : acceptsGraphIso
    (source (graph core2197) (root 10) 0 0) DegreeOneSmallSpectrum1859.graph sourceMap2197=true := by decide +kernel
theorem fusedMap2197_checked : acceptsGraphIso
    (fused (graph core2197) (root 10) 0 0) DegreeOneSmallSpectrum1320.graph fusedMap2197=true := by decide +kernel
theorem certified2197 : Certified (graph core2197) (root 10) 0 0 :=
  of_native_maps core2197 DegreeOneSmallSpectrum1859.graph DegreeOneSmallSpectrum1320.graph
    sourceMap2197 fusedMap2197 sourceMap2197_checked fusedMap2197_checked
    DegreeOneSmallComparisons.comparison2197
#print axioms sourceMap2197_checked
#print axioms fusedMap2197_checked
#print axioms certified2197
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
