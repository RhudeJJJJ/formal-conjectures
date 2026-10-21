/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons45
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2274 : Family 10 := level10.get ⟨865,by decide⟩
def sourceMap2274 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,8,9,10,11,12,5,6,7,3,4] (sourceLabel 10 0 0 v)
def fusedMap2274 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,7,8,9,10,11,12,4,5,6,2,3] (fusedLabel 10 0 0 v)
theorem sourceMap2274_checked : acceptsGraphIso
    (source (graph core2274) (root 10) 0 0) DegreeOneSmallSpectrum1753.graph sourceMap2274=true := by decide +kernel
theorem fusedMap2274_checked : acceptsGraphIso
    (fused (graph core2274) (root 10) 0 0) DegreeOneSmallSpectrum1482.graph fusedMap2274=true := by decide +kernel
theorem certified2274 : Certified (graph core2274) (root 10) 0 0 :=
  of_native_maps core2274 DegreeOneSmallSpectrum1753.graph DegreeOneSmallSpectrum1482.graph
    sourceMap2274 fusedMap2274 sourceMap2274_checked fusedMap2274_checked
    DegreeOneSmallComparisons.comparison2274
#print axioms sourceMap2274_checked
#print axioms fusedMap2274_checked
#print axioms certified2274
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
