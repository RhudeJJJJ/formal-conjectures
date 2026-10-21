/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons48
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2429 : Family 10 := level10.get ⟨1324,by decide⟩
def sourceMap2429 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,8,9,10,11,12,4,5,6,7,2,3] (sourceLabel 10 0 0 v)
def fusedMap2429 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,9,10,11,12,7,8] (fusedLabel 10 0 0 v)
theorem sourceMap2429_checked : acceptsGraphIso
    (source (graph core2429) (root 10) 0 0) DegreeOneSmallSpectrum1741.graph sourceMap2429=true := by decide +kernel
theorem fusedMap2429_checked : acceptsGraphIso
    (fused (graph core2429) (root 10) 0 0) DegreeOneSmallSpectrum1954.graph fusedMap2429=true := by decide +kernel
theorem certified2429 : Certified (graph core2429) (root 10) 0 0 :=
  of_native_maps core2429 DegreeOneSmallSpectrum1741.graph DegreeOneSmallSpectrum1954.graph
    sourceMap2429 fusedMap2429 sourceMap2429_checked fusedMap2429_checked
    DegreeOneSmallComparisons.comparison2429
#print axioms sourceMap2429_checked
#print axioms fusedMap2429_checked
#print axioms certified2429
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
