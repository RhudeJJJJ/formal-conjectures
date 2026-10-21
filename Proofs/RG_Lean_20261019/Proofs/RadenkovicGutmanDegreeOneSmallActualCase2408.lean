/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons48
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2408 : Family 10 := level10.get ⟨1261,by decide⟩
def sourceMap2408 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,7,8,9,10,11,12,4,5,6,2,3] (sourceLabel 10 0 0 v)
def fusedMap2408 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,10,11,12,8,9] (fusedLabel 10 0 0 v)
theorem sourceMap2408_checked : acceptsGraphIso
    (source (graph core2408) (root 10) 0 0) DegreeOneSmallSpectrum1787.graph sourceMap2408=true := by decide +kernel
theorem fusedMap2408_checked : acceptsGraphIso
    (fused (graph core2408) (root 10) 0 0) DegreeOneSmallSpectrum1914.graph fusedMap2408=true := by decide +kernel
theorem certified2408 : Certified (graph core2408) (root 10) 0 0 :=
  of_native_maps core2408 DegreeOneSmallSpectrum1787.graph DegreeOneSmallSpectrum1914.graph
    sourceMap2408 fusedMap2408 sourceMap2408_checked fusedMap2408_checked
    DegreeOneSmallComparisons.comparison2408
#print axioms sourceMap2408_checked
#print axioms fusedMap2408_checked
#print axioms certified2408
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
