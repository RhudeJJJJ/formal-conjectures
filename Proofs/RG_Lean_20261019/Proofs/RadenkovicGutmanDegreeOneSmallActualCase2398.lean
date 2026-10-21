/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons47
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2398 : Family 10 := level10.get ⟨1242,by decide⟩
def sourceMap2398 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,5,6,7,8,9,10,11,12,4,2,3] (sourceLabel 10 0 0 v)
def fusedMap2398 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap2398_checked : acceptsGraphIso
    (source (graph core2398) (root 10) 0 0) DegreeOneSmallSpectrum1817.graph sourceMap2398=true := by decide +kernel
theorem fusedMap2398_checked : acceptsGraphIso
    (fused (graph core2398) (root 10) 0 0) DegreeOneSmallSpectrum1893.graph fusedMap2398=true := by decide +kernel
theorem certified2398 : Certified (graph core2398) (root 10) 0 0 :=
  of_native_maps core2398 DegreeOneSmallSpectrum1817.graph DegreeOneSmallSpectrum1893.graph
    sourceMap2398 fusedMap2398 sourceMap2398_checked fusedMap2398_checked
    DegreeOneSmallComparisons.comparison2398
#print axioms sourceMap2398_checked
#print axioms fusedMap2398_checked
#print axioms certified2398
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
