/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons48
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2415 : Family 10 := level10.get ⟨1280,by decide⟩
def sourceMap2415 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,8,9,10,11,12,4,5,6,7,2,3] (sourceLabel 10 0 0 v)
def fusedMap2415 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,9,10,11,12,7,8] (fusedLabel 10 0 0 v)
theorem sourceMap2415_checked : acceptsGraphIso
    (source (graph core2415) (root 10) 0 0) DegreeOneSmallSpectrum1780.graph sourceMap2415=true := by decide +kernel
theorem fusedMap2415_checked : acceptsGraphIso
    (fused (graph core2415) (root 10) 0 0) DegreeOneSmallSpectrum1931.graph fusedMap2415=true := by decide +kernel
theorem certified2415 : Certified (graph core2415) (root 10) 0 0 :=
  of_native_maps core2415 DegreeOneSmallSpectrum1780.graph DegreeOneSmallSpectrum1931.graph
    sourceMap2415 fusedMap2415 sourceMap2415_checked fusedMap2415_checked
    DegreeOneSmallComparisons.comparison2415
#print axioms sourceMap2415_checked
#print axioms fusedMap2415_checked
#print axioms certified2415
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
