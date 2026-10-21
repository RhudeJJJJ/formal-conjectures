/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons48
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2446 : Family 10 := level10.get ⟨1418,by decide⟩
def sourceMap2446 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![6,0,10,11,12,1,2,3,4,5,9,7,8] (sourceLabel 10 0 0 v)
def fusedMap2446 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,4,5,6,7,8,9,10,11,12,2,3] (fusedLabel 10 0 0 v)
theorem sourceMap2446_checked : acceptsGraphIso
    (source (graph core2446) (root 10) 0 0) DegreeOneSmallSpectrum1555.graph sourceMap2446=true := by decide +kernel
theorem fusedMap2446_checked : acceptsGraphIso
    (fused (graph core2446) (root 10) 0 0) DegreeOneSmallSpectrum1977.graph fusedMap2446=true := by decide +kernel
theorem certified2446 : Certified (graph core2446) (root 10) 0 0 :=
  of_native_maps core2446 DegreeOneSmallSpectrum1555.graph DegreeOneSmallSpectrum1977.graph
    sourceMap2446 fusedMap2446 sourceMap2446_checked fusedMap2446_checked
    DegreeOneSmallComparisons.comparison2446
#print axioms sourceMap2446_checked
#print axioms fusedMap2446_checked
#print axioms certified2446
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
