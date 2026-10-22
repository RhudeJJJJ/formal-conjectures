/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons13
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0666 : Family 10 := level10.get ⟨877,by decide⟩
def sourceMap0666 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,6,7,8,9,10,11,12,3,4,5] (sourceLabel 10 0 0 v)
def fusedMap0666 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,5,6,7,8,9,10,11,12,4,2,3] (fusedLabel 10 0 0 v)
theorem sourceMap0666_checked : acceptsGraphIso
    (source (graph core0666) (root 10) 0 0) DegreeOneSmallSpectrum1696.graph sourceMap0666=true := by decide +kernel
theorem fusedMap0666_checked : acceptsGraphIso
    (fused (graph core0666) (root 10) 0 0) DegreeOneSmallSpectrum1447.graph fusedMap0666=true := by decide +kernel
theorem certified0666 : Certified (graph core0666) (root 10) 0 0 :=
  of_native_maps core0666 DegreeOneSmallSpectrum1696.graph DegreeOneSmallSpectrum1447.graph
    sourceMap0666 fusedMap0666 sourceMap0666_checked fusedMap0666_checked
    DegreeTwoThreeFiniteComparisons.comparison0666
#print axioms sourceMap0666_checked
#print axioms fusedMap0666_checked
#print axioms certified0666
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
