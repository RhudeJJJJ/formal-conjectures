/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons12
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0629 : Family 10 := level10.get ⟨778,by decide⟩
def sourceMap0629 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,6,7,8,9,10,11,12,2,3,4,5] (sourceLabel 10 0 0 v)
def fusedMap0629 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,6,7,8,9,10,11,12,2,3,4,5] (fusedLabel 10 0 0 v)
theorem sourceMap0629_checked : acceptsGraphIso
    (source (graph core0629) (root 10) 0 0) DegreeOneSmallSpectrum1381.graph sourceMap0629=true := by decide +kernel
theorem fusedMap0629_checked : acceptsGraphIso
    (fused (graph core0629) (root 10) 0 0) DegreeOneSmallSpectrum1336.graph fusedMap0629=true := by decide +kernel
theorem certified0629 : Certified (graph core0629) (root 10) 0 0 :=
  of_native_maps core0629 DegreeOneSmallSpectrum1381.graph DegreeOneSmallSpectrum1336.graph
    sourceMap0629 fusedMap0629 sourceMap0629_checked fusedMap0629_checked
    DegreeTwoThreeFiniteComparisons.comparison0629
#print axioms sourceMap0629_checked
#print axioms fusedMap0629_checked
#print axioms certified0629
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
