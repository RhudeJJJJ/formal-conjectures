/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons00
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0017 : Family 6 := level6.get ⟨24,by decide⟩
def sourceMap0017 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 1) → Fin 9 :=
  fun v => ![1,0,5,6,7,8,2,3,4] (sourceLabel 6 0 0 v)
def fusedMap0017 : (Vertices 6 ⊕ Fin 2) → Fin 9 :=
  fun v => ![5,0,1,2,3,4,8,6,7] (fusedLabel 6 0 0 v)
theorem sourceMap0017_checked : acceptsGraphIso
    (source (graph core0017) (root 6) 0 0) DegreeOneSmallSpectrum067.graph sourceMap0017=true := by decide +kernel
theorem fusedMap0017_checked : acceptsGraphIso
    (fused (graph core0017) (root 6) 0 0) DegreeOneSmallSpectrum046.graph fusedMap0017=true := by decide +kernel
theorem certified0017 : Certified (graph core0017) (root 6) 0 0 :=
  of_native_maps core0017 DegreeOneSmallSpectrum067.graph DegreeOneSmallSpectrum046.graph
    sourceMap0017 fusedMap0017 sourceMap0017_checked fusedMap0017_checked
    DegreeTwoThreeFiniteComparisons.comparison0017
#print axioms sourceMap0017_checked
#print axioms fusedMap0017_checked
#print axioms certified0017
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
