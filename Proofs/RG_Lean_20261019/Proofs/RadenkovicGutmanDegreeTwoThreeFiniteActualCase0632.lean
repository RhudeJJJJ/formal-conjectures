/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons12
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0632 : Family 10 := level10.get ⟨786,by decide⟩
def sourceMap0632 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,6,7,8,9,10,11,12,2,3,4,5] (sourceLabel 10 0 0 v)
def fusedMap0632 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,6,7,8,9,10,11,12,2,3,4,5] (fusedLabel 10 0 0 v)
theorem sourceMap0632_checked : acceptsGraphIso
    (source (graph core0632) (root 10) 0 0) DegreeOneSmallSpectrum1382.graph sourceMap0632=true := by decide +kernel
theorem fusedMap0632_checked : acceptsGraphIso
    (fused (graph core0632) (root 10) 0 0) DegreeOneSmallSpectrum1337.graph fusedMap0632=true := by decide +kernel
theorem certified0632 : Certified (graph core0632) (root 10) 0 0 :=
  of_native_maps core0632 DegreeOneSmallSpectrum1382.graph DegreeOneSmallSpectrum1337.graph
    sourceMap0632 fusedMap0632 sourceMap0632_checked fusedMap0632_checked
    DegreeTwoThreeFiniteComparisons.comparison0632
#print axioms sourceMap0632_checked
#print axioms fusedMap0632_checked
#print axioms certified0632
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
