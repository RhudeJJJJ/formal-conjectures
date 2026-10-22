/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons12
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0635 : Family 10 := level10.get ⟨794,by decide⟩
def sourceMap0635 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,7,8,9,10,11,12,6,2,3,4,5] (sourceLabel 10 0 0 v)
def fusedMap0635 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,7,8,9,10,11,12,6,2,3,4,5] (fusedLabel 10 0 0 v)
theorem sourceMap0635_checked : acceptsGraphIso
    (source (graph core0635) (root 10) 0 0) DegreeOneSmallSpectrum1375.graph sourceMap0635=true := by decide +kernel
theorem fusedMap0635_checked : acceptsGraphIso
    (fused (graph core0635) (root 10) 0 0) DegreeOneSmallSpectrum1326.graph fusedMap0635=true := by decide +kernel
theorem certified0635 : Certified (graph core0635) (root 10) 0 0 :=
  of_native_maps core0635 DegreeOneSmallSpectrum1375.graph DegreeOneSmallSpectrum1326.graph
    sourceMap0635 fusedMap0635 sourceMap0635_checked fusedMap0635_checked
    DegreeTwoThreeFiniteComparisons.comparison0635
#print axioms sourceMap0635_checked
#print axioms fusedMap0635_checked
#print axioms certified0635
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
