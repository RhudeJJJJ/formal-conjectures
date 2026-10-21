/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons00
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0043 : Family 7 := level7.get ⟨56,by decide⟩
def sourceMap0043 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 1) → Fin 10 :=
  fun v => ![1,0,6,7,8,9,2,3,4,5] (sourceLabel 7 0 0 v)
def fusedMap0043 : (Vertices 7 ⊕ Fin 2) → Fin 10 :=
  fun v => ![1,0,6,7,8,9,2,3,4,5] (fusedLabel 7 0 0 v)
theorem sourceMap0043_checked : acceptsGraphIso
    (source (graph core0043) (root 7) 0 0) DegreeOneSmallSpectrum142.graph sourceMap0043=true := by decide +kernel
theorem fusedMap0043_checked : acceptsGraphIso
    (fused (graph core0043) (root 7) 0 0) DegreeOneSmallSpectrum137.graph fusedMap0043=true := by decide +kernel
theorem certified0043 : Certified (graph core0043) (root 7) 0 0 :=
  of_native_maps core0043 DegreeOneSmallSpectrum142.graph DegreeOneSmallSpectrum137.graph
    sourceMap0043 fusedMap0043 sourceMap0043_checked fusedMap0043_checked
    DegreeTwoThreeFiniteComparisons.comparison0043
#print axioms sourceMap0043_checked
#print axioms fusedMap0043_checked
#print axioms certified0043
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
