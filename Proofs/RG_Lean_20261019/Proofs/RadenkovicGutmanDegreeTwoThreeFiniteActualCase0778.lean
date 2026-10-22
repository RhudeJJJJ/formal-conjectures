/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons15
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0778 : Family 10 := level10.get ⟨1160,by decide⟩
def sourceMap0778 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,11,12,7,8,9,10] (sourceLabel 10 0 0 v)
def fusedMap0778 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,11,12,7,8,9,10] (fusedLabel 10 0 0 v)
theorem sourceMap0778_checked : acceptsGraphIso
    (source (graph core0778) (root 10) 0 0) DegreeOneSmallSpectrum1828.graph sourceMap0778=true := by decide +kernel
theorem fusedMap0778_checked : acceptsGraphIso
    (fused (graph core0778) (root 10) 0 0) DegreeOneSmallSpectrum1823.graph fusedMap0778=true := by decide +kernel
theorem certified0778 : Certified (graph core0778) (root 10) 0 0 :=
  of_native_maps core0778 DegreeOneSmallSpectrum1828.graph DegreeOneSmallSpectrum1823.graph
    sourceMap0778 fusedMap0778 sourceMap0778_checked fusedMap0778_checked
    DegreeTwoThreeFiniteComparisons.comparison0778
#print axioms sourceMap0778_checked
#print axioms fusedMap0778_checked
#print axioms certified0778
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
