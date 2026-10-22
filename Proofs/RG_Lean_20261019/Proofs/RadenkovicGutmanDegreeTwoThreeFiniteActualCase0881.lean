/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons17
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0881 : Family 10 := level10.get ⟨1398,by decide⟩
def sourceMap0881 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,9,10,11,12,2,3,4,5,6,7,8] (sourceLabel 10 0 0 v)
def fusedMap0881 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,9,10,11,12,2,3,4,5,6,7,8] (fusedLabel 10 0 0 v)
theorem sourceMap0881_checked : acceptsGraphIso
    (source (graph core0881) (root 10) 0 0) DegreeOneSmallSpectrum1576.graph sourceMap0881=true := by decide +kernel
theorem fusedMap0881_checked : acceptsGraphIso
    (fused (graph core0881) (root 10) 0 0) DegreeOneSmallSpectrum1567.graph fusedMap0881=true := by decide +kernel
theorem certified0881 : Certified (graph core0881) (root 10) 0 0 :=
  of_native_maps core0881 DegreeOneSmallSpectrum1576.graph DegreeOneSmallSpectrum1567.graph
    sourceMap0881 fusedMap0881 sourceMap0881_checked fusedMap0881_checked
    DegreeTwoThreeFiniteComparisons.comparison0881
#print axioms sourceMap0881_checked
#print axioms fusedMap0881_checked
#print axioms certified0881
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
