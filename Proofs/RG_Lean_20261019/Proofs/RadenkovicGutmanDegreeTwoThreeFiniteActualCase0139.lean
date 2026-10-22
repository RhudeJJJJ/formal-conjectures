/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons02
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0139 : Family 8 := level8.get ⟨218,by decide⟩
def sourceMap0139 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (sourceLabel 8 0 0 v)
def fusedMap0139 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (fusedLabel 8 0 0 v)
theorem sourceMap0139_checked : acceptsGraphIso
    (source (graph core0139) (root 8) 0 0) DegreeOneSmallSpectrum300.graph sourceMap0139=true := by decide +kernel
theorem fusedMap0139_checked : acceptsGraphIso
    (fused (graph core0139) (root 8) 0 0) DegreeOneSmallSpectrum299.graph fusedMap0139=true := by decide +kernel
theorem certified0139 : Certified (graph core0139) (root 8) 0 0 :=
  of_native_maps core0139 DegreeOneSmallSpectrum300.graph DegreeOneSmallSpectrum299.graph
    sourceMap0139 fusedMap0139 sourceMap0139_checked fusedMap0139_checked
    DegreeTwoThreeFiniteComparisons.comparison0139
#print axioms sourceMap0139_checked
#print axioms fusedMap0139_checked
#print axioms certified0139
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
