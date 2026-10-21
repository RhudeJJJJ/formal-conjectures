/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons00
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0007 : Family 5 := level5.get ⟨10,by decide⟩
def sourceMap0007 : (Vertices 5 ⊕ Fin 1 ⊕ Fin 1) → Fin 8 :=
  fun v => ![1,0,5,6,7,2,3,4] (sourceLabel 5 0 0 v)
def fusedMap0007 : (Vertices 5 ⊕ Fin 2) → Fin 8 :=
  fun v => ![0,4,5,6,7,3,1,2] (fusedLabel 5 0 0 v)
theorem sourceMap0007_checked : acceptsGraphIso
    (source (graph core0007) (root 5) 0 0) DegreeOneSmallSpectrum030.graph sourceMap0007=true := by decide +kernel
theorem fusedMap0007_checked : acceptsGraphIso
    (fused (graph core0007) (root 5) 0 0) DegreeOneSmallSpectrum024.graph fusedMap0007=true := by decide +kernel
theorem certified0007 : Certified (graph core0007) (root 5) 0 0 :=
  of_native_maps core0007 DegreeOneSmallSpectrum030.graph DegreeOneSmallSpectrum024.graph
    sourceMap0007 fusedMap0007 sourceMap0007_checked fusedMap0007_checked
    DegreeTwoThreeFiniteComparisons.comparison0007
#print axioms sourceMap0007_checked
#print axioms fusedMap0007_checked
#print axioms certified0007
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
