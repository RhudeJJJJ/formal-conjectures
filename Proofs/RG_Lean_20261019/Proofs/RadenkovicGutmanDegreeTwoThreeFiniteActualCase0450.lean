/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons09
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0450 : Family 10 := level10.get ⟨230,by decide⟩
def sourceMap0450 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,6,7,8,9,10,11,12,3,4,5] (sourceLabel 10 0 0 v)
def fusedMap0450 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap0450_checked : acceptsGraphIso
    (source (graph core0450) (root 10) 0 0) DegreeOneSmallSpectrum1062.graph sourceMap0450=true := by decide +kernel
theorem fusedMap0450_checked : acceptsGraphIso
    (fused (graph core0450) (root 10) 0 0) DegreeOneSmallSpectrum1154.graph fusedMap0450=true := by decide +kernel
theorem certified0450 : Certified (graph core0450) (root 10) 0 0 :=
  of_native_maps core0450 DegreeOneSmallSpectrum1062.graph DegreeOneSmallSpectrum1154.graph
    sourceMap0450 fusedMap0450 sourceMap0450_checked fusedMap0450_checked
    DegreeTwoThreeFiniteComparisons.comparison0450
#print axioms sourceMap0450_checked
#print axioms fusedMap0450_checked
#print axioms certified0450
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
