/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons00
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0025 : Family 6 := level6.get ⟨39,by decide⟩
def sourceMap0025 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 1) → Fin 9 :=
  fun v => ![0,1,2,3,4,5,6,7,8] (sourceLabel 6 0 0 v)
def fusedMap0025 : (Vertices 6 ⊕ Fin 2) → Fin 9 :=
  fun v => ![0,1,2,3,4,5,6,7,8] (fusedLabel 6 0 0 v)
theorem sourceMap0025_checked : acceptsGraphIso
    (source (graph core0025) (root 6) 0 0) DegreeTwoThreeSpectrum064.graph sourceMap0025=true := by decide +kernel
theorem fusedMap0025_checked : acceptsGraphIso
    (fused (graph core0025) (root 6) 0 0) DegreeOneSmallSpectrum068.graph fusedMap0025=true := by decide +kernel
theorem certified0025 : Certified (graph core0025) (root 6) 0 0 :=
  of_native_maps core0025 DegreeTwoThreeSpectrum064.graph DegreeOneSmallSpectrum068.graph
    sourceMap0025 fusedMap0025 sourceMap0025_checked fusedMap0025_checked
    DegreeTwoThreeFiniteComparisons.comparison0025
#print axioms sourceMap0025_checked
#print axioms fusedMap0025_checked
#print axioms certified0025
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
