/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons05
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0256 : Family 9 := level9.get ⟨324,by decide⟩
def sourceMap0256 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![8,7,0,1,2,3,4,5,6,9,10,11] (sourceLabel 9 0 0 v)
def fusedMap0256 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,11,9,10] (fusedLabel 9 0 0 v)
theorem sourceMap0256_checked : acceptsGraphIso
    (source (graph core0256) (root 9) 0 0) DegreeTwoThreeSpectrum521.graph sourceMap0256=true := by decide +kernel
theorem fusedMap0256_checked : acceptsGraphIso
    (fused (graph core0256) (root 9) 0 0) DegreeOneSmallSpectrum616.graph fusedMap0256=true := by decide +kernel
theorem certified0256 : Certified (graph core0256) (root 9) 0 0 :=
  of_native_maps core0256 DegreeTwoThreeSpectrum521.graph DegreeOneSmallSpectrum616.graph
    sourceMap0256 fusedMap0256 sourceMap0256_checked fusedMap0256_checked
    DegreeTwoThreeFiniteComparisons.comparison0256
#print axioms sourceMap0256_checked
#print axioms fusedMap0256_checked
#print axioms certified0256
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
