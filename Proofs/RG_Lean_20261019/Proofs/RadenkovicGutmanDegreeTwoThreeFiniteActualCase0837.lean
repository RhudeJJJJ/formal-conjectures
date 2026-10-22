/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons16
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0837 : Family 10 := level10.get ⟨1302,by decide⟩
def sourceMap0837 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,6,7,8,9,10,11,12,5,2,3,4] (sourceLabel 10 0 0 v)
def fusedMap0837 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,11,9,10] (fusedLabel 10 0 0 v)
theorem sourceMap0837_checked : acceptsGraphIso
    (source (graph core0837) (root 10) 0 0) DegreeTwoThreeSpectrum1432.graph sourceMap0837=true := by decide +kernel
theorem fusedMap0837_checked : acceptsGraphIso
    (fused (graph core0837) (root 10) 0 0) DegreeOneSmallSpectrum1937.graph fusedMap0837=true := by decide +kernel
theorem certified0837 : Certified (graph core0837) (root 10) 0 0 :=
  of_native_maps core0837 DegreeTwoThreeSpectrum1432.graph DegreeOneSmallSpectrum1937.graph
    sourceMap0837 fusedMap0837 sourceMap0837_checked fusedMap0837_checked
    DegreeTwoThreeFiniteComparisons.comparison0837
#print axioms sourceMap0837_checked
#print axioms fusedMap0837_checked
#print axioms certified0837
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
