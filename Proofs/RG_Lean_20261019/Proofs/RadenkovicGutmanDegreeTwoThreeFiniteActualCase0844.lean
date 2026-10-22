/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons16
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0844 : Family 10 := level10.get ⟨1319,by decide⟩
def sourceMap0844 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (sourceLabel 10 0 0 v)
def fusedMap0844 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,10,11,12,9,7,8] (fusedLabel 10 0 0 v)
theorem sourceMap0844_checked : acceptsGraphIso
    (source (graph core0844) (root 10) 0 0) DegreeOneSmallSpectrum1951.graph sourceMap0844=true := by decide +kernel
theorem fusedMap0844_checked : acceptsGraphIso
    (fused (graph core0844) (root 10) 0 0) DegreeOneSmallSpectrum1946.graph fusedMap0844=true := by decide +kernel
theorem certified0844 : Certified (graph core0844) (root 10) 0 0 :=
  of_native_maps core0844 DegreeOneSmallSpectrum1951.graph DegreeOneSmallSpectrum1946.graph
    sourceMap0844 fusedMap0844 sourceMap0844_checked fusedMap0844_checked
    DegreeTwoThreeFiniteComparisons.comparison0844
#print axioms sourceMap0844_checked
#print axioms fusedMap0844_checked
#print axioms certified0844
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
