/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons16
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0821 : Family 10 := level10.get ⟨1263,by decide⟩
def sourceMap0821 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,12,8,9,10,11] (sourceLabel 10 0 0 v)
def fusedMap0821 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,12,8,9,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap0821_checked : acceptsGraphIso
    (source (graph core0821) (root 10) 0 0) DegreeTwoThreeSpectrum1611.graph sourceMap0821=true := by decide +kernel
theorem fusedMap0821_checked : acceptsGraphIso
    (fused (graph core0821) (root 10) 0 0) DegreeOneSmallSpectrum1908.graph fusedMap0821=true := by decide +kernel
theorem certified0821 : Certified (graph core0821) (root 10) 0 0 :=
  of_native_maps core0821 DegreeTwoThreeSpectrum1611.graph DegreeOneSmallSpectrum1908.graph
    sourceMap0821 fusedMap0821 sourceMap0821_checked fusedMap0821_checked
    DegreeTwoThreeFiniteComparisons.comparison0821
#print axioms sourceMap0821_checked
#print axioms fusedMap0821_checked
#print axioms certified0821
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
