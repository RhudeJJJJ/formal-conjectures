/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons17
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0858 : Family 10 := level10.get ⟨1350,by decide⟩
def sourceMap0858 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,6,7,8,9,10,11,12,2,3,4,5] (sourceLabel 10 0 0 v)
def fusedMap0858 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,6,7,8,9,10,11,12,2,3,4,5] (fusedLabel 10 0 0 v)
theorem sourceMap0858_checked : acceptsGraphIso
    (source (graph core0858) (root 10) 0 0) DegreeOneSmallSpectrum1946.graph sourceMap0858=true := by decide +kernel
theorem fusedMap0858_checked : acceptsGraphIso
    (fused (graph core0858) (root 10) 0 0) DegreeOneSmallSpectrum1922.graph fusedMap0858=true := by decide +kernel
theorem certified0858 : Certified (graph core0858) (root 10) 0 0 :=
  of_native_maps core0858 DegreeOneSmallSpectrum1946.graph DegreeOneSmallSpectrum1922.graph
    sourceMap0858 fusedMap0858 sourceMap0858_checked fusedMap0858_checked
    DegreeTwoThreeFiniteComparisons.comparison0858
#print axioms sourceMap0858_checked
#print axioms fusedMap0858_checked
#print axioms certified0858
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
