/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons17
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0855 : Family 10 := level10.get ⟨1340,by decide⟩
def sourceMap0855 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,8,9,10,11,12,2,3,4,5,6,7] (sourceLabel 10 0 0 v)
def fusedMap0855 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,8,9,10,11,12,2,3,4,5,6,7] (fusedLabel 10 0 0 v)
theorem sourceMap0855_checked : acceptsGraphIso
    (source (graph core0855) (root 10) 0 0) DegreeTwoThreeSpectrum1414.graph sourceMap0855=true := by decide +kernel
theorem fusedMap0855_checked : acceptsGraphIso
    (fused (graph core0855) (root 10) 0 0) DegreeTwoThreeSpectrum1390.graph fusedMap0855=true := by decide +kernel
theorem certified0855 : Certified (graph core0855) (root 10) 0 0 :=
  of_native_maps core0855 DegreeTwoThreeSpectrum1414.graph DegreeTwoThreeSpectrum1390.graph
    sourceMap0855 fusedMap0855 sourceMap0855_checked fusedMap0855_checked
    DegreeTwoThreeFiniteComparisons.comparison0855
#print axioms sourceMap0855_checked
#print axioms fusedMap0855_checked
#print axioms certified0855
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
