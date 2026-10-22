/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons16
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0815 : Family 10 := level10.get ⟨1247,by decide⟩
def sourceMap0815 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (sourceLabel 10 0 0 v)
def fusedMap0815 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap0815_checked : acceptsGraphIso
    (source (graph core0815) (root 10) 0 0) DegreeTwoThreeSpectrum1597.graph sourceMap0815=true := by decide +kernel
theorem fusedMap0815_checked : acceptsGraphIso
    (fused (graph core0815) (root 10) 0 0) DegreeOneSmallSpectrum1894.graph fusedMap0815=true := by decide +kernel
theorem certified0815 : Certified (graph core0815) (root 10) 0 0 :=
  of_native_maps core0815 DegreeTwoThreeSpectrum1597.graph DegreeOneSmallSpectrum1894.graph
    sourceMap0815 fusedMap0815 sourceMap0815_checked fusedMap0815_checked
    DegreeTwoThreeFiniteComparisons.comparison0815
#print axioms sourceMap0815_checked
#print axioms fusedMap0815_checked
#print axioms certified0815
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
