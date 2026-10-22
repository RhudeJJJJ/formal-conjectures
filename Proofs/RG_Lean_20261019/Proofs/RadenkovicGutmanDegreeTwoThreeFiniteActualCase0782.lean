/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons15
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0782 : Family 10 := level10.get ⟨1167,by decide⟩
def sourceMap0782 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9,10,11,12] (sourceLabel 10 0 0 v)
def fusedMap0782 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9,10,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap0782_checked : acceptsGraphIso
    (source (graph core0782) (root 10) 0 0) DegreeOneSmallSpectrum1161.graph sourceMap0782=true := by decide +kernel
theorem fusedMap0782_checked : acceptsGraphIso
    (fused (graph core0782) (root 10) 0 0) DegreeOneSmallSpectrum1160.graph fusedMap0782=true := by decide +kernel
theorem certified0782 : Certified (graph core0782) (root 10) 0 0 :=
  of_native_maps core0782 DegreeOneSmallSpectrum1161.graph DegreeOneSmallSpectrum1160.graph
    sourceMap0782 fusedMap0782 sourceMap0782_checked fusedMap0782_checked
    DegreeTwoThreeFiniteComparisons.comparison0782
#print axioms sourceMap0782_checked
#print axioms fusedMap0782_checked
#print axioms certified0782
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
