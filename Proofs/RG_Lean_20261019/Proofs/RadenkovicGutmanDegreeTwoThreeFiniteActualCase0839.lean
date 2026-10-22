/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons16
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0839 : Family 10 := level10.get ⟨1308,by decide⟩
def sourceMap0839 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,7,8,9,10,11,12,5,6,2,3,4] (sourceLabel 10 0 0 v)
def fusedMap0839 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,10,8,9] (fusedLabel 10 0 0 v)
theorem sourceMap0839_checked : acceptsGraphIso
    (source (graph core0839) (root 10) 0 0) DegreeTwoThreeSpectrum1389.graph sourceMap0839=true := by decide +kernel
theorem fusedMap0839_checked : acceptsGraphIso
    (fused (graph core0839) (root 10) 0 0) DegreeOneSmallSpectrum1940.graph fusedMap0839=true := by decide +kernel
theorem certified0839 : Certified (graph core0839) (root 10) 0 0 :=
  of_native_maps core0839 DegreeTwoThreeSpectrum1389.graph DegreeOneSmallSpectrum1940.graph
    sourceMap0839 fusedMap0839 sourceMap0839_checked fusedMap0839_checked
    DegreeTwoThreeFiniteComparisons.comparison0839
#print axioms sourceMap0839_checked
#print axioms fusedMap0839_checked
#print axioms certified0839
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
