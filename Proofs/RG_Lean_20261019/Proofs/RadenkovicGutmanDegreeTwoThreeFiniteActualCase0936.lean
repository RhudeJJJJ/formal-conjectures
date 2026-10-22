/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons18
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0936 : Family 10 := level10.get ⟨1548,by decide⟩
def sourceMap0936 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (sourceLabel 10 0 0 v)
def fusedMap0936 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap0936_checked : acceptsGraphIso
    (source (graph core0936) (root 10) 0 0) DegreeTwoThreeSpectrum1317.graph sourceMap0936=true := by decide +kernel
theorem fusedMap0936_checked : acceptsGraphIso
    (fused (graph core0936) (root 10) 0 0) DegreeOneSmallSpectrum1566.graph fusedMap0936=true := by decide +kernel
theorem certified0936 : Certified (graph core0936) (root 10) 0 0 :=
  of_native_maps core0936 DegreeTwoThreeSpectrum1317.graph DegreeOneSmallSpectrum1566.graph
    sourceMap0936 fusedMap0936 sourceMap0936_checked fusedMap0936_checked
    DegreeTwoThreeFiniteComparisons.comparison0936
#print axioms sourceMap0936_checked
#print axioms fusedMap0936_checked
#print axioms certified0936
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
