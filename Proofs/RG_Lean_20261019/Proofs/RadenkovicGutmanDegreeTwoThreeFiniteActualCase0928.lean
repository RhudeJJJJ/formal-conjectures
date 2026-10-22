/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons18
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0928 : Family 10 := level10.get ⟨1529,by decide⟩
def sourceMap0928 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (sourceLabel 10 0 0 v)
def fusedMap0928 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap0928_checked : acceptsGraphIso
    (source (graph core0928) (root 10) 0 0) DegreeTwoThreeSpectrum1286.graph sourceMap0928=true := by decide +kernel
theorem fusedMap0928_checked : acceptsGraphIso
    (fused (graph core0928) (root 10) 0 0) DegreeOneSmallSpectrum1529.graph fusedMap0928=true := by decide +kernel
theorem certified0928 : Certified (graph core0928) (root 10) 0 0 :=
  of_native_maps core0928 DegreeTwoThreeSpectrum1286.graph DegreeOneSmallSpectrum1529.graph
    sourceMap0928 fusedMap0928 sourceMap0928_checked fusedMap0928_checked
    DegreeTwoThreeFiniteComparisons.comparison0928
#print axioms sourceMap0928_checked
#print axioms fusedMap0928_checked
#print axioms certified0928
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
