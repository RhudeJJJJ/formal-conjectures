/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons14
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0726 : Family 10 := level10.get ⟨1026,by decide⟩
def sourceMap0726 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,12,8,9,10,11] (sourceLabel 10 0 0 v)
def fusedMap0726 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,12,8,9,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap0726_checked : acceptsGraphIso
    (source (graph core0726) (root 10) 0 0) DegreeTwoThreeSpectrum1346.graph sourceMap0726=true := by decide +kernel
theorem fusedMap0726_checked : acceptsGraphIso
    (fused (graph core0726) (root 10) 0 0) DegreeOneSmallSpectrum1594.graph fusedMap0726=true := by decide +kernel
theorem certified0726 : Certified (graph core0726) (root 10) 0 0 :=
  of_native_maps core0726 DegreeTwoThreeSpectrum1346.graph DegreeOneSmallSpectrum1594.graph
    sourceMap0726 fusedMap0726 sourceMap0726_checked fusedMap0726_checked
    DegreeTwoThreeFiniteComparisons.comparison0726
#print axioms sourceMap0726_checked
#print axioms fusedMap0726_checked
#print axioms certified0726
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
