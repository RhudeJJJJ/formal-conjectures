/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons17
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0874 : Family 8 := level8.get ⟨44,by decide⟩
def sourceMap0874 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,9,10,11,12] (sourceLabel 8 1 1 v)
def fusedMap0874 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (fusedLabel 8 1 1 v)
theorem sourceMap0874_checked : acceptsGraphIso
    (source (graph core0874) (root 8) 1 1) DegreeOneSmallSpectrum1204.graph sourceMap0874=true := by decide +kernel
theorem fusedMap0874_checked : acceptsGraphIso
    (fused (graph core0874) (root 8) 1 1) DegreeOneSmallSpectrum880.graph fusedMap0874=true := by decide +kernel
theorem certified0874 : Certified (graph core0874) (root 8) 1 1 :=
  of_native_maps core0874 DegreeOneSmallSpectrum1204.graph DegreeOneSmallSpectrum880.graph
    sourceMap0874 fusedMap0874 sourceMap0874_checked fusedMap0874_checked
    DegreeOneSmallComparisons.comparison0874
#print axioms sourceMap0874_checked
#print axioms fusedMap0874_checked
#print axioms certified0874
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
