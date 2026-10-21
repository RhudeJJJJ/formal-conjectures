/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons17
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0850 : Family 8 := level8.get ⟨36,by decide⟩
def sourceMap0850 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,9,10,11,12] (sourceLabel 8 1 1 v)
def fusedMap0850 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (fusedLabel 8 1 1 v)
theorem sourceMap0850_checked : acceptsGraphIso
    (source (graph core0850) (root 8) 1 1) DegreeOneSmallSpectrum1053.graph sourceMap0850=true := by decide +kernel
theorem fusedMap0850_checked : acceptsGraphIso
    (fused (graph core0850) (root 8) 1 1) DegreeOneSmallSpectrum864.graph fusedMap0850=true := by decide +kernel
theorem certified0850 : Certified (graph core0850) (root 8) 1 1 :=
  of_native_maps core0850 DegreeOneSmallSpectrum1053.graph DegreeOneSmallSpectrum864.graph
    sourceMap0850 fusedMap0850 sourceMap0850_checked fusedMap0850_checked
    DegreeOneSmallComparisons.comparison0850
#print axioms sourceMap0850_checked
#print axioms fusedMap0850_checked
#print axioms certified0850
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
