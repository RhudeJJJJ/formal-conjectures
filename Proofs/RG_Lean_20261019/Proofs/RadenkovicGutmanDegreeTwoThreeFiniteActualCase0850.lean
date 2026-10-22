/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons17
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0850 : Family 10 := level10.get ⟨1332,by decide⟩
def sourceMap0850 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11,12] (sourceLabel 10 0 0 v)
def fusedMap0850 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap0850_checked : acceptsGraphIso
    (source (graph core0850) (root 10) 0 0) DegreeOneSmallSpectrum1378.graph sourceMap0850=true := by decide +kernel
theorem fusedMap0850_checked : acceptsGraphIso
    (fused (graph core0850) (root 10) 0 0) DegreeOneSmallSpectrum1377.graph fusedMap0850=true := by decide +kernel
theorem certified0850 : Certified (graph core0850) (root 10) 0 0 :=
  of_native_maps core0850 DegreeOneSmallSpectrum1378.graph DegreeOneSmallSpectrum1377.graph
    sourceMap0850 fusedMap0850 sourceMap0850_checked fusedMap0850_checked
    DegreeTwoThreeFiniteComparisons.comparison0850
#print axioms sourceMap0850_checked
#print axioms fusedMap0850_checked
#print axioms certified0850
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
