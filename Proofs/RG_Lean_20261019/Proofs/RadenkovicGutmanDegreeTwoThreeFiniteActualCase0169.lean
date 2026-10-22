/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons03
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0169 : Family 9 := level9.get ⟨54,by decide⟩
def sourceMap0169 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,1,0,6,7,8,9,10,11,3,4,5] (sourceLabel 9 0 0 v)
def fusedMap0169 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![8,7,0,1,2,3,4,5,6,11,9,10] (fusedLabel 9 0 0 v)
theorem sourceMap0169_checked : acceptsGraphIso
    (source (graph core0169) (root 9) 0 0) DegreeOneSmallSpectrum418.graph sourceMap0169=true := by decide +kernel
theorem fusedMap0169_checked : acceptsGraphIso
    (fused (graph core0169) (root 9) 0 0) DegreeOneSmallSpectrum453.graph fusedMap0169=true := by decide +kernel
theorem certified0169 : Certified (graph core0169) (root 9) 0 0 :=
  of_native_maps core0169 DegreeOneSmallSpectrum418.graph DegreeOneSmallSpectrum453.graph
    sourceMap0169 fusedMap0169 sourceMap0169_checked fusedMap0169_checked
    DegreeTwoThreeFiniteComparisons.comparison0169
#print axioms sourceMap0169_checked
#print axioms fusedMap0169_checked
#print axioms certified0169
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
