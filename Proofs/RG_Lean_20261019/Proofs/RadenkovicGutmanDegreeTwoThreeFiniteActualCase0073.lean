/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons01
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0073 : Family 8 := level8.get ⟨47,by decide⟩
def sourceMap0073 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![2,1,0,6,7,8,9,10,3,4,5] (sourceLabel 8 0 0 v)
def fusedMap0073 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![7,6,0,1,2,3,4,5,10,8,9] (fusedLabel 8 0 0 v)
theorem sourceMap0073_checked : acceptsGraphIso
    (source (graph core0073) (root 8) 0 0) DegreeOneSmallSpectrum262.graph sourceMap0073=true := by decide +kernel
theorem fusedMap0073_checked : acceptsGraphIso
    (fused (graph core0073) (root 8) 0 0) DegreeOneSmallSpectrum186.graph fusedMap0073=true := by decide +kernel
theorem certified0073 : Certified (graph core0073) (root 8) 0 0 :=
  of_native_maps core0073 DegreeOneSmallSpectrum262.graph DegreeOneSmallSpectrum186.graph
    sourceMap0073 fusedMap0073 sourceMap0073_checked fusedMap0073_checked
    DegreeTwoThreeFiniteComparisons.comparison0073
#print axioms sourceMap0073_checked
#print axioms fusedMap0073_checked
#print axioms certified0073
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
