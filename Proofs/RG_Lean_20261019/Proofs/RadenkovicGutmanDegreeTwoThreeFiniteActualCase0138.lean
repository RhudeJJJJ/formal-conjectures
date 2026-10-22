/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons02
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0138 : Family 8 := level8.get ⟨216,by decide⟩
def sourceMap0138 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9,10] (sourceLabel 8 0 0 v)
def fusedMap0138 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9,10] (fusedLabel 8 0 0 v)
theorem sourceMap0138_checked : acceptsGraphIso
    (source (graph core0138) (root 8) 0 0) DegreeOneSmallSpectrum289.graph sourceMap0138=true := by decide +kernel
theorem fusedMap0138_checked : acceptsGraphIso
    (fused (graph core0138) (root 8) 0 0) DegreeOneSmallSpectrum288.graph fusedMap0138=true := by decide +kernel
theorem certified0138 : Certified (graph core0138) (root 8) 0 0 :=
  of_native_maps core0138 DegreeOneSmallSpectrum289.graph DegreeOneSmallSpectrum288.graph
    sourceMap0138 fusedMap0138 sourceMap0138_checked fusedMap0138_checked
    DegreeTwoThreeFiniteComparisons.comparison0138
#print axioms sourceMap0138_checked
#print axioms fusedMap0138_checked
#print axioms certified0138
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
