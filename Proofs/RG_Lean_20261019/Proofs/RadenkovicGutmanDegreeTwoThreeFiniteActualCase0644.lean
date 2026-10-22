/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons12
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0644 : Family 10 := level10.get ⟨817,by decide⟩
def sourceMap0644 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,12,7,8,9,10,11] (sourceLabel 10 0 0 v)
def fusedMap0644 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,12,7,8,9,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap0644_checked : acceptsGraphIso
    (source (graph core0644) (root 10) 0 0) DegreeOneSmallSpectrum1449.graph sourceMap0644=true := by decide +kernel
theorem fusedMap0644_checked : acceptsGraphIso
    (fused (graph core0644) (root 10) 0 0) DegreeOneSmallSpectrum1446.graph fusedMap0644=true := by decide +kernel
theorem certified0644 : Certified (graph core0644) (root 10) 0 0 :=
  of_native_maps core0644 DegreeOneSmallSpectrum1449.graph DegreeOneSmallSpectrum1446.graph
    sourceMap0644 fusedMap0644 sourceMap0644_checked fusedMap0644_checked
    DegreeTwoThreeFiniteComparisons.comparison0644
#print axioms sourceMap0644_checked
#print axioms fusedMap0644_checked
#print axioms certified0644
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
