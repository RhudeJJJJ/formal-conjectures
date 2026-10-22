/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons01
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0050 : Family 7 := level7.get ⟨74,by decide⟩
def sourceMap0050 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 1) → Fin 10 :=
  fun v => ![1,0,5,6,7,8,9,2,3,4] (sourceLabel 7 0 0 v)
def fusedMap0050 : (Vertices 7 ⊕ Fin 2) → Fin 10 :=
  fun v => ![6,0,1,2,3,4,5,9,7,8] (fusedLabel 7 0 0 v)
theorem sourceMap0050_checked : acceptsGraphIso
    (source (graph core0050) (root 7) 0 0) DegreeOneSmallSpectrum157.graph sourceMap0050=true := by decide +kernel
theorem fusedMap0050_checked : acceptsGraphIso
    (fused (graph core0050) (root 7) 0 0) DegreeOneSmallSpectrum114.graph fusedMap0050=true := by decide +kernel
theorem certified0050 : Certified (graph core0050) (root 7) 0 0 :=
  of_native_maps core0050 DegreeOneSmallSpectrum157.graph DegreeOneSmallSpectrum114.graph
    sourceMap0050 fusedMap0050 sourceMap0050_checked fusedMap0050_checked
    DegreeTwoThreeFiniteComparisons.comparison0050
#print axioms sourceMap0050_checked
#print axioms fusedMap0050_checked
#print axioms certified0050
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
