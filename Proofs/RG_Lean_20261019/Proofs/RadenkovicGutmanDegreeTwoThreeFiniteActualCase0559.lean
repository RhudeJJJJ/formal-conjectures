/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons11
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0559 : Family 10 := level10.get ⟨575,by decide⟩
def sourceMap0559 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,9,10,11,12] (sourceLabel 10 0 0 v)
def fusedMap0559 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,9,10,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap0559_checked : acceptsGraphIso
    (source (graph core0559) (root 10) 0 0) DegreeOneSmallSpectrum1106.graph sourceMap0559=true := by decide +kernel
theorem fusedMap0559_checked : acceptsGraphIso
    (fused (graph core0559) (root 10) 0 0) DegreeOneSmallSpectrum1105.graph fusedMap0559=true := by decide +kernel
theorem certified0559 : Certified (graph core0559) (root 10) 0 0 :=
  of_native_maps core0559 DegreeOneSmallSpectrum1106.graph DegreeOneSmallSpectrum1105.graph
    sourceMap0559 fusedMap0559 sourceMap0559_checked fusedMap0559_checked
    DegreeTwoThreeFiniteComparisons.comparison0559
#print axioms sourceMap0559_checked
#print axioms fusedMap0559_checked
#print axioms certified0559
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
