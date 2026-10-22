/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons15
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0777 : Family 10 := level10.get ⟨1159,by decide⟩
def sourceMap0777 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,8,9,10,11,12,5,6,7,2,3,4] (sourceLabel 10 0 0 v)
def fusedMap0777 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,10,11,12,9,7,8] (fusedLabel 10 0 0 v)
theorem sourceMap0777_checked : acceptsGraphIso
    (source (graph core0777) (root 10) 0 0) DegreeOneSmallSpectrum1642.graph sourceMap0777=true := by decide +kernel
theorem fusedMap0777_checked : acceptsGraphIso
    (fused (graph core0777) (root 10) 0 0) DegreeOneSmallSpectrum1832.graph fusedMap0777=true := by decide +kernel
theorem certified0777 : Certified (graph core0777) (root 10) 0 0 :=
  of_native_maps core0777 DegreeOneSmallSpectrum1642.graph DegreeOneSmallSpectrum1832.graph
    sourceMap0777 fusedMap0777 sourceMap0777_checked fusedMap0777_checked
    DegreeTwoThreeFiniteComparisons.comparison0777
#print axioms sourceMap0777_checked
#print axioms fusedMap0777_checked
#print axioms certified0777
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
