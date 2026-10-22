/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons19
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0994 : Family 10 := level10.get ⟨1703,by decide⟩
def sourceMap0994 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (sourceLabel 10 0 0 v)
def fusedMap0994 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap0994_checked : acceptsGraphIso
    (source (graph core0994) (root 10) 0 0) DegreeTwoThreeSpectrum1594.graph sourceMap0994=true := by decide +kernel
theorem fusedMap0994_checked : acceptsGraphIso
    (fused (graph core0994) (root 10) 0 0) DegreeOneSmallSpectrum1891.graph fusedMap0994=true := by decide +kernel
theorem certified0994 : Certified (graph core0994) (root 10) 0 0 :=
  of_native_maps core0994 DegreeTwoThreeSpectrum1594.graph DegreeOneSmallSpectrum1891.graph
    sourceMap0994 fusedMap0994 sourceMap0994_checked fusedMap0994_checked
    DegreeTwoThreeFiniteComparisons.comparison0994
#print axioms sourceMap0994_checked
#print axioms fusedMap0994_checked
#print axioms certified0994
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
